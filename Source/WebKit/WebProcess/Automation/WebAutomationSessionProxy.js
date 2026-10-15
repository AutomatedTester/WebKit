/*
 * Copyright (C) 2016 Apple Inc. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY APPLE INC. AND ITS CONTRIBUTORS ``AS IS''
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL APPLE INC. OR ITS CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
 * THE POSSIBILITY OF SUCH DAMAGE.
 */

//# sourceURL=__InjectedScript_WebAutomationSessionProxy.js

(function (sessionIdentifier, currentFrameIdentifier, evaluate, createUUID, isValidNodeIdentifier, isKnownReference, addKnownReference, isProxy, shadowRootForElement, frameIdentifierForWindow) {

const sessionNodePropertyName = "session-node-" + sessionIdentifier;

// Brand checks used by WebDriver BiDi serialization. Unlike instanceof, these also recognize
// objects created in other realms. If the page has replaced the interface object, the check
// fails closed rather than breaking creation of this script.
function brandCheck(interfaceName, property)
{
    let getter;
    try {
        getter = Object.getOwnPropertyDescriptor(globalThis[interfaceName].prototype, property).get;
    } catch {
        return () => false;
    }

    return value => {
        try {
            getter.call(value);
            return true;
        } catch {
            return false;
        }
    };
}

const isArrayBuffer = brandCheck("ArrayBuffer", "byteLength");
const isMap = brandCheck("Map", "size");
const isSet = brandCheck("Set", "size");
const isRegExp = brandCheck("RegExp", "source");
const isAttr = brandCheck("Attr", "ownerElement");
const isElement = brandCheck("Element", "attributes");
const isHTMLCollection = brandCheck("HTMLCollection", "length");
const isNode = brandCheck("Node", "nodeType");
const isNodeList = brandCheck("NodeList", "length");
const isShadowRoot = brandCheck("ShadowRoot", "mode");

// %TypedArray%.prototype[@@toStringTag] returns undefined for anything but a typed array.
const isTypedArray = (() => {
    let toStringTagGetter = Object.getOwnPropertyDescriptor(Object.getPrototypeOf(Int8Array.prototype), Symbol.toStringTag).get;
    return value => toStringTagGetter.call(value) !== undefined;
})();

function isDate(value)
{
    try {
        Date.prototype.getTime.call(value);
        return true;
    } catch {
        return false;
    }
}

function isWeakMap(value)
{
    try {
        WeakMap.prototype.has.call(value, {});
        return true;
    } catch {
        return false;
    }
}

function isWeakSet(value)
{
    try {
        WeakSet.prototype.has.call(value, {});
        return true;
    } catch {
        return false;
    }
}

const objectToString = Object.prototype.toString;
const mapEntries = Map.prototype.entries;
const setValues = Set.prototype.values;
const dateToISOString = Date.prototype.toISOString;

let AutomationSessionProxy = class AutomationSessionProxy
{
    constructor()
    {
        this._nodeToIdMap = new Map;
        this._idToNodeMap = new Map;
        this._staleIdentifiers = new Set;
        this._bidiHandles = new Map;
    }

    // Public

    evaluateJavaScriptFunction(functionString, argumentStrings, expectsImplicitCallbackArgument, forceUserGesture, frameID, callbackID, resultCallback, callbackTimeout)
    {
        this._execute(functionString, argumentStrings, expectsImplicitCallbackArgument, callbackTimeout)
            .then(result => { resultCallback(frameID, callbackID, this._jsonStringify(result)); })
            .catch(error => { resultCallback(frameID, callbackID, error); });
    }

    evaluateBidiScript(expression, awaitPromise, maxDomDepth, maxObjectDepth, includeShadowTree, resultOwnership, frameID, callbackID, resultCallback, callbackTimeout)
    {
        let serializationOptions = { maxDomDepth, maxObjectDepth, includeShadowTree };
        this._executeBidiScript(expression, awaitPromise, serializationOptions, resultOwnership, callbackTimeout)
            .then(result => { resultCallback(frameID, callbackID, JSON.stringify(result)); })
            .catch(error => { resultCallback(frameID, callbackID, error); });
    }

    nodeForIdentifier(identifier)
    {
        this._clearStaleNodes();
        return this._nodeForIdentifier(identifier);
    }

    // Private

    _execute(functionString, argumentStrings, expectsImplicitCallbackArgument, callbackTimeout)
    {
        let timeoutPromise;
        let timeoutIdentifier = 0;
        if (callbackTimeout >= 0) {
            timeoutPromise = new Promise((resolve, reject) => {
                timeoutIdentifier = setTimeout(() => {
                    reject({ name: "JavaScriptTimeout", message: `script timed out after ${callbackTimeout}ms` });
                }, callbackTimeout);
            });
        }

        let promise = new Promise((resolve, reject) => {
            // Split initial line comments like "//# __injectedScript" source map that would break the async expression below.
            let lines = functionString.split("\n");
            let prefixLines = [];
            while (lines && lines[0].startsWith("//")) {
                prefixLines.push(lines.shift());
            }
            functionString = lines.join("\n");

            let prefix = prefixLines.join("\n")
            if (prefix)
                prefix += "\n";

            // The script is expected to be a function declaration. Evaluate it inside parenthesis to get the function value.
            let functionValue = evaluate(prefix + "(async " + functionString + ")");
            if (typeof functionValue !== "function")
                reject(new TypeError("Script did not evaluate to a function."));

            this._clearStaleNodes();

            let argumentValues = argumentStrings.map(this._jsonParse, this);
            if (expectsImplicitCallbackArgument)
                argumentValues.push(resolve);
            let resultPromise = functionValue.apply(null, argumentValues);

            let promises = [resultPromise];
            if (timeoutPromise)
                promises.push(timeoutPromise);
            Promise.race(promises)
                .then(result => {
                    if (!expectsImplicitCallbackArgument) {
                        resolve(result);
                    }
                })
                .catch(error => {
                    reject(error);
                });
        });

        // Async scripts can call Promise.resolve() in the function script, generating a new promise that is resolved in a
        // timer (see w3c test execute_async_script/promise.py::test_promise_resolve_timeout). In that case, the internal race
        // finishes resolved, so we need to start a new one here to wait for the second promise to be resolved or the timeout.
        let promises = [promise];
        if (timeoutPromise)
            promises.push(timeoutPromise);
        return Promise.race(promises)
            .finally(() => {
                if (timeoutIdentifier) {
                    clearTimeout(timeoutIdentifier);
                }
            });
    }

    _executeBidiScript(expression, awaitPromise, serializationOptions, resultOwnership, callbackTimeout)
    {
        let timeoutPromise;
        let timeoutIdentifier = 0;
        if (callbackTimeout >= 0) {
            timeoutPromise = new Promise((resolve, reject) => {
                timeoutIdentifier = setTimeout(() => {
                    reject({ name: "JavaScriptTimeout", message: `script timed out after ${callbackTimeout}ms` });
                }, callbackTimeout);
            });
        }

        let promise = new Promise((resolve, reject) => {
            // Errors thrown while serializing are internal errors, not exceptions thrown by the evaluated script.
            let resolveWithSuccess = value => {
                try {
                    resolve({ success: true, result: this._serializeBidiRemoteValue(value, serializationOptions, resultOwnership) });
                } catch (error) {
                    reject(error);
                }
            };
            let resolveWithException = exception => {
                try {
                    resolve(this._bidiExceptionEnvelope(exception, serializationOptions, resultOwnership));
                } catch (error) {
                    reject(error);
                }
            };

            let result;
            try {
                // Execute expression using globalThis.eval pattern (like original implementation).
                result = globalThis.eval(expression);
            } catch (exception) {
                resolveWithException(exception);
                return;
            }

            if (awaitPromise && result && typeof result.then === "function")
                result.then(resolveWithSuccess, resolveWithException);
            else
                resolveWithSuccess(result);
        });

        let promises = [promise];
        if (timeoutPromise)
            promises.push(timeoutPromise);
        return Promise.race(promises)
            .finally(() => {
                if (timeoutIdentifier) {
                    clearTimeout(timeoutIdentifier);
                }
            });
    }

    _bidiExceptionEnvelope(exception, serializationOptions, resultOwnership)
    {
        let text;
        try {
            text = String(exception);
        } catch {
            text = "Uncaught exception";
        }

        return {
            success: false,
            text,
            exception: this._serializeBidiRemoteValue(exception, serializationOptions, resultOwnership),
        };
    }

    _jsonParse(string)
    {
        if (!string)
            return undefined;
        return JSON.parse(string, (key, value) => this._reviveJSONValue(key, value));
    }

    _jsonStringify(value)
    {
        return JSON.stringify(this._jsonClone(value));
    }

    _reviveJSONValue(key, value)
    {
        if (value && typeof value === "object" && value[sessionNodePropertyName])
            return this._nodeForIdentifier(value[sessionNodePropertyName]);
        return value;
    }

    _isCollection(value) {
        switch (Object.prototype.toString.call(value)) {
        case "[object Arguments]":
        case "[object Array]":
        case "[object FileList]":
        case "[object HTMLAllCollection]":
        case "[object HTMLCollection]":
        case "[object HTMLFormControlsCollection]":
        case "[object HTMLOptionsCollection]":
        case "[object NodeList]":
            return true;
        }
        return false;
    }

    _checkCyclic(value, stack = [])
    {
        function isCyclic(value, proxy, stack = []) {
            if (value === undefined || value === null)
                return false;

            if (typeof value === "boolean" || typeof value === "number" || typeof value === "string")
                return false;

            if (value instanceof Node)
                return false;

            if (stack.includes(value))
                return true;

            if (proxy._isCollection(value)) {
                stack.push(value);
                for (let i = 0; i < value.length; i++) {
                    if (isCyclic(value[i], proxy, stack))
                        return true;
                }

                stack.pop();
                return false;
            }

            stack.push(value);
            for (let property in value) {
                if (isCyclic(value[property], proxy, stack))
                    return true;
            }

            stack.pop();
            return false;
        }

        if (isCyclic(value, this))
            throw new TypeError("cannot serialize cyclic structures.");
    }

    _jsonClone(value)
    {
        // Internal JSON clone algorithm.
        // https://w3c.github.io/webdriver/#dfn-internal-json-clone-algorithm
        if (value === undefined || value === null)
            return null;

        if (typeof value === "boolean" || typeof value === "number" || typeof value === "string")
            return value;

        if (this._isCollection(value)) {
            this._checkCyclic(value);
            return [...value].map(item => this._jsonClone(item));
        }

        if (value instanceof Node)
            return this._createNodeHandle(value);

        // FIXME: implement window proxy serialization.

        if (typeof value.toJSON === "function")
            return value.toJSON();

        let customObject = {};
        for (let property in value) {
            this._checkCyclic(value);
            customObject[property] = this._jsonClone(value[property]);
        }
        return customObject;
    }

    _createNodeHandle(node)
    {
        if (node.ownerDocument !== window.document || !node.isConnected) {
            // https://w3c.github.io/webdriver/#dfn-internal-json-clone
            if (node instanceof Element)
                throw {name: "StaleNode", message: "Stale element found when trying to create the node handle"};
            throw {name: "NodeNotFound", message: "Stale node found when trying to create the node handle"};
        }

        return {[sessionNodePropertyName]: this._identifierForNode(node)};
    }

    _nodeForIdentifier(identifier)
    {
        if (!isValidNodeIdentifier(identifier))
            throw {name: "InvalidNodeIdentifier", message: "Node identifier '" + identifier + "' is invalid"};

        let node = this._idToNodeMap.get(identifier);
        if (node)
            return node;

        // A node this frame knew about and then evicted is stale. One it never knew about
        // belongs to a different browsing context, which callers must distinguish.
        if (this._staleIdentifiers.has(identifier) || isKnownReference(currentFrameIdentifier, identifier))
            throw {name: "StaleNode", message: "Node with identifier '" + identifier + "' is stale"};
        throw {name: "NodeNotFound", message: "Node with identifier '" + identifier + "' was not found"};
    }

    _identifierForNode(node)
    {
        let identifier = this._nodeToIdMap.get(node);
        if (identifier)
            return identifier;

        identifier = "node-" + createUUID();

        this._nodeToIdMap.set(node, identifier);
        this._idToNodeMap.set(identifier, node);
        addKnownReference(currentFrameIdentifier, identifier);

        return identifier;
    }

    _clearStaleNodes()
    {
        for (var [node, identifier] of this._nodeToIdMap) {
            const rootNode = node.getRootNode({ composed: true });
            if (rootNode !== document) {
                this._nodeToIdMap.delete(node);
                this._idToNodeMap.delete(identifier);
                this._staleIdentifiers.add(identifier);
            }
        }
    }

    // WebDriver BiDi serialization.
    // https://w3c.github.io/webdriver-bidi/#serialize-as-a-remote-value

    _serializeBidiRemoteValue(value, serializationOptions, ownershipType)
    {
        return this._serializeAsRemoteValue(value, serializationOptions, ownershipType, new Map);
    }

    _serializeAsRemoteValue(value, serializationOptions, ownershipType, serializationInternalMap)
    {
        switch (typeof value) {
        case "undefined":
            return { type: "undefined" };
        case "string":
            return { type: "string", value };
        case "boolean":
            return { type: "boolean", value };
        case "bigint":
            return { type: "bigint", value: value.toString() };
        case "number":
            return { type: "number", value: this._serializeNumber(value) };
        }

        if (value === null)
            return { type: "null" };

        let handle = this._handleForObject(value, ownershipType);

        // A value seen earlier in this serialization is emitted as a reference to the first occurrence.
        // This is also what terminates cycles.
        let previouslySerialized = serializationInternalMap.get(value);
        if (previouslySerialized) {
            if (!previouslySerialized.internalId)
                previouslySerialized.internalId = createUUID().toLowerCase();

            let remoteValue = { type: previouslySerialized.type, internalId: previouslySerialized.internalId };
            if (handle)
                remoteValue.handle = handle;
            return remoteValue;
        }

        let windowFrameIdentifier = frameIdentifierForWindow(value);
        let type = this._remoteValueType(value, windowFrameIdentifier);
        let remoteValue = { type };
        if (handle)
            remoteValue.handle = handle;

        switch (type) {
        case "array":
        case "set":
        case "nodelist":
        case "htmlcollection":
            serializationInternalMap.set(value, remoteValue);
            if (serializationOptions.maxObjectDepth !== 0) {
                let childOptions = this._serializationOptionsForChildValue(serializationOptions);
                remoteValue.value = this._listItems(value, type).map(item => this._serializeAsRemoteValue(item, childOptions, "none", serializationInternalMap));
            }
            break;

        case "map":
        case "object":
            serializationInternalMap.set(value, remoteValue);
            if (serializationOptions.maxObjectDepth !== 0) {
                let childOptions = this._serializationOptionsForChildValue(serializationOptions);
                let entries = type === "map" ? Array.from(mapEntries.call(value)) : Object.entries(value);
                remoteValue.value = entries.map(([key, item]) => {
                    let serializedKey = typeof key === "string" ? key : this._serializeAsRemoteValue(key, childOptions, "none", serializationInternalMap);
                    return [serializedKey, this._serializeAsRemoteValue(item, childOptions, "none", serializationInternalMap)];
                });
            }
            break;

        case "regexp":
            remoteValue.value = { pattern: String(value.source), flags: String(value.flags) };
            break;

        case "date":
            try {
                remoteValue.value = dateToISOString.call(value);
            } catch {
                // toISOString() throws for invalid dates.
                remoteValue.value = "Invalid Date";
            }
            break;

        case "node":
            serializationInternalMap.set(value, remoteValue);
            remoteValue.sharedId = this._identifierForNode(value);
            remoteValue.value = this._serializeNode(value, serializationOptions, serializationInternalMap);
            break;

        case "window":
            // The UI process replaces the frame identifier with the browsing context id.
            if (windowFrameIdentifier)
                remoteValue.value = { context: windowFrameIdentifier };
            break;
        }

        return remoteValue;
    }

    _serializeNumber(value)
    {
        if (Number.isNaN(value))
            return "NaN";
        if (Object.is(value, -0))
            return "-0";
        if (value === Infinity)
            return "Infinity";
        if (value === -Infinity)
            return "-Infinity";
        return value;
    }

    _remoteValueType(value, windowFrameIdentifier)
    {
        if (typeof value === "symbol")
            return "symbol";

        // Check for proxies and windows first so that no trap or cross-origin access check runs below.
        if (isProxy(value))
            return "proxy";
        if (windowFrameIdentifier !== null)
            return "window";

        if (Array.isArray(value))
            return "array";
        if (isRegExp(value))
            return "regexp";
        if (isDate(value))
            return "date";
        if (isMap(value))
            return "map";
        if (isSet(value))
            return "set";
        if (isWeakMap(value))
            return "weakmap";
        if (isWeakSet(value))
            return "weakset";

        switch (objectToString.call(value)) {
        case "[object Generator]":
        case "[object AsyncGenerator]":
            return "generator";
        case "[object Error]":
            return "error";
        case "[object Promise]":
            return "promise";
        }

        if (isTypedArray(value))
            return "typedarray";
        if (isArrayBuffer(value))
            return "arraybuffer";
        if (isNodeList(value))
            return "nodelist";
        if (isHTMLCollection(value))
            return "htmlcollection";
        if (isNode(value))
            return "node";
        if (typeof value === "function")
            return "function";
        return "object";
    }

    _listItems(value, type)
    {
        if (type === "set")
            return Array.from(setValues.call(value));

        // Index rather than iterate, so that sparse arrays serialize holes as undefined.
        let items = [];
        for (let i = 0; i < value.length; ++i)
            items.push(value[i]);
        return items;
    }

    _serializationOptionsForChildValue(serializationOptions)
    {
        if (serializationOptions.maxObjectDepth === null)
            return serializationOptions;
        return { ...serializationOptions, maxObjectDepth: serializationOptions.maxObjectDepth - 1 };
    }

    _serializeNode(node, serializationOptions, serializationInternalMap)
    {
        let serialized = {
            nodeType: node.nodeType,
            childNodeCount: node.childNodes.length,
        };

        let nodeValue = node.nodeValue;
        if (nodeValue !== null)
            serialized.nodeValue = nodeValue;

        let nodeIsElement = isElement(node);
        if (nodeIsElement || isAttr(node)) {
            serialized.localName = node.localName;
            serialized.namespaceURI = node.namespaceURI;
        }

        let includeChildren = serializationOptions.maxDomDepth !== 0;
        if (isShadowRoot(node)) {
            serialized.mode = node.mode;
            let includeShadowTree = serializationOptions.includeShadowTree;
            if (includeShadowTree === "none" || (includeShadowTree === "open" && node.mode !== "open"))
                includeChildren = false;
        }

        if (includeChildren) {
            let childOptions = serializationOptions;
            if (serializationOptions.maxDomDepth !== null)
                childOptions = { ...serializationOptions, maxDomDepth: serializationOptions.maxDomDepth - 1 };
            serialized.children = Array.from(node.childNodes, child => this._serializeAsRemoteValue(child, childOptions, "none", serializationInternalMap));
        }

        if (nodeIsElement) {
            let attributes = Object.create(null);
            for (let attribute of node.attributes)
                attributes[attribute.name] = attribute.value;
            serialized.attributes = attributes;

            // The native helper also returns closed shadow roots, which page script cannot reach.
            let shadowRoot = shadowRootForElement(node);
            serialized.shadowRoot = shadowRoot ? this._serializeAsRemoteValue(shadowRoot, serializationOptions, "none", serializationInternalMap) : null;
        }

        return serialized;
    }

    _handleForObject(value, ownershipType)
    {
        if (ownershipType !== "root")
            return null;

        // FIXME: Release handles in script.disown <https://webkit.org/b/288059>.
        let handle = createUUID().toLowerCase();
        this._bidiHandles.set(handle, value);
        return handle;
    }
};

return new AutomationSessionProxy;

})
