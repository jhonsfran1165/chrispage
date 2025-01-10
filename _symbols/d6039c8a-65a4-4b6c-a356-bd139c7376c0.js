// New Block - Updated January 10, 2025
function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function create_slot(definition, ctx, $$scope, fn) {
    if (definition) {
        const slot_ctx = get_slot_context(definition, ctx, $$scope, fn);
        return definition[0](slot_ctx);
    }
}
function get_slot_context(definition, ctx, $$scope, fn) {
    return definition[1] && fn
        ? assign($$scope.ctx.slice(), definition[1](fn(ctx)))
        : $$scope.ctx;
}
function get_slot_changes(definition, $$scope, dirty, fn) {
    if (definition[2] && fn) {
        const lets = definition[2](fn(dirty));
        if ($$scope.dirty === undefined) {
            return lets;
        }
        if (typeof lets === 'object') {
            const merged = [];
            const len = Math.max($$scope.dirty.length, lets.length);
            for (let i = 0; i < len; i += 1) {
                merged[i] = $$scope.dirty[i] | lets[i];
            }
            return merged;
        }
        return $$scope.dirty | lets;
    }
    return $$scope.dirty;
}
function update_slot_base(slot, slot_definition, ctx, $$scope, slot_changes, get_slot_context_fn) {
    if (slot_changes) {
        const slot_context = get_slot_context(slot_definition, ctx, $$scope, get_slot_context_fn);
        slot.p(slot_context, slot_changes);
    }
}
function get_all_dirty_from_scope($$scope) {
    if ($$scope.ctx.length > 32) {
        const dirty = [];
        const length = $$scope.ctx.length / 32;
        for (let i = 0; i < length; i++) {
            dirty[i] = -1;
        }
        return dirty;
    }
    return -1;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}
function compute_rest_props(props, keys) {
    const rest = {};
    keys = new Set(keys);
    for (const k in props)
        if (!keys.has(k) && k[0] !== '$')
            rest[k] = props[k];
    return rest;
}
function compute_slots(slots) {
    const result = {};
    for (const key in slots) {
        result[key] = true;
    }
    return result;
}
function action_destroyer(action_result) {
    return action_result && is_function(action_result.destroy) ? action_result.destroy : noop;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function set_custom_element_data_map(node, data_map) {
    Object.keys(data_map).forEach((key) => {
        set_custom_element_data(node, key, data_map[key]);
    });
}
function set_custom_element_data(node, prop, value) {
    if (prop in node) {
        node[prop] = typeof node[prop] === 'boolean' && value === '' ? true : value;
    }
    else {
        attr(node, prop, value);
    }
}
function set_dynamic_element_data(tag) {
    return (/-/.test(tag)) ? set_custom_element_data_map : set_attributes;
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash$2(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash$2(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher$1() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}
/**
 * Associates an arbitrary `context` object with the current component and the specified `key`
 * and returns that object. The context is then available to children of the component
 * (including slotted content) with `getContext`.
 *
 * Like lifecycle functions, this must be called during component initialisation.
 *
 * https://svelte.dev/docs#run-time-svelte-setcontext
 */
function setContext(key, context) {
    get_current_component().$$.context.set(key, context);
    return context;
}
/**
 * Retrieves the context that belongs to the closest parent component with the specified `key`.
 * Must be called during component initialisation.
 *
 * https://svelte.dev/docs#run-time-svelte-getcontext
 */
function getContext(key) {
    return get_current_component().$$.context.get(key);
}
// TODO figure out if we still want to support
// shorthand events, or if we want to implement
// a real bubbling mechanism
function bubble(component, event) {
    const callbacks = component.$$.callbacks[event.type];
    if (callbacks) {
        // @ts-ignore
        callbacks.slice().forEach(fn => fn.call(this, event));
    }
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
function add_flush_callback(fn) {
    flush_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function get_spread_object(spread_props) {
    return typeof spread_props === 'object' && spread_props !== null ? spread_props : {};
}

function bind(component, name, callback) {
    const index = component.$$.props[name];
    if (index !== undefined) {
        component.$$.bound[index] = callback;
        callback(component.$$.ctx[index]);
    }
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

const exports = {}; const module = { exports };

/*!
	Copyright (c) 2018 Jed Watson.
	Licensed under the MIT License (MIT), see
	http://jedwatson.github.io/classnames
*/
/* global define */

(function () {

	var hasOwn = {}.hasOwnProperty;

	function classNames () {
		var classes = '';

		for (var i = 0; i < arguments.length; i++) {
			var arg = arguments[i];
			if (arg) {
				classes = appendClass(classes, parseValue(arg));
			}
		}

		return classes;
	}

	function parseValue (arg) {
		if (typeof arg === 'string' || typeof arg === 'number') {
			return arg;
		}

		if (typeof arg !== 'object') {
			return '';
		}

		if (Array.isArray(arg)) {
			return classNames.apply(null, arg);
		}

		if (arg.toString !== Object.prototype.toString && !arg.toString.toString().includes('[native code]')) {
			return arg.toString();
		}

		var classes = '';

		for (var key in arg) {
			if (hasOwn.call(arg, key) && arg[key]) {
				classes = appendClass(classes, key);
			}
		}

		return classes;
	}

	function appendClass (value, newClass) {
		if (!newClass) {
			return value;
		}
	
		if (value) {
			return value + ' ' + newClass;
		}
	
		return value + newClass;
	}

	if (typeof module !== 'undefined' && module.exports) {
		classNames.default = classNames;
		module.exports = classNames;
	} else if (typeof define === 'function' && typeof define.amd === 'object' && define.amd) {
		// register as 'classnames', consistent with npm package name
		define('classnames', [], function () {
			return classNames;
		});
	} else {
		window.classNames = classNames;
	}
}());




var classNames = module.exports;

/* generated by Svelte v3.59.1 */

function create_else_block$3(ctx) {
	let previous_tag = /*tag*/ ctx[1];
	let svelte_element_anchor;
	let current;
	let svelte_element = /*tag*/ ctx[1] && create_dynamic_element_1(ctx);

	return {
		c() {
			if (svelte_element) svelte_element.c();
			svelte_element_anchor = empty();
		},
		l(nodes) {
			if (svelte_element) svelte_element.l(nodes);
			svelte_element_anchor = empty();
		},
		m(target, anchor) {
			if (svelte_element) svelte_element.m(target, anchor);
			insert_hydration(target, svelte_element_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			if (/*tag*/ ctx[1]) {
				if (!previous_tag) {
					svelte_element = create_dynamic_element_1(ctx);
					previous_tag = /*tag*/ ctx[1];
					svelte_element.c();
					svelte_element.m(svelte_element_anchor.parentNode, svelte_element_anchor);
				} else if (safe_not_equal(previous_tag, /*tag*/ ctx[1])) {
					svelte_element.d(1);
					svelte_element = create_dynamic_element_1(ctx);
					previous_tag = /*tag*/ ctx[1];
					svelte_element.c();
					svelte_element.m(svelte_element_anchor.parentNode, svelte_element_anchor);
				} else {
					svelte_element.p(ctx, dirty);
				}
			} else if (previous_tag) {
				svelte_element.d(1);
				svelte_element = null;
				previous_tag = /*tag*/ ctx[1];
			}
		},
		i(local) {
			if (current) return;
			transition_in(svelte_element);
			current = true;
		},
		o(local) {
			transition_out(svelte_element);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(svelte_element_anchor);
			if (svelte_element) svelte_element.d(detaching);
		}
	};
}

// (81:0) {#if transition}
function create_if_block$6(ctx) {
	let previous_tag = /*tag*/ ctx[1];
	let svelte_element_anchor;
	let tag_will_be_removed = false;
	let current;
	let svelte_element = /*tag*/ ctx[1] && create_dynamic_element$3(ctx);

	return {
		c() {
			if (svelte_element) svelte_element.c();
			svelte_element_anchor = empty();
		},
		l(nodes) {
			if (svelte_element) svelte_element.l(nodes);
			svelte_element_anchor = empty();
		},
		m(target, anchor) {
			if (svelte_element) svelte_element.m(target, anchor);
			insert_hydration(target, svelte_element_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			if (/*tag*/ ctx[1]) {
				if (!previous_tag) {
					svelte_element = create_dynamic_element$3(ctx);
					previous_tag = /*tag*/ ctx[1];
					svelte_element.c();
					transition_in(svelte_element);
					svelte_element.m(svelte_element_anchor.parentNode, svelte_element_anchor);
				} else if (safe_not_equal(previous_tag, /*tag*/ ctx[1])) {
					svelte_element.d(1);
					svelte_element = create_dynamic_element$3(ctx);
					previous_tag = /*tag*/ ctx[1];
					svelte_element.c();

					if (tag_will_be_removed) {
						tag_will_be_removed = false;
						transition_in(svelte_element);
					}

					svelte_element.m(svelte_element_anchor.parentNode, svelte_element_anchor);
				} else {
					if (tag_will_be_removed) {
						tag_will_be_removed = false;
						transition_in(svelte_element);
					}

					svelte_element.p(ctx, dirty);
				}
			} else if (previous_tag) {
				tag_will_be_removed = true;
				group_outros();

				transition_out(svelte_element, 1, 1, () => {
					svelte_element = null;
					previous_tag = /*tag*/ ctx[1];
					tag_will_be_removed = false;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(svelte_element);
			current = true;
		},
		o(local) {
			transition_out(svelte_element);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(svelte_element_anchor);
			if (svelte_element) svelte_element.d(detaching);
		}
	};
}

// (96:2) <svelte:element     this={tag}     use:use={options}     bind:this={node}     {...$$restProps}     class={divClass}     on:mouseenter     on:mouseleave     on:focusin     on:focusout>
function create_dynamic_element_1(ctx) {
	let svelte_element;
	let use_action;
	let current;
	let mounted;
	let dispose;
	const default_slot_template = /*#slots*/ ctx[13].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[12], null);
	let svelte_element_levels = [/*$$restProps*/ ctx[7], { class: /*divClass*/ ctx[6] }];
	let svelte_element_data = {};

	for (let i = 0; i < svelte_element_levels.length; i += 1) {
		svelte_element_data = assign(svelte_element_data, svelte_element_levels[i]);
	}

	return {
		c() {
			svelte_element = element(/*tag*/ ctx[1]);
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			svelte_element = claim_element(nodes, (/*tag*/ ctx[1] || 'null').toUpperCase(), { class: true });
			var svelte_element_nodes = children(svelte_element);
			if (default_slot) default_slot.l(svelte_element_nodes);
			svelte_element_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_dynamic_element_data(/*tag*/ ctx[1])(svelte_element, svelte_element_data);
		},
		m(target, anchor) {
			insert_hydration(target, svelte_element, anchor);

			if (default_slot) {
				default_slot.m(svelte_element, null);
			}

			/*svelte_element_binding_1*/ ctx[23](svelte_element);
			current = true;

			if (!mounted) {
				dispose = [
					action_destroyer(use_action = /*use*/ ctx[4].call(null, svelte_element, /*options*/ ctx[5])),
					listen(svelte_element, "mouseenter", /*mouseenter_handler_1*/ ctx[18]),
					listen(svelte_element, "mouseleave", /*mouseleave_handler_1*/ ctx[19]),
					listen(svelte_element, "focusin", /*focusin_handler_1*/ ctx[20]),
					listen(svelte_element, "focusout", /*focusout_handler_1*/ ctx[21])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 4096)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[12],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[12])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[12], dirty, null),
						null
					);
				}
			}

			set_dynamic_element_data(/*tag*/ ctx[1])(svelte_element, svelte_element_data = get_spread_update(svelte_element_levels, [
				dirty & /*$$restProps*/ 128 && /*$$restProps*/ ctx[7],
				(!current || dirty & /*divClass*/ 64) && { class: /*divClass*/ ctx[6] }
			]));

			if (use_action && is_function(use_action.update) && dirty & /*options*/ 32) use_action.update.call(null, /*options*/ ctx[5]);
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(svelte_element);
			if (default_slot) default_slot.d(detaching);
			/*svelte_element_binding_1*/ ctx[23](null);
			mounted = false;
			run_all(dispose);
		}
	};
}

// (82:2) <svelte:element     this={tag}     use:use={options}     bind:this={node}     transition:transition={params}     {...$$restProps}     class={divClass}     on:mouseenter     on:mouseleave     on:focusin     on:focusout>
function create_dynamic_element$3(ctx) {
	let svelte_element;
	let use_action;
	let svelte_element_transition;
	let current;
	let mounted;
	let dispose;
	const default_slot_template = /*#slots*/ ctx[13].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[12], null);
	let svelte_element_levels = [/*$$restProps*/ ctx[7], { class: /*divClass*/ ctx[6] }];
	let svelte_element_data = {};

	for (let i = 0; i < svelte_element_levels.length; i += 1) {
		svelte_element_data = assign(svelte_element_data, svelte_element_levels[i]);
	}

	return {
		c() {
			svelte_element = element(/*tag*/ ctx[1]);
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			svelte_element = claim_element(nodes, (/*tag*/ ctx[1] || 'null').toUpperCase(), { class: true });
			var svelte_element_nodes = children(svelte_element);
			if (default_slot) default_slot.l(svelte_element_nodes);
			svelte_element_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_dynamic_element_data(/*tag*/ ctx[1])(svelte_element, svelte_element_data);
		},
		m(target, anchor) {
			insert_hydration(target, svelte_element, anchor);

			if (default_slot) {
				default_slot.m(svelte_element, null);
			}

			/*svelte_element_binding*/ ctx[22](svelte_element);
			current = true;

			if (!mounted) {
				dispose = [
					action_destroyer(use_action = /*use*/ ctx[4].call(null, svelte_element, /*options*/ ctx[5])),
					listen(svelte_element, "mouseenter", /*mouseenter_handler*/ ctx[14]),
					listen(svelte_element, "mouseleave", /*mouseleave_handler*/ ctx[15]),
					listen(svelte_element, "focusin", /*focusin_handler*/ ctx[16]),
					listen(svelte_element, "focusout", /*focusout_handler*/ ctx[17])
				];

				mounted = true;
			}
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;

			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 4096)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[12],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[12])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[12], dirty, null),
						null
					);
				}
			}

			set_dynamic_element_data(/*tag*/ ctx[1])(svelte_element, svelte_element_data = get_spread_update(svelte_element_levels, [
				dirty & /*$$restProps*/ 128 && /*$$restProps*/ ctx[7],
				(!current || dirty & /*divClass*/ 64) && { class: /*divClass*/ ctx[6] }
			]));

			if (use_action && is_function(use_action.update) && dirty & /*options*/ 32) use_action.update.call(null, /*options*/ ctx[5]);
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);

			add_render_callback(() => {
				if (!current) return;
				if (!svelte_element_transition) svelte_element_transition = create_bidirectional_transition(svelte_element, /*transition*/ ctx[2], /*params*/ ctx[3], true);
				svelte_element_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			if (!svelte_element_transition) svelte_element_transition = create_bidirectional_transition(svelte_element, /*transition*/ ctx[2], /*params*/ ctx[3], false);
			svelte_element_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(svelte_element);
			if (default_slot) default_slot.d(detaching);
			/*svelte_element_binding*/ ctx[22](null);
			if (detaching && svelte_element_transition) svelte_element_transition.end();
			mounted = false;
			run_all(dispose);
		}
	};
}

function create_fragment$e(ctx) {
	let current_block_type_index;
	let if_block;
	let if_block_anchor;
	let current;
	const if_block_creators = [create_if_block$6, create_else_block$3];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*transition*/ ctx[2]) return 0;
		return 1;
	}

	current_block_type_index = select_block_type(ctx);
	if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_blocks[current_block_type_index].m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if_blocks[current_block_type_index].p(ctx, dirty);
			} else {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block = if_blocks[current_block_type_index];

				if (!if_block) {
					if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block.c();
				} else {
					if_block.p(ctx, dirty);
				}

				transition_in(if_block, 1);
				if_block.m(if_block_anchor.parentNode, if_block_anchor);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if_blocks[current_block_type_index].d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$e($$self, $$props, $$invalidate) {
	const omit_props_names = [
		"tag","color","rounded","border","shadow","transition","params","node","use","options"
	];

	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	setContext('background', true);
	let { tag = 'div' } = $$props;
	let { color = 'default' } = $$props;
	let { rounded = false } = $$props;
	let { border = false } = $$props;
	let { shadow = false } = $$props;
	let { transition = undefined } = $$props;
	let { params = {} } = $$props;
	let { node = undefined } = $$props;
	let { use = noop } = $$props;
	let { options = {} } = $$props;

	// your script goes here
	const bgColors = {
		gray: 'bg-gray-50 dark:bg-gray-800',
		red: 'bg-red-50 dark:bg-gray-800',
		yellow: 'bg-yellow-50 dark:bg-gray-800 ',
		green: 'bg-green-50 dark:bg-gray-800 ',
		indigo: 'bg-indigo-50 dark:bg-gray-800 ',
		purple: 'bg-purple-50 dark:bg-gray-800 ',
		pink: 'bg-pink-50 dark:bg-gray-800 ',
		blue: 'bg-blue-50 dark:bg-gray-800 ',
		light: 'bg-gray-50 dark:bg-gray-700',
		dark: 'bg-gray-50 dark:bg-gray-800',
		default: 'bg-white dark:bg-gray-800',
		dropdown: 'bg-white dark:bg-gray-700',
		navbar: 'bg-white dark:bg-gray-900',
		navbarUl: 'bg-gray-50 dark:bg-gray-800',
		form: 'bg-gray-50 dark:bg-gray-700',
		primary: 'bg-primary-50 dark:bg-gray-800 ',
		none: ''
	};

	const textColors = {
		gray: 'text-gray-800 dark:text-gray-300',
		red: 'text-red-800 dark:text-red-400',
		yellow: 'text-yellow-800 dark:text-yellow-300',
		green: 'text-green-800 dark:text-green-400',
		indigo: 'text-indigo-800 dark:text-indigo-400',
		purple: 'text-purple-800 dark:text-purple-400',
		pink: 'text-pink-800 dark:text-pink-400',
		blue: 'text-blue-800 dark:text-blue-400',
		light: 'text-gray-700 dark:text-gray-300',
		dark: 'text-gray-700 dark:text-gray-300',
		default: 'text-gray-500 dark:text-gray-400',
		dropdown: 'text-gray-700 dark:text-gray-200',
		navbar: 'text-gray-700 dark:text-gray-200',
		navbarUl: 'text-gray-700 dark:text-gray-400',
		form: 'text-gray-900 dark:text-white',
		primary: 'text-primary-800 dark:text-primary-400',
		none: ''
	};

	const borderColors = {
		gray: 'border-gray-300 dark:border-gray-800',
		red: 'border-red-300 dark:border-red-800',
		yellow: 'border-yellow-300 dark:border-yellow-800',
		green: 'border-green-300 dark:border-green-800',
		indigo: 'border-indigo-300 dark:border-indigo-800',
		purple: 'border-purple-300 dark:border-purple-800',
		pink: 'border-pink-300 dark:border-pink-800',
		blue: 'border-blue-300 dark:border-blue-800',
		light: 'border-gray-500',
		dark: 'border-gray-500',
		default: 'border-gray-200 dark:border-gray-700',
		dropdown: 'border-gray-100 dark:border-gray-700',
		navbar: 'border-gray-100 dark:border-gray-700',
		navbarUl: 'border-gray-100 dark:border-gray-700',
		form: 'border-gray-300 dark:border-gray-700',
		primary: 'border-primary-500 dark:bg-primary-200 ',
		none: ''
	};

	let divClass;

	function mouseenter_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler(event) {
		bubble.call(this, $$self, event);
	}

	function focusin_handler(event) {
		bubble.call(this, $$self, event);
	}

	function focusout_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function focusin_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function focusout_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function svelte_element_binding($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			node = $$value;
			$$invalidate(0, node);
		});
	}

	function svelte_element_binding_1($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			node = $$value;
			$$invalidate(0, node);
		});
	}

	$$self.$$set = $$new_props => {
		$$invalidate(27, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(7, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('tag' in $$new_props) $$invalidate(1, tag = $$new_props.tag);
		if ('color' in $$new_props) $$invalidate(8, color = $$new_props.color);
		if ('rounded' in $$new_props) $$invalidate(9, rounded = $$new_props.rounded);
		if ('border' in $$new_props) $$invalidate(10, border = $$new_props.border);
		if ('shadow' in $$new_props) $$invalidate(11, shadow = $$new_props.shadow);
		if ('transition' in $$new_props) $$invalidate(2, transition = $$new_props.transition);
		if ('params' in $$new_props) $$invalidate(3, params = $$new_props.params);
		if ('node' in $$new_props) $$invalidate(0, node = $$new_props.node);
		if ('use' in $$new_props) $$invalidate(4, use = $$new_props.use);
		if ('options' in $$new_props) $$invalidate(5, options = $$new_props.options);
		if ('$$scope' in $$new_props) $$invalidate(12, $$scope = $$new_props.$$scope);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*color*/ 256) {
			setContext('color', color);
		}

		$$invalidate(6, divClass = classNames(bgColors[color], textColors[color], rounded && (color === 'dropdown' ? 'rounded' : 'rounded-lg'), border && 'border', borderColors[color], shadow && 'shadow-md', $$props.class));
	};

	$$props = exclude_internal_props($$props);

	return [
		node,
		tag,
		transition,
		params,
		use,
		options,
		divClass,
		$$restProps,
		color,
		rounded,
		border,
		shadow,
		$$scope,
		slots,
		mouseenter_handler,
		mouseleave_handler,
		focusin_handler,
		focusout_handler,
		mouseenter_handler_1,
		mouseleave_handler_1,
		focusin_handler_1,
		focusout_handler_1,
		svelte_element_binding,
		svelte_element_binding_1
	];
}

let Component$e = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$e, create_fragment$e, safe_not_equal, {
			tag: 1,
			color: 8,
			rounded: 9,
			border: 10,
			shadow: 11,
			transition: 2,
			params: 3,
			node: 0,
			use: 4,
			options: 5
		});
	}
};

function cubicOut(t) {
    const f = t - 1.0;
    return f * f * f + 1.0;
}
function quintOut(t) {
    return --t * t * t * t * t + 1;
}

function slide(node, { delay = 0, duration = 400, easing = cubicOut, axis = 'y' } = {}) {
    const style = getComputedStyle(node);
    const opacity = +style.opacity;
    const primary_property = axis === 'y' ? 'height' : 'width';
    const primary_property_value = parseFloat(style[primary_property]);
    const secondary_properties = axis === 'y' ? ['top', 'bottom'] : ['left', 'right'];
    const capitalized_secondary_properties = secondary_properties.map((e) => `${e[0].toUpperCase()}${e.slice(1)}`);
    const padding_start_value = parseFloat(style[`padding${capitalized_secondary_properties[0]}`]);
    const padding_end_value = parseFloat(style[`padding${capitalized_secondary_properties[1]}`]);
    const margin_start_value = parseFloat(style[`margin${capitalized_secondary_properties[0]}`]);
    const margin_end_value = parseFloat(style[`margin${capitalized_secondary_properties[1]}`]);
    const border_width_start_value = parseFloat(style[`border${capitalized_secondary_properties[0]}Width`]);
    const border_width_end_value = parseFloat(style[`border${capitalized_secondary_properties[1]}Width`]);
    return {
        delay,
        duration,
        easing,
        css: t => 'overflow: hidden;' +
            `opacity: ${Math.min(t * 20, 1) * opacity};` +
            `${primary_property}: ${t * primary_property_value}px;` +
            `padding-${secondary_properties[0]}: ${t * padding_start_value}px;` +
            `padding-${secondary_properties[1]}: ${t * padding_end_value}px;` +
            `margin-${secondary_properties[0]}: ${t * margin_start_value}px;` +
            `margin-${secondary_properties[1]}: ${t * margin_end_value}px;` +
            `border-${secondary_properties[0]}-width: ${t * border_width_start_value}px;` +
            `border-${secondary_properties[1]}-width: ${t * border_width_end_value}px;`
    };
}

/* generated by Svelte v3.59.1 */
const get_default_slot_changes$1 = dirty => ({ svgSize: dirty & /*size*/ 4 });

const get_default_slot_context$1 = ctx => ({
	svgSize: /*svgSizes*/ ctx[4][/*size*/ ctx[2]]
});

// (36:2) {#if name}
function create_if_block$5(ctx) {
	let span;
	let t;

	return {
		c() {
			span = element("span");
			t = text(/*name*/ ctx[0]);
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, /*name*/ ctx[0]);
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "sr-only");
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		p(ctx, dirty) {
			if (dirty & /*name*/ 1) set_data(t, /*name*/ ctx[0]);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

function create_fragment$d(ctx) {
	let button;
	let t;
	let button_aria_label_value;
	let current;
	let mounted;
	let dispose;
	let if_block = /*name*/ ctx[0] && create_if_block$5(ctx);
	const default_slot_template = /*#slots*/ ctx[8].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[7], get_default_slot_context$1);

	let button_levels = [
		{ type: "button" },
		/*$$restProps*/ ctx[5],
		{ class: /*buttonClass*/ ctx[3] },
		{
			"aria-label": button_aria_label_value = /*ariaLabel*/ ctx[1] ?? /*name*/ ctx[0]
		}
	];

	let button_data = {};

	for (let i = 0; i < button_levels.length; i += 1) {
		button_data = assign(button_data, button_levels[i]);
	}

	return {
		c() {
			button = element("button");
			if (if_block) if_block.c();
			t = space();
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			button = claim_element(nodes, "BUTTON", {
				type: true,
				class: true,
				"aria-label": true
			});

			var button_nodes = children(button);
			if (if_block) if_block.l(button_nodes);
			t = claim_space(button_nodes);
			if (default_slot) default_slot.l(button_nodes);
			button_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_attributes(button, button_data);
		},
		m(target, anchor) {
			insert_hydration(target, button, anchor);
			if (if_block) if_block.m(button, null);
			append_hydration(button, t);

			if (default_slot) {
				default_slot.m(button, null);
			}

			if (button.autofocus) button.focus();
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[9]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (/*name*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$5(ctx);
					if_block.c();
					if_block.m(button, t);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope, size*/ 132)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[7],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[7])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[7], dirty, get_default_slot_changes$1),
						get_default_slot_context$1
					);
				}
			}

			set_attributes(button, button_data = get_spread_update(button_levels, [
				{ type: "button" },
				dirty & /*$$restProps*/ 32 && /*$$restProps*/ ctx[5],
				(!current || dirty & /*buttonClass*/ 8) && { class: /*buttonClass*/ ctx[3] },
				(!current || dirty & /*ariaLabel, name*/ 3 && button_aria_label_value !== (button_aria_label_value = /*ariaLabel*/ ctx[1] ?? /*name*/ ctx[0])) && { "aria-label": button_aria_label_value }
			]));
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(button);
			if (if_block) if_block.d();
			if (default_slot) default_slot.d(detaching);
			mounted = false;
			dispose();
		}
	};
}

function instance$d($$self, $$props, $$invalidate) {
	const omit_props_names = ["color","name","ariaLabel","size"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	const background = getContext('background');
	let { color = 'default' } = $$props;
	let { name = undefined } = $$props;
	let { ariaLabel = undefined } = $$props;
	let { size = 'md' } = $$props;

	const colors = {
		dark: 'text-gray-500 hover:text-gray-900 hover:bg-gray-200 dark:text-gray-400 dark:hover:text-white dark:hover:bg-gray-700',
		gray: 'text-gray-500 focus:ring-gray-400 hover:bg-gray-200 dark:hover:bg-gray-700',
		red: 'text-red-500 focus:ring-red-400 hover:bg-red-200 dark:hover:bg-gray-700',
		yellow: 'text-yellow-500 focus:ring-yellow-400 hover:bg-yellow-200 dark:hover:bg-gray-700',
		green: 'text-green-500 focus:ring-green-400 hover:bg-green-200 dark:hover:bg-gray-700',
		indigo: 'text-indigo-500 focus:ring-indigo-400 hover:bg-indigo-200 dark:hover:bg-gray-700',
		purple: 'text-purple-500 focus:ring-purple-400 hover:bg-purple-200 dark:hover:bg-gray-700',
		pink: 'text-pink-500 focus:ring-pink-400 hover:bg-pink-200 dark:hover:bg-gray-700',
		blue: 'text-blue-500 focus:ring-blue-400 hover:bg-blue-200 dark:hover:bg-gray-700',
		default: 'focus:ring-gray-400 '
	};

	const sizing = {
		xs: 'm-0.5 rounded focus:ring-1 p-0.5',
		sm: 'm-0.5 rounded focus:ring-1 p-0.5',
		md: 'rounded-lg focus:ring-2 p-1.5'
	};

	let buttonClass;

	const svgSizes = {
		xs: 'w-3 h-3',
		sm: 'w-3.5 h-3.5',
		md: 'w-5 h-5'
	};

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	$$self.$$set = $$new_props => {
		$$invalidate(13, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(5, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('color' in $$new_props) $$invalidate(6, color = $$new_props.color);
		if ('name' in $$new_props) $$invalidate(0, name = $$new_props.name);
		if ('ariaLabel' in $$new_props) $$invalidate(1, ariaLabel = $$new_props.ariaLabel);
		if ('size' in $$new_props) $$invalidate(2, size = $$new_props.size);
		if ('$$scope' in $$new_props) $$invalidate(7, $$scope = $$new_props.$$scope);
	};

	$$self.$$.update = () => {
		$$invalidate(3, buttonClass = classNames(
			'focus:outline-none whitespace-normal',
			sizing[size],
			colors[color],
			color === 'default' && (background
			? 'hover:bg-gray-100 dark:hover:bg-gray-600'
			: 'hover:bg-gray-100 dark:hover:bg-gray-700'),
			$$props.class
		));
	};

	$$props = exclude_internal_props($$props);

	return [
		name,
		ariaLabel,
		size,
		buttonClass,
		svgSizes,
		$$restProps,
		color,
		$$scope,
		slots,
		click_handler
	];
}

let Component$d = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$d, create_fragment$d, safe_not_equal, { color: 6, name: 0, ariaLabel: 1, size: 2 });
	}
};

var top = 'top';
var bottom = 'bottom';
var right = 'right';
var left = 'left';
var auto = 'auto';
var basePlacements = [top, bottom, right, left];
var start = 'start';
var end = 'end';
var clippingParents = 'clippingParents';
var viewport = 'viewport';
var popper = 'popper';
var reference = 'reference';
var variationPlacements = /*#__PURE__*/basePlacements.reduce(function (acc, placement) {
  return acc.concat([placement + "-" + start, placement + "-" + end]);
}, []);
var placements = /*#__PURE__*/[].concat(basePlacements, [auto]).reduce(function (acc, placement) {
  return acc.concat([placement, placement + "-" + start, placement + "-" + end]);
}, []); // modifiers that need to read the DOM

var beforeRead = 'beforeRead';
var read = 'read';
var afterRead = 'afterRead'; // pure-logic modifiers

var beforeMain = 'beforeMain';
var main = 'main';
var afterMain = 'afterMain'; // modifier with the purpose to write to the DOM (or write into a framework state)

var beforeWrite = 'beforeWrite';
var write = 'write';
var afterWrite = 'afterWrite';
var modifierPhases = [beforeRead, read, afterRead, beforeMain, main, afterMain, beforeWrite, write, afterWrite];

function getNodeName(element) {
  return element ? (element.nodeName || '').toLowerCase() : null;
}

function getWindow(node) {
  if (node == null) {
    return window;
  }

  if (node.toString() !== '[object Window]') {
    var ownerDocument = node.ownerDocument;
    return ownerDocument ? ownerDocument.defaultView || window : window;
  }

  return node;
}

function isElement(node) {
  var OwnElement = getWindow(node).Element;
  return node instanceof OwnElement || node instanceof Element;
}

function isHTMLElement(node) {
  var OwnElement = getWindow(node).HTMLElement;
  return node instanceof OwnElement || node instanceof HTMLElement;
}

function isShadowRoot(node) {
  // IE 11 has no ShadowRoot
  if (typeof ShadowRoot === 'undefined') {
    return false;
  }

  var OwnElement = getWindow(node).ShadowRoot;
  return node instanceof OwnElement || node instanceof ShadowRoot;
}

// and applies them to the HTMLElements such as popper and arrow

function applyStyles(_ref) {
  var state = _ref.state;
  Object.keys(state.elements).forEach(function (name) {
    var style = state.styles[name] || {};
    var attributes = state.attributes[name] || {};
    var element = state.elements[name]; // arrow is optional + virtual elements

    if (!isHTMLElement(element) || !getNodeName(element)) {
      return;
    } // Flow doesn't support to extend this property, but it's the most
    // effective way to apply styles to an HTMLElement
    // $FlowFixMe[cannot-write]


    Object.assign(element.style, style);
    Object.keys(attributes).forEach(function (name) {
      var value = attributes[name];

      if (value === false) {
        element.removeAttribute(name);
      } else {
        element.setAttribute(name, value === true ? '' : value);
      }
    });
  });
}

function effect$2(_ref2) {
  var state = _ref2.state;
  var initialStyles = {
    popper: {
      position: state.options.strategy,
      left: '0',
      top: '0',
      margin: '0'
    },
    arrow: {
      position: 'absolute'
    },
    reference: {}
  };
  Object.assign(state.elements.popper.style, initialStyles.popper);
  state.styles = initialStyles;

  if (state.elements.arrow) {
    Object.assign(state.elements.arrow.style, initialStyles.arrow);
  }

  return function () {
    Object.keys(state.elements).forEach(function (name) {
      var element = state.elements[name];
      var attributes = state.attributes[name] || {};
      var styleProperties = Object.keys(state.styles.hasOwnProperty(name) ? state.styles[name] : initialStyles[name]); // Set all values to an empty string to unset them

      var style = styleProperties.reduce(function (style, property) {
        style[property] = '';
        return style;
      }, {}); // arrow is optional + virtual elements

      if (!isHTMLElement(element) || !getNodeName(element)) {
        return;
      }

      Object.assign(element.style, style);
      Object.keys(attributes).forEach(function (attribute) {
        element.removeAttribute(attribute);
      });
    });
  };
} // eslint-disable-next-line import/no-unused-modules


var applyStyles$1 = {
  name: 'applyStyles',
  enabled: true,
  phase: 'write',
  fn: applyStyles,
  effect: effect$2,
  requires: ['computeStyles']
};

function getBasePlacement(placement) {
  return placement.split('-')[0];
}

var max = Math.max;
var min = Math.min;
var round = Math.round;

function getUAString() {
  var uaData = navigator.userAgentData;

  if (uaData != null && uaData.brands && Array.isArray(uaData.brands)) {
    return uaData.brands.map(function (item) {
      return item.brand + "/" + item.version;
    }).join(' ');
  }

  return navigator.userAgent;
}

function isLayoutViewport() {
  return !/^((?!chrome|android).)*safari/i.test(getUAString());
}

function getBoundingClientRect(element, includeScale, isFixedStrategy) {
  if (includeScale === void 0) {
    includeScale = false;
  }

  if (isFixedStrategy === void 0) {
    isFixedStrategy = false;
  }

  var clientRect = element.getBoundingClientRect();
  var scaleX = 1;
  var scaleY = 1;

  if (includeScale && isHTMLElement(element)) {
    scaleX = element.offsetWidth > 0 ? round(clientRect.width) / element.offsetWidth || 1 : 1;
    scaleY = element.offsetHeight > 0 ? round(clientRect.height) / element.offsetHeight || 1 : 1;
  }

  var _ref = isElement(element) ? getWindow(element) : window,
      visualViewport = _ref.visualViewport;

  var addVisualOffsets = !isLayoutViewport() && isFixedStrategy;
  var x = (clientRect.left + (addVisualOffsets && visualViewport ? visualViewport.offsetLeft : 0)) / scaleX;
  var y = (clientRect.top + (addVisualOffsets && visualViewport ? visualViewport.offsetTop : 0)) / scaleY;
  var width = clientRect.width / scaleX;
  var height = clientRect.height / scaleY;
  return {
    width: width,
    height: height,
    top: y,
    right: x + width,
    bottom: y + height,
    left: x,
    x: x,
    y: y
  };
}

// means it doesn't take into account transforms.

function getLayoutRect(element) {
  var clientRect = getBoundingClientRect(element); // Use the clientRect sizes if it's not been transformed.
  // Fixes https://github.com/popperjs/popper-core/issues/1223

  var width = element.offsetWidth;
  var height = element.offsetHeight;

  if (Math.abs(clientRect.width - width) <= 1) {
    width = clientRect.width;
  }

  if (Math.abs(clientRect.height - height) <= 1) {
    height = clientRect.height;
  }

  return {
    x: element.offsetLeft,
    y: element.offsetTop,
    width: width,
    height: height
  };
}

function contains(parent, child) {
  var rootNode = child.getRootNode && child.getRootNode(); // First, attempt with faster native method

  if (parent.contains(child)) {
    return true;
  } // then fallback to custom implementation with Shadow DOM support
  else if (rootNode && isShadowRoot(rootNode)) {
      var next = child;

      do {
        if (next && parent.isSameNode(next)) {
          return true;
        } // $FlowFixMe[prop-missing]: need a better way to handle this...


        next = next.parentNode || next.host;
      } while (next);
    } // Give up, the result is false


  return false;
}

function getComputedStyle$1(element) {
  return getWindow(element).getComputedStyle(element);
}

function isTableElement(element) {
  return ['table', 'td', 'th'].indexOf(getNodeName(element)) >= 0;
}

function getDocumentElement(element) {
  // $FlowFixMe[incompatible-return]: assume body is always available
  return ((isElement(element) ? element.ownerDocument : // $FlowFixMe[prop-missing]
  element.document) || window.document).documentElement;
}

function getParentNode(element) {
  if (getNodeName(element) === 'html') {
    return element;
  }

  return (// this is a quicker (but less type safe) way to save quite some bytes from the bundle
    // $FlowFixMe[incompatible-return]
    // $FlowFixMe[prop-missing]
    element.assignedSlot || // step into the shadow DOM of the parent of a slotted node
    element.parentNode || ( // DOM Element detected
    isShadowRoot(element) ? element.host : null) || // ShadowRoot detected
    // $FlowFixMe[incompatible-call]: HTMLElement is a Node
    getDocumentElement(element) // fallback

  );
}

function getTrueOffsetParent(element) {
  if (!isHTMLElement(element) || // https://github.com/popperjs/popper-core/issues/837
  getComputedStyle$1(element).position === 'fixed') {
    return null;
  }

  return element.offsetParent;
} // `.offsetParent` reports `null` for fixed elements, while absolute elements
// return the containing block


function getContainingBlock(element) {
  var isFirefox = /firefox/i.test(getUAString());
  var isIE = /Trident/i.test(getUAString());

  if (isIE && isHTMLElement(element)) {
    // In IE 9, 10 and 11 fixed elements containing block is always established by the viewport
    var elementCss = getComputedStyle$1(element);

    if (elementCss.position === 'fixed') {
      return null;
    }
  }

  var currentNode = getParentNode(element);

  if (isShadowRoot(currentNode)) {
    currentNode = currentNode.host;
  }

  while (isHTMLElement(currentNode) && ['html', 'body'].indexOf(getNodeName(currentNode)) < 0) {
    var css = getComputedStyle$1(currentNode); // This is non-exhaustive but covers the most common CSS properties that
    // create a containing block.
    // https://developer.mozilla.org/en-US/docs/Web/CSS/Containing_block#identifying_the_containing_block

    if (css.transform !== 'none' || css.perspective !== 'none' || css.contain === 'paint' || ['transform', 'perspective'].indexOf(css.willChange) !== -1 || isFirefox && css.willChange === 'filter' || isFirefox && css.filter && css.filter !== 'none') {
      return currentNode;
    } else {
      currentNode = currentNode.parentNode;
    }
  }

  return null;
} // Gets the closest ancestor positioned element. Handles some edge cases,
// such as table ancestors and cross browser bugs.


function getOffsetParent(element) {
  var window = getWindow(element);
  var offsetParent = getTrueOffsetParent(element);

  while (offsetParent && isTableElement(offsetParent) && getComputedStyle$1(offsetParent).position === 'static') {
    offsetParent = getTrueOffsetParent(offsetParent);
  }

  if (offsetParent && (getNodeName(offsetParent) === 'html' || getNodeName(offsetParent) === 'body' && getComputedStyle$1(offsetParent).position === 'static')) {
    return window;
  }

  return offsetParent || getContainingBlock(element) || window;
}

function getMainAxisFromPlacement(placement) {
  return ['top', 'bottom'].indexOf(placement) >= 0 ? 'x' : 'y';
}

function within(min$1, value, max$1) {
  return max(min$1, min(value, max$1));
}
function withinMaxClamp(min, value, max) {
  var v = within(min, value, max);
  return v > max ? max : v;
}

function getFreshSideObject() {
  return {
    top: 0,
    right: 0,
    bottom: 0,
    left: 0
  };
}

function mergePaddingObject(paddingObject) {
  return Object.assign({}, getFreshSideObject(), paddingObject);
}

function expandToHashMap(value, keys) {
  return keys.reduce(function (hashMap, key) {
    hashMap[key] = value;
    return hashMap;
  }, {});
}

var toPaddingObject = function toPaddingObject(padding, state) {
  padding = typeof padding === 'function' ? padding(Object.assign({}, state.rects, {
    placement: state.placement
  })) : padding;
  return mergePaddingObject(typeof padding !== 'number' ? padding : expandToHashMap(padding, basePlacements));
};

function arrow(_ref) {
  var _state$modifiersData$;

  var state = _ref.state,
      name = _ref.name,
      options = _ref.options;
  var arrowElement = state.elements.arrow;
  var popperOffsets = state.modifiersData.popperOffsets;
  var basePlacement = getBasePlacement(state.placement);
  var axis = getMainAxisFromPlacement(basePlacement);
  var isVertical = [left, right].indexOf(basePlacement) >= 0;
  var len = isVertical ? 'height' : 'width';

  if (!arrowElement || !popperOffsets) {
    return;
  }

  var paddingObject = toPaddingObject(options.padding, state);
  var arrowRect = getLayoutRect(arrowElement);
  var minProp = axis === 'y' ? top : left;
  var maxProp = axis === 'y' ? bottom : right;
  var endDiff = state.rects.reference[len] + state.rects.reference[axis] - popperOffsets[axis] - state.rects.popper[len];
  var startDiff = popperOffsets[axis] - state.rects.reference[axis];
  var arrowOffsetParent = getOffsetParent(arrowElement);
  var clientSize = arrowOffsetParent ? axis === 'y' ? arrowOffsetParent.clientHeight || 0 : arrowOffsetParent.clientWidth || 0 : 0;
  var centerToReference = endDiff / 2 - startDiff / 2; // Make sure the arrow doesn't overflow the popper if the center point is
  // outside of the popper bounds

  var min = paddingObject[minProp];
  var max = clientSize - arrowRect[len] - paddingObject[maxProp];
  var center = clientSize / 2 - arrowRect[len] / 2 + centerToReference;
  var offset = within(min, center, max); // Prevents breaking syntax highlighting...

  var axisProp = axis;
  state.modifiersData[name] = (_state$modifiersData$ = {}, _state$modifiersData$[axisProp] = offset, _state$modifiersData$.centerOffset = offset - center, _state$modifiersData$);
}

function effect$1(_ref2) {
  var state = _ref2.state,
      options = _ref2.options;
  var _options$element = options.element,
      arrowElement = _options$element === void 0 ? '[data-popper-arrow]' : _options$element;

  if (arrowElement == null) {
    return;
  } // CSS selector


  if (typeof arrowElement === 'string') {
    arrowElement = state.elements.popper.querySelector(arrowElement);

    if (!arrowElement) {
      return;
    }
  }

  if (!contains(state.elements.popper, arrowElement)) {
    return;
  }

  state.elements.arrow = arrowElement;
} // eslint-disable-next-line import/no-unused-modules


var arrow$1 = {
  name: 'arrow',
  enabled: true,
  phase: 'main',
  fn: arrow,
  effect: effect$1,
  requires: ['popperOffsets'],
  requiresIfExists: ['preventOverflow']
};

function getVariation(placement) {
  return placement.split('-')[1];
}

var unsetSides = {
  top: 'auto',
  right: 'auto',
  bottom: 'auto',
  left: 'auto'
}; // Round the offsets to the nearest suitable subpixel based on the DPR.
// Zooming can change the DPR, but it seems to report a value that will
// cleanly divide the values into the appropriate subpixels.

function roundOffsetsByDPR(_ref, win) {
  var x = _ref.x,
      y = _ref.y;
  var dpr = win.devicePixelRatio || 1;
  return {
    x: round(x * dpr) / dpr || 0,
    y: round(y * dpr) / dpr || 0
  };
}

function mapToStyles(_ref2) {
  var _Object$assign2;

  var popper = _ref2.popper,
      popperRect = _ref2.popperRect,
      placement = _ref2.placement,
      variation = _ref2.variation,
      offsets = _ref2.offsets,
      position = _ref2.position,
      gpuAcceleration = _ref2.gpuAcceleration,
      adaptive = _ref2.adaptive,
      roundOffsets = _ref2.roundOffsets,
      isFixed = _ref2.isFixed;
  var _offsets$x = offsets.x,
      x = _offsets$x === void 0 ? 0 : _offsets$x,
      _offsets$y = offsets.y,
      y = _offsets$y === void 0 ? 0 : _offsets$y;

  var _ref3 = typeof roundOffsets === 'function' ? roundOffsets({
    x: x,
    y: y
  }) : {
    x: x,
    y: y
  };

  x = _ref3.x;
  y = _ref3.y;
  var hasX = offsets.hasOwnProperty('x');
  var hasY = offsets.hasOwnProperty('y');
  var sideX = left;
  var sideY = top;
  var win = window;

  if (adaptive) {
    var offsetParent = getOffsetParent(popper);
    var heightProp = 'clientHeight';
    var widthProp = 'clientWidth';

    if (offsetParent === getWindow(popper)) {
      offsetParent = getDocumentElement(popper);

      if (getComputedStyle$1(offsetParent).position !== 'static' && position === 'absolute') {
        heightProp = 'scrollHeight';
        widthProp = 'scrollWidth';
      }
    } // $FlowFixMe[incompatible-cast]: force type refinement, we compare offsetParent with window above, but Flow doesn't detect it


    offsetParent = offsetParent;

    if (placement === top || (placement === left || placement === right) && variation === end) {
      sideY = bottom;
      var offsetY = isFixed && offsetParent === win && win.visualViewport ? win.visualViewport.height : // $FlowFixMe[prop-missing]
      offsetParent[heightProp];
      y -= offsetY - popperRect.height;
      y *= gpuAcceleration ? 1 : -1;
    }

    if (placement === left || (placement === top || placement === bottom) && variation === end) {
      sideX = right;
      var offsetX = isFixed && offsetParent === win && win.visualViewport ? win.visualViewport.width : // $FlowFixMe[prop-missing]
      offsetParent[widthProp];
      x -= offsetX - popperRect.width;
      x *= gpuAcceleration ? 1 : -1;
    }
  }

  var commonStyles = Object.assign({
    position: position
  }, adaptive && unsetSides);

  var _ref4 = roundOffsets === true ? roundOffsetsByDPR({
    x: x,
    y: y
  }, getWindow(popper)) : {
    x: x,
    y: y
  };

  x = _ref4.x;
  y = _ref4.y;

  if (gpuAcceleration) {
    var _Object$assign;

    return Object.assign({}, commonStyles, (_Object$assign = {}, _Object$assign[sideY] = hasY ? '0' : '', _Object$assign[sideX] = hasX ? '0' : '', _Object$assign.transform = (win.devicePixelRatio || 1) <= 1 ? "translate(" + x + "px, " + y + "px)" : "translate3d(" + x + "px, " + y + "px, 0)", _Object$assign));
  }

  return Object.assign({}, commonStyles, (_Object$assign2 = {}, _Object$assign2[sideY] = hasY ? y + "px" : '', _Object$assign2[sideX] = hasX ? x + "px" : '', _Object$assign2.transform = '', _Object$assign2));
}

function computeStyles(_ref5) {
  var state = _ref5.state,
      options = _ref5.options;
  var _options$gpuAccelerat = options.gpuAcceleration,
      gpuAcceleration = _options$gpuAccelerat === void 0 ? true : _options$gpuAccelerat,
      _options$adaptive = options.adaptive,
      adaptive = _options$adaptive === void 0 ? true : _options$adaptive,
      _options$roundOffsets = options.roundOffsets,
      roundOffsets = _options$roundOffsets === void 0 ? true : _options$roundOffsets;
  var commonStyles = {
    placement: getBasePlacement(state.placement),
    variation: getVariation(state.placement),
    popper: state.elements.popper,
    popperRect: state.rects.popper,
    gpuAcceleration: gpuAcceleration,
    isFixed: state.options.strategy === 'fixed'
  };

  if (state.modifiersData.popperOffsets != null) {
    state.styles.popper = Object.assign({}, state.styles.popper, mapToStyles(Object.assign({}, commonStyles, {
      offsets: state.modifiersData.popperOffsets,
      position: state.options.strategy,
      adaptive: adaptive,
      roundOffsets: roundOffsets
    })));
  }

  if (state.modifiersData.arrow != null) {
    state.styles.arrow = Object.assign({}, state.styles.arrow, mapToStyles(Object.assign({}, commonStyles, {
      offsets: state.modifiersData.arrow,
      position: 'absolute',
      adaptive: false,
      roundOffsets: roundOffsets
    })));
  }

  state.attributes.popper = Object.assign({}, state.attributes.popper, {
    'data-popper-placement': state.placement
  });
} // eslint-disable-next-line import/no-unused-modules


var computeStyles$1 = {
  name: 'computeStyles',
  enabled: true,
  phase: 'beforeWrite',
  fn: computeStyles,
  data: {}
};

var passive = {
  passive: true
};

function effect(_ref) {
  var state = _ref.state,
      instance = _ref.instance,
      options = _ref.options;
  var _options$scroll = options.scroll,
      scroll = _options$scroll === void 0 ? true : _options$scroll,
      _options$resize = options.resize,
      resize = _options$resize === void 0 ? true : _options$resize;
  var window = getWindow(state.elements.popper);
  var scrollParents = [].concat(state.scrollParents.reference, state.scrollParents.popper);

  if (scroll) {
    scrollParents.forEach(function (scrollParent) {
      scrollParent.addEventListener('scroll', instance.update, passive);
    });
  }

  if (resize) {
    window.addEventListener('resize', instance.update, passive);
  }

  return function () {
    if (scroll) {
      scrollParents.forEach(function (scrollParent) {
        scrollParent.removeEventListener('scroll', instance.update, passive);
      });
    }

    if (resize) {
      window.removeEventListener('resize', instance.update, passive);
    }
  };
} // eslint-disable-next-line import/no-unused-modules


var eventListeners = {
  name: 'eventListeners',
  enabled: true,
  phase: 'write',
  fn: function fn() {},
  effect: effect,
  data: {}
};

var hash$1 = {
  left: 'right',
  right: 'left',
  bottom: 'top',
  top: 'bottom'
};
function getOppositePlacement(placement) {
  return placement.replace(/left|right|bottom|top/g, function (matched) {
    return hash$1[matched];
  });
}

var hash = {
  start: 'end',
  end: 'start'
};
function getOppositeVariationPlacement(placement) {
  return placement.replace(/start|end/g, function (matched) {
    return hash[matched];
  });
}

function getWindowScroll(node) {
  var win = getWindow(node);
  var scrollLeft = win.pageXOffset;
  var scrollTop = win.pageYOffset;
  return {
    scrollLeft: scrollLeft,
    scrollTop: scrollTop
  };
}

function getWindowScrollBarX(element) {
  // If <html> has a CSS width greater than the viewport, then this will be
  // incorrect for RTL.
  // Popper 1 is broken in this case and never had a bug report so let's assume
  // it's not an issue. I don't think anyone ever specifies width on <html>
  // anyway.
  // Browsers where the left scrollbar doesn't cause an issue report `0` for
  // this (e.g. Edge 2019, IE11, Safari)
  return getBoundingClientRect(getDocumentElement(element)).left + getWindowScroll(element).scrollLeft;
}

function getViewportRect(element, strategy) {
  var win = getWindow(element);
  var html = getDocumentElement(element);
  var visualViewport = win.visualViewport;
  var width = html.clientWidth;
  var height = html.clientHeight;
  var x = 0;
  var y = 0;

  if (visualViewport) {
    width = visualViewport.width;
    height = visualViewport.height;
    var layoutViewport = isLayoutViewport();

    if (layoutViewport || !layoutViewport && strategy === 'fixed') {
      x = visualViewport.offsetLeft;
      y = visualViewport.offsetTop;
    }
  }

  return {
    width: width,
    height: height,
    x: x + getWindowScrollBarX(element),
    y: y
  };
}

// of the `<html>` and `<body>` rect bounds if horizontally scrollable

function getDocumentRect(element) {
  var _element$ownerDocumen;

  var html = getDocumentElement(element);
  var winScroll = getWindowScroll(element);
  var body = (_element$ownerDocumen = element.ownerDocument) == null ? void 0 : _element$ownerDocumen.body;
  var width = max(html.scrollWidth, html.clientWidth, body ? body.scrollWidth : 0, body ? body.clientWidth : 0);
  var height = max(html.scrollHeight, html.clientHeight, body ? body.scrollHeight : 0, body ? body.clientHeight : 0);
  var x = -winScroll.scrollLeft + getWindowScrollBarX(element);
  var y = -winScroll.scrollTop;

  if (getComputedStyle$1(body || html).direction === 'rtl') {
    x += max(html.clientWidth, body ? body.clientWidth : 0) - width;
  }

  return {
    width: width,
    height: height,
    x: x,
    y: y
  };
}

function isScrollParent(element) {
  // Firefox wants us to check `-x` and `-y` variations as well
  var _getComputedStyle = getComputedStyle$1(element),
      overflow = _getComputedStyle.overflow,
      overflowX = _getComputedStyle.overflowX,
      overflowY = _getComputedStyle.overflowY;

  return /auto|scroll|overlay|hidden/.test(overflow + overflowY + overflowX);
}

function getScrollParent(node) {
  if (['html', 'body', '#document'].indexOf(getNodeName(node)) >= 0) {
    // $FlowFixMe[incompatible-return]: assume body is always available
    return node.ownerDocument.body;
  }

  if (isHTMLElement(node) && isScrollParent(node)) {
    return node;
  }

  return getScrollParent(getParentNode(node));
}

/*
given a DOM element, return the list of all scroll parents, up the list of ancesors
until we get to the top window object. This list is what we attach scroll listeners
to, because if any of these parent elements scroll, we'll need to re-calculate the
reference element's position.
*/

function listScrollParents(element, list) {
  var _element$ownerDocumen;

  if (list === void 0) {
    list = [];
  }

  var scrollParent = getScrollParent(element);
  var isBody = scrollParent === ((_element$ownerDocumen = element.ownerDocument) == null ? void 0 : _element$ownerDocumen.body);
  var win = getWindow(scrollParent);
  var target = isBody ? [win].concat(win.visualViewport || [], isScrollParent(scrollParent) ? scrollParent : []) : scrollParent;
  var updatedList = list.concat(target);
  return isBody ? updatedList : // $FlowFixMe[incompatible-call]: isBody tells us target will be an HTMLElement here
  updatedList.concat(listScrollParents(getParentNode(target)));
}

function rectToClientRect(rect) {
  return Object.assign({}, rect, {
    left: rect.x,
    top: rect.y,
    right: rect.x + rect.width,
    bottom: rect.y + rect.height
  });
}

function getInnerBoundingClientRect(element, strategy) {
  var rect = getBoundingClientRect(element, false, strategy === 'fixed');
  rect.top = rect.top + element.clientTop;
  rect.left = rect.left + element.clientLeft;
  rect.bottom = rect.top + element.clientHeight;
  rect.right = rect.left + element.clientWidth;
  rect.width = element.clientWidth;
  rect.height = element.clientHeight;
  rect.x = rect.left;
  rect.y = rect.top;
  return rect;
}

function getClientRectFromMixedType(element, clippingParent, strategy) {
  return clippingParent === viewport ? rectToClientRect(getViewportRect(element, strategy)) : isElement(clippingParent) ? getInnerBoundingClientRect(clippingParent, strategy) : rectToClientRect(getDocumentRect(getDocumentElement(element)));
} // A "clipping parent" is an overflowable container with the characteristic of
// clipping (or hiding) overflowing elements with a position different from
// `initial`


function getClippingParents(element) {
  var clippingParents = listScrollParents(getParentNode(element));
  var canEscapeClipping = ['absolute', 'fixed'].indexOf(getComputedStyle$1(element).position) >= 0;
  var clipperElement = canEscapeClipping && isHTMLElement(element) ? getOffsetParent(element) : element;

  if (!isElement(clipperElement)) {
    return [];
  } // $FlowFixMe[incompatible-return]: https://github.com/facebook/flow/issues/1414


  return clippingParents.filter(function (clippingParent) {
    return isElement(clippingParent) && contains(clippingParent, clipperElement) && getNodeName(clippingParent) !== 'body';
  });
} // Gets the maximum area that the element is visible in due to any number of
// clipping parents


function getClippingRect(element, boundary, rootBoundary, strategy) {
  var mainClippingParents = boundary === 'clippingParents' ? getClippingParents(element) : [].concat(boundary);
  var clippingParents = [].concat(mainClippingParents, [rootBoundary]);
  var firstClippingParent = clippingParents[0];
  var clippingRect = clippingParents.reduce(function (accRect, clippingParent) {
    var rect = getClientRectFromMixedType(element, clippingParent, strategy);
    accRect.top = max(rect.top, accRect.top);
    accRect.right = min(rect.right, accRect.right);
    accRect.bottom = min(rect.bottom, accRect.bottom);
    accRect.left = max(rect.left, accRect.left);
    return accRect;
  }, getClientRectFromMixedType(element, firstClippingParent, strategy));
  clippingRect.width = clippingRect.right - clippingRect.left;
  clippingRect.height = clippingRect.bottom - clippingRect.top;
  clippingRect.x = clippingRect.left;
  clippingRect.y = clippingRect.top;
  return clippingRect;
}

function computeOffsets(_ref) {
  var reference = _ref.reference,
      element = _ref.element,
      placement = _ref.placement;
  var basePlacement = placement ? getBasePlacement(placement) : null;
  var variation = placement ? getVariation(placement) : null;
  var commonX = reference.x + reference.width / 2 - element.width / 2;
  var commonY = reference.y + reference.height / 2 - element.height / 2;
  var offsets;

  switch (basePlacement) {
    case top:
      offsets = {
        x: commonX,
        y: reference.y - element.height
      };
      break;

    case bottom:
      offsets = {
        x: commonX,
        y: reference.y + reference.height
      };
      break;

    case right:
      offsets = {
        x: reference.x + reference.width,
        y: commonY
      };
      break;

    case left:
      offsets = {
        x: reference.x - element.width,
        y: commonY
      };
      break;

    default:
      offsets = {
        x: reference.x,
        y: reference.y
      };
  }

  var mainAxis = basePlacement ? getMainAxisFromPlacement(basePlacement) : null;

  if (mainAxis != null) {
    var len = mainAxis === 'y' ? 'height' : 'width';

    switch (variation) {
      case start:
        offsets[mainAxis] = offsets[mainAxis] - (reference[len] / 2 - element[len] / 2);
        break;

      case end:
        offsets[mainAxis] = offsets[mainAxis] + (reference[len] / 2 - element[len] / 2);
        break;
    }
  }

  return offsets;
}

function detectOverflow(state, options) {
  if (options === void 0) {
    options = {};
  }

  var _options = options,
      _options$placement = _options.placement,
      placement = _options$placement === void 0 ? state.placement : _options$placement,
      _options$strategy = _options.strategy,
      strategy = _options$strategy === void 0 ? state.strategy : _options$strategy,
      _options$boundary = _options.boundary,
      boundary = _options$boundary === void 0 ? clippingParents : _options$boundary,
      _options$rootBoundary = _options.rootBoundary,
      rootBoundary = _options$rootBoundary === void 0 ? viewport : _options$rootBoundary,
      _options$elementConte = _options.elementContext,
      elementContext = _options$elementConte === void 0 ? popper : _options$elementConte,
      _options$altBoundary = _options.altBoundary,
      altBoundary = _options$altBoundary === void 0 ? false : _options$altBoundary,
      _options$padding = _options.padding,
      padding = _options$padding === void 0 ? 0 : _options$padding;
  var paddingObject = mergePaddingObject(typeof padding !== 'number' ? padding : expandToHashMap(padding, basePlacements));
  var altContext = elementContext === popper ? reference : popper;
  var popperRect = state.rects.popper;
  var element = state.elements[altBoundary ? altContext : elementContext];
  var clippingClientRect = getClippingRect(isElement(element) ? element : element.contextElement || getDocumentElement(state.elements.popper), boundary, rootBoundary, strategy);
  var referenceClientRect = getBoundingClientRect(state.elements.reference);
  var popperOffsets = computeOffsets({
    reference: referenceClientRect,
    element: popperRect,
    strategy: 'absolute',
    placement: placement
  });
  var popperClientRect = rectToClientRect(Object.assign({}, popperRect, popperOffsets));
  var elementClientRect = elementContext === popper ? popperClientRect : referenceClientRect; // positive = overflowing the clipping rect
  // 0 or negative = within the clipping rect

  var overflowOffsets = {
    top: clippingClientRect.top - elementClientRect.top + paddingObject.top,
    bottom: elementClientRect.bottom - clippingClientRect.bottom + paddingObject.bottom,
    left: clippingClientRect.left - elementClientRect.left + paddingObject.left,
    right: elementClientRect.right - clippingClientRect.right + paddingObject.right
  };
  var offsetData = state.modifiersData.offset; // Offsets can be applied only to the popper element

  if (elementContext === popper && offsetData) {
    var offset = offsetData[placement];
    Object.keys(overflowOffsets).forEach(function (key) {
      var multiply = [right, bottom].indexOf(key) >= 0 ? 1 : -1;
      var axis = [top, bottom].indexOf(key) >= 0 ? 'y' : 'x';
      overflowOffsets[key] += offset[axis] * multiply;
    });
  }

  return overflowOffsets;
}

function computeAutoPlacement(state, options) {
  if (options === void 0) {
    options = {};
  }

  var _options = options,
      placement = _options.placement,
      boundary = _options.boundary,
      rootBoundary = _options.rootBoundary,
      padding = _options.padding,
      flipVariations = _options.flipVariations,
      _options$allowedAutoP = _options.allowedAutoPlacements,
      allowedAutoPlacements = _options$allowedAutoP === void 0 ? placements : _options$allowedAutoP;
  var variation = getVariation(placement);
  var placements$1 = variation ? flipVariations ? variationPlacements : variationPlacements.filter(function (placement) {
    return getVariation(placement) === variation;
  }) : basePlacements;
  var allowedPlacements = placements$1.filter(function (placement) {
    return allowedAutoPlacements.indexOf(placement) >= 0;
  });

  if (allowedPlacements.length === 0) {
    allowedPlacements = placements$1;
  } // $FlowFixMe[incompatible-type]: Flow seems to have problems with two array unions...


  var overflows = allowedPlacements.reduce(function (acc, placement) {
    acc[placement] = detectOverflow(state, {
      placement: placement,
      boundary: boundary,
      rootBoundary: rootBoundary,
      padding: padding
    })[getBasePlacement(placement)];
    return acc;
  }, {});
  return Object.keys(overflows).sort(function (a, b) {
    return overflows[a] - overflows[b];
  });
}

function getExpandedFallbackPlacements(placement) {
  if (getBasePlacement(placement) === auto) {
    return [];
  }

  var oppositePlacement = getOppositePlacement(placement);
  return [getOppositeVariationPlacement(placement), oppositePlacement, getOppositeVariationPlacement(oppositePlacement)];
}

function flip(_ref) {
  var state = _ref.state,
      options = _ref.options,
      name = _ref.name;

  if (state.modifiersData[name]._skip) {
    return;
  }

  var _options$mainAxis = options.mainAxis,
      checkMainAxis = _options$mainAxis === void 0 ? true : _options$mainAxis,
      _options$altAxis = options.altAxis,
      checkAltAxis = _options$altAxis === void 0 ? true : _options$altAxis,
      specifiedFallbackPlacements = options.fallbackPlacements,
      padding = options.padding,
      boundary = options.boundary,
      rootBoundary = options.rootBoundary,
      altBoundary = options.altBoundary,
      _options$flipVariatio = options.flipVariations,
      flipVariations = _options$flipVariatio === void 0 ? true : _options$flipVariatio,
      allowedAutoPlacements = options.allowedAutoPlacements;
  var preferredPlacement = state.options.placement;
  var basePlacement = getBasePlacement(preferredPlacement);
  var isBasePlacement = basePlacement === preferredPlacement;
  var fallbackPlacements = specifiedFallbackPlacements || (isBasePlacement || !flipVariations ? [getOppositePlacement(preferredPlacement)] : getExpandedFallbackPlacements(preferredPlacement));
  var placements = [preferredPlacement].concat(fallbackPlacements).reduce(function (acc, placement) {
    return acc.concat(getBasePlacement(placement) === auto ? computeAutoPlacement(state, {
      placement: placement,
      boundary: boundary,
      rootBoundary: rootBoundary,
      padding: padding,
      flipVariations: flipVariations,
      allowedAutoPlacements: allowedAutoPlacements
    }) : placement);
  }, []);
  var referenceRect = state.rects.reference;
  var popperRect = state.rects.popper;
  var checksMap = new Map();
  var makeFallbackChecks = true;
  var firstFittingPlacement = placements[0];

  for (var i = 0; i < placements.length; i++) {
    var placement = placements[i];

    var _basePlacement = getBasePlacement(placement);

    var isStartVariation = getVariation(placement) === start;
    var isVertical = [top, bottom].indexOf(_basePlacement) >= 0;
    var len = isVertical ? 'width' : 'height';
    var overflow = detectOverflow(state, {
      placement: placement,
      boundary: boundary,
      rootBoundary: rootBoundary,
      altBoundary: altBoundary,
      padding: padding
    });
    var mainVariationSide = isVertical ? isStartVariation ? right : left : isStartVariation ? bottom : top;

    if (referenceRect[len] > popperRect[len]) {
      mainVariationSide = getOppositePlacement(mainVariationSide);
    }

    var altVariationSide = getOppositePlacement(mainVariationSide);
    var checks = [];

    if (checkMainAxis) {
      checks.push(overflow[_basePlacement] <= 0);
    }

    if (checkAltAxis) {
      checks.push(overflow[mainVariationSide] <= 0, overflow[altVariationSide] <= 0);
    }

    if (checks.every(function (check) {
      return check;
    })) {
      firstFittingPlacement = placement;
      makeFallbackChecks = false;
      break;
    }

    checksMap.set(placement, checks);
  }

  if (makeFallbackChecks) {
    // `2` may be desired in some cases – research later
    var numberOfChecks = flipVariations ? 3 : 1;

    var _loop = function _loop(_i) {
      var fittingPlacement = placements.find(function (placement) {
        var checks = checksMap.get(placement);

        if (checks) {
          return checks.slice(0, _i).every(function (check) {
            return check;
          });
        }
      });

      if (fittingPlacement) {
        firstFittingPlacement = fittingPlacement;
        return "break";
      }
    };

    for (var _i = numberOfChecks; _i > 0; _i--) {
      var _ret = _loop(_i);

      if (_ret === "break") break;
    }
  }

  if (state.placement !== firstFittingPlacement) {
    state.modifiersData[name]._skip = true;
    state.placement = firstFittingPlacement;
    state.reset = true;
  }
} // eslint-disable-next-line import/no-unused-modules


var flip$1 = {
  name: 'flip',
  enabled: true,
  phase: 'main',
  fn: flip,
  requiresIfExists: ['offset'],
  data: {
    _skip: false
  }
};

function getSideOffsets(overflow, rect, preventedOffsets) {
  if (preventedOffsets === void 0) {
    preventedOffsets = {
      x: 0,
      y: 0
    };
  }

  return {
    top: overflow.top - rect.height - preventedOffsets.y,
    right: overflow.right - rect.width + preventedOffsets.x,
    bottom: overflow.bottom - rect.height + preventedOffsets.y,
    left: overflow.left - rect.width - preventedOffsets.x
  };
}

function isAnySideFullyClipped(overflow) {
  return [top, right, bottom, left].some(function (side) {
    return overflow[side] >= 0;
  });
}

function hide(_ref) {
  var state = _ref.state,
      name = _ref.name;
  var referenceRect = state.rects.reference;
  var popperRect = state.rects.popper;
  var preventedOffsets = state.modifiersData.preventOverflow;
  var referenceOverflow = detectOverflow(state, {
    elementContext: 'reference'
  });
  var popperAltOverflow = detectOverflow(state, {
    altBoundary: true
  });
  var referenceClippingOffsets = getSideOffsets(referenceOverflow, referenceRect);
  var popperEscapeOffsets = getSideOffsets(popperAltOverflow, popperRect, preventedOffsets);
  var isReferenceHidden = isAnySideFullyClipped(referenceClippingOffsets);
  var hasPopperEscaped = isAnySideFullyClipped(popperEscapeOffsets);
  state.modifiersData[name] = {
    referenceClippingOffsets: referenceClippingOffsets,
    popperEscapeOffsets: popperEscapeOffsets,
    isReferenceHidden: isReferenceHidden,
    hasPopperEscaped: hasPopperEscaped
  };
  state.attributes.popper = Object.assign({}, state.attributes.popper, {
    'data-popper-reference-hidden': isReferenceHidden,
    'data-popper-escaped': hasPopperEscaped
  });
} // eslint-disable-next-line import/no-unused-modules


var hide$1 = {
  name: 'hide',
  enabled: true,
  phase: 'main',
  requiresIfExists: ['preventOverflow'],
  fn: hide
};

function distanceAndSkiddingToXY(placement, rects, offset) {
  var basePlacement = getBasePlacement(placement);
  var invertDistance = [left, top].indexOf(basePlacement) >= 0 ? -1 : 1;

  var _ref = typeof offset === 'function' ? offset(Object.assign({}, rects, {
    placement: placement
  })) : offset,
      skidding = _ref[0],
      distance = _ref[1];

  skidding = skidding || 0;
  distance = (distance || 0) * invertDistance;
  return [left, right].indexOf(basePlacement) >= 0 ? {
    x: distance,
    y: skidding
  } : {
    x: skidding,
    y: distance
  };
}

function offset(_ref2) {
  var state = _ref2.state,
      options = _ref2.options,
      name = _ref2.name;
  var _options$offset = options.offset,
      offset = _options$offset === void 0 ? [0, 0] : _options$offset;
  var data = placements.reduce(function (acc, placement) {
    acc[placement] = distanceAndSkiddingToXY(placement, state.rects, offset);
    return acc;
  }, {});
  var _data$state$placement = data[state.placement],
      x = _data$state$placement.x,
      y = _data$state$placement.y;

  if (state.modifiersData.popperOffsets != null) {
    state.modifiersData.popperOffsets.x += x;
    state.modifiersData.popperOffsets.y += y;
  }

  state.modifiersData[name] = data;
} // eslint-disable-next-line import/no-unused-modules


var offset$1 = {
  name: 'offset',
  enabled: true,
  phase: 'main',
  requires: ['popperOffsets'],
  fn: offset
};

function popperOffsets(_ref) {
  var state = _ref.state,
      name = _ref.name;
  // Offsets are the actual position the popper needs to have to be
  // properly positioned near its reference element
  // This is the most basic placement, and will be adjusted by
  // the modifiers in the next step
  state.modifiersData[name] = computeOffsets({
    reference: state.rects.reference,
    element: state.rects.popper,
    strategy: 'absolute',
    placement: state.placement
  });
} // eslint-disable-next-line import/no-unused-modules


var popperOffsets$1 = {
  name: 'popperOffsets',
  enabled: true,
  phase: 'read',
  fn: popperOffsets,
  data: {}
};

function getAltAxis(axis) {
  return axis === 'x' ? 'y' : 'x';
}

function preventOverflow(_ref) {
  var state = _ref.state,
      options = _ref.options,
      name = _ref.name;
  var _options$mainAxis = options.mainAxis,
      checkMainAxis = _options$mainAxis === void 0 ? true : _options$mainAxis,
      _options$altAxis = options.altAxis,
      checkAltAxis = _options$altAxis === void 0 ? false : _options$altAxis,
      boundary = options.boundary,
      rootBoundary = options.rootBoundary,
      altBoundary = options.altBoundary,
      padding = options.padding,
      _options$tether = options.tether,
      tether = _options$tether === void 0 ? true : _options$tether,
      _options$tetherOffset = options.tetherOffset,
      tetherOffset = _options$tetherOffset === void 0 ? 0 : _options$tetherOffset;
  var overflow = detectOverflow(state, {
    boundary: boundary,
    rootBoundary: rootBoundary,
    padding: padding,
    altBoundary: altBoundary
  });
  var basePlacement = getBasePlacement(state.placement);
  var variation = getVariation(state.placement);
  var isBasePlacement = !variation;
  var mainAxis = getMainAxisFromPlacement(basePlacement);
  var altAxis = getAltAxis(mainAxis);
  var popperOffsets = state.modifiersData.popperOffsets;
  var referenceRect = state.rects.reference;
  var popperRect = state.rects.popper;
  var tetherOffsetValue = typeof tetherOffset === 'function' ? tetherOffset(Object.assign({}, state.rects, {
    placement: state.placement
  })) : tetherOffset;
  var normalizedTetherOffsetValue = typeof tetherOffsetValue === 'number' ? {
    mainAxis: tetherOffsetValue,
    altAxis: tetherOffsetValue
  } : Object.assign({
    mainAxis: 0,
    altAxis: 0
  }, tetherOffsetValue);
  var offsetModifierState = state.modifiersData.offset ? state.modifiersData.offset[state.placement] : null;
  var data = {
    x: 0,
    y: 0
  };

  if (!popperOffsets) {
    return;
  }

  if (checkMainAxis) {
    var _offsetModifierState$;

    var mainSide = mainAxis === 'y' ? top : left;
    var altSide = mainAxis === 'y' ? bottom : right;
    var len = mainAxis === 'y' ? 'height' : 'width';
    var offset = popperOffsets[mainAxis];
    var min$1 = offset + overflow[mainSide];
    var max$1 = offset - overflow[altSide];
    var additive = tether ? -popperRect[len] / 2 : 0;
    var minLen = variation === start ? referenceRect[len] : popperRect[len];
    var maxLen = variation === start ? -popperRect[len] : -referenceRect[len]; // We need to include the arrow in the calculation so the arrow doesn't go
    // outside the reference bounds

    var arrowElement = state.elements.arrow;
    var arrowRect = tether && arrowElement ? getLayoutRect(arrowElement) : {
      width: 0,
      height: 0
    };
    var arrowPaddingObject = state.modifiersData['arrow#persistent'] ? state.modifiersData['arrow#persistent'].padding : getFreshSideObject();
    var arrowPaddingMin = arrowPaddingObject[mainSide];
    var arrowPaddingMax = arrowPaddingObject[altSide]; // If the reference length is smaller than the arrow length, we don't want
    // to include its full size in the calculation. If the reference is small
    // and near the edge of a boundary, the popper can overflow even if the
    // reference is not overflowing as well (e.g. virtual elements with no
    // width or height)

    var arrowLen = within(0, referenceRect[len], arrowRect[len]);
    var minOffset = isBasePlacement ? referenceRect[len] / 2 - additive - arrowLen - arrowPaddingMin - normalizedTetherOffsetValue.mainAxis : minLen - arrowLen - arrowPaddingMin - normalizedTetherOffsetValue.mainAxis;
    var maxOffset = isBasePlacement ? -referenceRect[len] / 2 + additive + arrowLen + arrowPaddingMax + normalizedTetherOffsetValue.mainAxis : maxLen + arrowLen + arrowPaddingMax + normalizedTetherOffsetValue.mainAxis;
    var arrowOffsetParent = state.elements.arrow && getOffsetParent(state.elements.arrow);
    var clientOffset = arrowOffsetParent ? mainAxis === 'y' ? arrowOffsetParent.clientTop || 0 : arrowOffsetParent.clientLeft || 0 : 0;
    var offsetModifierValue = (_offsetModifierState$ = offsetModifierState == null ? void 0 : offsetModifierState[mainAxis]) != null ? _offsetModifierState$ : 0;
    var tetherMin = offset + minOffset - offsetModifierValue - clientOffset;
    var tetherMax = offset + maxOffset - offsetModifierValue;
    var preventedOffset = within(tether ? min(min$1, tetherMin) : min$1, offset, tether ? max(max$1, tetherMax) : max$1);
    popperOffsets[mainAxis] = preventedOffset;
    data[mainAxis] = preventedOffset - offset;
  }

  if (checkAltAxis) {
    var _offsetModifierState$2;

    var _mainSide = mainAxis === 'x' ? top : left;

    var _altSide = mainAxis === 'x' ? bottom : right;

    var _offset = popperOffsets[altAxis];

    var _len = altAxis === 'y' ? 'height' : 'width';

    var _min = _offset + overflow[_mainSide];

    var _max = _offset - overflow[_altSide];

    var isOriginSide = [top, left].indexOf(basePlacement) !== -1;

    var _offsetModifierValue = (_offsetModifierState$2 = offsetModifierState == null ? void 0 : offsetModifierState[altAxis]) != null ? _offsetModifierState$2 : 0;

    var _tetherMin = isOriginSide ? _min : _offset - referenceRect[_len] - popperRect[_len] - _offsetModifierValue + normalizedTetherOffsetValue.altAxis;

    var _tetherMax = isOriginSide ? _offset + referenceRect[_len] + popperRect[_len] - _offsetModifierValue - normalizedTetherOffsetValue.altAxis : _max;

    var _preventedOffset = tether && isOriginSide ? withinMaxClamp(_tetherMin, _offset, _tetherMax) : within(tether ? _tetherMin : _min, _offset, tether ? _tetherMax : _max);

    popperOffsets[altAxis] = _preventedOffset;
    data[altAxis] = _preventedOffset - _offset;
  }

  state.modifiersData[name] = data;
} // eslint-disable-next-line import/no-unused-modules


var preventOverflow$1 = {
  name: 'preventOverflow',
  enabled: true,
  phase: 'main',
  fn: preventOverflow,
  requiresIfExists: ['offset']
};

function getHTMLElementScroll(element) {
  return {
    scrollLeft: element.scrollLeft,
    scrollTop: element.scrollTop
  };
}

function getNodeScroll(node) {
  if (node === getWindow(node) || !isHTMLElement(node)) {
    return getWindowScroll(node);
  } else {
    return getHTMLElementScroll(node);
  }
}

function isElementScaled(element) {
  var rect = element.getBoundingClientRect();
  var scaleX = round(rect.width) / element.offsetWidth || 1;
  var scaleY = round(rect.height) / element.offsetHeight || 1;
  return scaleX !== 1 || scaleY !== 1;
} // Returns the composite rect of an element relative to its offsetParent.
// Composite means it takes into account transforms as well as layout.


function getCompositeRect(elementOrVirtualElement, offsetParent, isFixed) {
  if (isFixed === void 0) {
    isFixed = false;
  }

  var isOffsetParentAnElement = isHTMLElement(offsetParent);
  var offsetParentIsScaled = isHTMLElement(offsetParent) && isElementScaled(offsetParent);
  var documentElement = getDocumentElement(offsetParent);
  var rect = getBoundingClientRect(elementOrVirtualElement, offsetParentIsScaled, isFixed);
  var scroll = {
    scrollLeft: 0,
    scrollTop: 0
  };
  var offsets = {
    x: 0,
    y: 0
  };

  if (isOffsetParentAnElement || !isOffsetParentAnElement && !isFixed) {
    if (getNodeName(offsetParent) !== 'body' || // https://github.com/popperjs/popper-core/issues/1078
    isScrollParent(documentElement)) {
      scroll = getNodeScroll(offsetParent);
    }

    if (isHTMLElement(offsetParent)) {
      offsets = getBoundingClientRect(offsetParent, true);
      offsets.x += offsetParent.clientLeft;
      offsets.y += offsetParent.clientTop;
    } else if (documentElement) {
      offsets.x = getWindowScrollBarX(documentElement);
    }
  }

  return {
    x: rect.left + scroll.scrollLeft - offsets.x,
    y: rect.top + scroll.scrollTop - offsets.y,
    width: rect.width,
    height: rect.height
  };
}

function order(modifiers) {
  var map = new Map();
  var visited = new Set();
  var result = [];
  modifiers.forEach(function (modifier) {
    map.set(modifier.name, modifier);
  }); // On visiting object, check for its dependencies and visit them recursively

  function sort(modifier) {
    visited.add(modifier.name);
    var requires = [].concat(modifier.requires || [], modifier.requiresIfExists || []);
    requires.forEach(function (dep) {
      if (!visited.has(dep)) {
        var depModifier = map.get(dep);

        if (depModifier) {
          sort(depModifier);
        }
      }
    });
    result.push(modifier);
  }

  modifiers.forEach(function (modifier) {
    if (!visited.has(modifier.name)) {
      // check for visited object
      sort(modifier);
    }
  });
  return result;
}

function orderModifiers(modifiers) {
  // order based on dependencies
  var orderedModifiers = order(modifiers); // order based on phase

  return modifierPhases.reduce(function (acc, phase) {
    return acc.concat(orderedModifiers.filter(function (modifier) {
      return modifier.phase === phase;
    }));
  }, []);
}

function debounce(fn) {
  var pending;
  return function () {
    if (!pending) {
      pending = new Promise(function (resolve) {
        Promise.resolve().then(function () {
          pending = undefined;
          resolve(fn());
        });
      });
    }

    return pending;
  };
}

function mergeByName(modifiers) {
  var merged = modifiers.reduce(function (merged, current) {
    var existing = merged[current.name];
    merged[current.name] = existing ? Object.assign({}, existing, current, {
      options: Object.assign({}, existing.options, current.options),
      data: Object.assign({}, existing.data, current.data)
    }) : current;
    return merged;
  }, {}); // IE11 does not support Object.values

  return Object.keys(merged).map(function (key) {
    return merged[key];
  });
}

var DEFAULT_OPTIONS = {
  placement: 'bottom',
  modifiers: [],
  strategy: 'absolute'
};

function areValidElements() {
  for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
    args[_key] = arguments[_key];
  }

  return !args.some(function (element) {
    return !(element && typeof element.getBoundingClientRect === 'function');
  });
}

function popperGenerator(generatorOptions) {
  if (generatorOptions === void 0) {
    generatorOptions = {};
  }

  var _generatorOptions = generatorOptions,
      _generatorOptions$def = _generatorOptions.defaultModifiers,
      defaultModifiers = _generatorOptions$def === void 0 ? [] : _generatorOptions$def,
      _generatorOptions$def2 = _generatorOptions.defaultOptions,
      defaultOptions = _generatorOptions$def2 === void 0 ? DEFAULT_OPTIONS : _generatorOptions$def2;
  return function createPopper(reference, popper, options) {
    if (options === void 0) {
      options = defaultOptions;
    }

    var state = {
      placement: 'bottom',
      orderedModifiers: [],
      options: Object.assign({}, DEFAULT_OPTIONS, defaultOptions),
      modifiersData: {},
      elements: {
        reference: reference,
        popper: popper
      },
      attributes: {},
      styles: {}
    };
    var effectCleanupFns = [];
    var isDestroyed = false;
    var instance = {
      state: state,
      setOptions: function setOptions(setOptionsAction) {
        var options = typeof setOptionsAction === 'function' ? setOptionsAction(state.options) : setOptionsAction;
        cleanupModifierEffects();
        state.options = Object.assign({}, defaultOptions, state.options, options);
        state.scrollParents = {
          reference: isElement(reference) ? listScrollParents(reference) : reference.contextElement ? listScrollParents(reference.contextElement) : [],
          popper: listScrollParents(popper)
        }; // Orders the modifiers based on their dependencies and `phase`
        // properties

        var orderedModifiers = orderModifiers(mergeByName([].concat(defaultModifiers, state.options.modifiers))); // Strip out disabled modifiers

        state.orderedModifiers = orderedModifiers.filter(function (m) {
          return m.enabled;
        });
        runModifierEffects();
        return instance.update();
      },
      // Sync update – it will always be executed, even if not necessary. This
      // is useful for low frequency updates where sync behavior simplifies the
      // logic.
      // For high frequency updates (e.g. `resize` and `scroll` events), always
      // prefer the async Popper#update method
      forceUpdate: function forceUpdate() {
        if (isDestroyed) {
          return;
        }

        var _state$elements = state.elements,
            reference = _state$elements.reference,
            popper = _state$elements.popper; // Don't proceed if `reference` or `popper` are not valid elements
        // anymore

        if (!areValidElements(reference, popper)) {
          return;
        } // Store the reference and popper rects to be read by modifiers


        state.rects = {
          reference: getCompositeRect(reference, getOffsetParent(popper), state.options.strategy === 'fixed'),
          popper: getLayoutRect(popper)
        }; // Modifiers have the ability to reset the current update cycle. The
        // most common use case for this is the `flip` modifier changing the
        // placement, which then needs to re-run all the modifiers, because the
        // logic was previously ran for the previous placement and is therefore
        // stale/incorrect

        state.reset = false;
        state.placement = state.options.placement; // On each update cycle, the `modifiersData` property for each modifier
        // is filled with the initial data specified by the modifier. This means
        // it doesn't persist and is fresh on each update.
        // To ensure persistent data, use `${name}#persistent`

        state.orderedModifiers.forEach(function (modifier) {
          return state.modifiersData[modifier.name] = Object.assign({}, modifier.data);
        });

        for (var index = 0; index < state.orderedModifiers.length; index++) {
          if (state.reset === true) {
            state.reset = false;
            index = -1;
            continue;
          }

          var _state$orderedModifie = state.orderedModifiers[index],
              fn = _state$orderedModifie.fn,
              _state$orderedModifie2 = _state$orderedModifie.options,
              _options = _state$orderedModifie2 === void 0 ? {} : _state$orderedModifie2,
              name = _state$orderedModifie.name;

          if (typeof fn === 'function') {
            state = fn({
              state: state,
              options: _options,
              name: name,
              instance: instance
            }) || state;
          }
        }
      },
      // Async and optimistically optimized update – it will not be executed if
      // not necessary (debounced to run at most once-per-tick)
      update: debounce(function () {
        return new Promise(function (resolve) {
          instance.forceUpdate();
          resolve(state);
        });
      }),
      destroy: function destroy() {
        cleanupModifierEffects();
        isDestroyed = true;
      }
    };

    if (!areValidElements(reference, popper)) {
      return instance;
    }

    instance.setOptions(options).then(function (state) {
      if (!isDestroyed && options.onFirstUpdate) {
        options.onFirstUpdate(state);
      }
    }); // Modifiers have the ability to execute arbitrary code before the first
    // update cycle runs. They will be executed in the same order as the update
    // cycle. This is useful when a modifier adds some persistent data that
    // other modifiers need to use, but the modifier is run after the dependent
    // one.

    function runModifierEffects() {
      state.orderedModifiers.forEach(function (_ref) {
        var name = _ref.name,
            _ref$options = _ref.options,
            options = _ref$options === void 0 ? {} : _ref$options,
            effect = _ref.effect;

        if (typeof effect === 'function') {
          var cleanupFn = effect({
            state: state,
            name: name,
            instance: instance,
            options: options
          });

          var noopFn = function noopFn() {};

          effectCleanupFns.push(cleanupFn || noopFn);
        }
      });
    }

    function cleanupModifierEffects() {
      effectCleanupFns.forEach(function (fn) {
        return fn();
      });
      effectCleanupFns = [];
    }

    return instance;
  };
}

var defaultModifiers = [eventListeners, popperOffsets$1, computeStyles$1, applyStyles$1, offset$1, flip$1, preventOverflow$1, arrow$1, hide$1];
var createPopper = /*#__PURE__*/popperGenerator({
  defaultModifiers: defaultModifiers
}); // eslint-disable-next-line import/no-unused-modules

/*
 Custom Event Dispatcher
 
 Sets `target` in event data.

 https://svelte.dev/repl/c93cbf99a8ca4f44912e662a8e3cbef7?version=3.37.0

*/


function createEventDispatcher() {
	const component = get_current_component();
	return (type, target, detail) => {
		const callbacks = component.$$.callbacks[type];
		if (callbacks) {
			const event = new CustomEvent(type, { detail });
			target.dispatchEvent(event);
			callbacks.slice().forEach((fn) => {
				fn.call(component, event);
			});
		}
	};
}

/* generated by Svelte v3.59.1 */

function create_if_block_2(ctx) {
	let div;

	return {
		c() {
			div = element("div");
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", {});
			children(div).forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			/*div_binding*/ ctx[19](div);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(div);
			/*div_binding*/ ctx[19](null);
		}
	};
}

// (124:0) {#if open && triggerEl}
function create_if_block$4(ctx) {
	let frame;
	let current;

	const frame_spread_levels = [
		{ use: /*init*/ ctx[8] },
		{ options: /*triggerEl*/ ctx[3] },
		{ role: "tooltip" },
		{
			tabIndex: /*activeContent*/ ctx[1] ? -1 : undefined
		},
		/*$$restProps*/ ctx[9],
		{
			class: classNames('z-10 outline-none', /*$$props*/ ctx[10].class)
		}
	];

	let frame_props = {
		$$slots: { default: [create_default_slot$6] },
		$$scope: { ctx }
	};

	for (let i = 0; i < frame_spread_levels.length; i += 1) {
		frame_props = assign(frame_props, frame_spread_levels[i]);
	}

	frame = new Component$e({ props: frame_props });

	frame.$on("focusin", function () {
		if (is_function(optional(/*activeContent*/ ctx[1], /*showHandler*/ ctx[6]))) optional(/*activeContent*/ ctx[1], /*showHandler*/ ctx[6]).apply(this, arguments);
	});

	frame.$on("focusout", function () {
		if (is_function(optional(/*activeContent*/ ctx[1], /*hideHandler*/ ctx[7]))) optional(/*activeContent*/ ctx[1], /*hideHandler*/ ctx[7]).apply(this, arguments);
	});

	frame.$on("mouseenter", function () {
		if (is_function(optional(/*activeContent*/ ctx[1] && !/*clickable*/ ctx[4], /*showHandler*/ ctx[6]))) optional(/*activeContent*/ ctx[1] && !/*clickable*/ ctx[4], /*showHandler*/ ctx[6]).apply(this, arguments);
	});

	frame.$on("mouseleave", function () {
		if (is_function(optional(/*activeContent*/ ctx[1] && !/*clickable*/ ctx[4], /*hideHandler*/ ctx[7]))) optional(/*activeContent*/ ctx[1] && !/*clickable*/ ctx[4], /*hideHandler*/ ctx[7]).apply(this, arguments);
	});

	return {
		c() {
			create_component(frame.$$.fragment);
		},
		l(nodes) {
			claim_component(frame.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(frame, target, anchor);
			current = true;
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;

			const frame_changes = (dirty & /*init, triggerEl, activeContent, undefined, $$restProps, classNames, $$props*/ 1802)
			? get_spread_update(frame_spread_levels, [
					dirty & /*init*/ 256 && { use: /*init*/ ctx[8] },
					dirty & /*triggerEl*/ 8 && { options: /*triggerEl*/ ctx[3] },
					frame_spread_levels[2],
					dirty & /*activeContent, undefined*/ 2 && {
						tabIndex: /*activeContent*/ ctx[1] ? -1 : undefined
					},
					dirty & /*$$restProps*/ 512 && get_spread_object(/*$$restProps*/ ctx[9]),
					dirty & /*classNames, $$props*/ 1024 && {
						class: classNames('z-10 outline-none', /*$$props*/ ctx[10].class)
					}
				])
			: {};

			if (dirty & /*$$scope, arrow*/ 1048580) {
				frame_changes.$$scope = { dirty, ctx };
			}

			frame.$set(frame_changes);
		},
		i(local) {
			if (current) return;
			transition_in(frame.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(frame.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(frame, detaching);
		}
	};
}

// (137:4) {#if arrow}
function create_if_block_1$2(ctx) {
	let div;

	return {
		c() {
			div = element("div");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { "data-popper-arrow": true, class: true });
			children(div).forEach(detach);
			this.h();
		},
		h() {
			attr(div, "data-popper-arrow", "");
			attr(div, "class", "tooltip-arrow");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (125:2) <Frame     use={init}     options={triggerEl}     role="tooltip"     tabIndex={activeContent ? -1 : undefined}     on:focusin={optional(activeContent, showHandler)}     on:focusout={optional(activeContent, hideHandler)}     on:mouseenter={optional(activeContent && !clickable, showHandler)}     on:mouseleave={optional(activeContent && !clickable, hideHandler)}     {...$$restProps}     class={classNames('z-10 outline-none', $$props.class)}>
function create_default_slot$6(ctx) {
	let t;
	let if_block_anchor;
	let current;
	const default_slot_template = /*#slots*/ ctx[18].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[20], null);
	let if_block = /*arrow*/ ctx[2] && create_if_block_1$2();

	return {
		c() {
			if (default_slot) default_slot.c();
			t = space();
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
			t = claim_space(nodes);
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			insert_hydration(target, t, anchor);
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 1048576)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[20],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[20])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[20], dirty, null),
						null
					);
				}
			}

			if (/*arrow*/ ctx[2]) {
				if (if_block) ; else {
					if_block = create_if_block_1$2();
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
			if (detaching) detach(t);
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function create_fragment$c(ctx) {
	let t;
	let if_block1_anchor;
	let current;
	let if_block0 = !/*triggerEl*/ ctx[3] && create_if_block_2(ctx);
	let if_block1 = /*open*/ ctx[0] && /*triggerEl*/ ctx[3] && create_if_block$4(ctx);

	return {
		c() {
			if (if_block0) if_block0.c();
			t = space();
			if (if_block1) if_block1.c();
			if_block1_anchor = empty();
		},
		l(nodes) {
			if (if_block0) if_block0.l(nodes);
			t = claim_space(nodes);
			if (if_block1) if_block1.l(nodes);
			if_block1_anchor = empty();
		},
		m(target, anchor) {
			if (if_block0) if_block0.m(target, anchor);
			insert_hydration(target, t, anchor);
			if (if_block1) if_block1.m(target, anchor);
			insert_hydration(target, if_block1_anchor, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			if (!/*triggerEl*/ ctx[3]) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_2(ctx);
					if_block0.c();
					if_block0.m(t.parentNode, t);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (/*open*/ ctx[0] && /*triggerEl*/ ctx[3]) {
				if (if_block1) {
					if_block1.p(ctx, dirty);

					if (dirty & /*open, triggerEl*/ 9) {
						transition_in(if_block1, 1);
					}
				} else {
					if_block1 = create_if_block$4(ctx);
					if_block1.c();
					transition_in(if_block1, 1);
					if_block1.m(if_block1_anchor.parentNode, if_block1_anchor);
				}
			} else if (if_block1) {
				group_outros();

				transition_out(if_block1, 1, 1, () => {
					if_block1 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block1);
			current = true;
		},
		o(local) {
			transition_out(if_block1);
			current = false;
		},
		d(detaching) {
			if (if_block0) if_block0.d(detaching);
			if (detaching) detach(t);
			if (if_block1) if_block1.d(detaching);
			if (detaching) detach(if_block1_anchor);
		}
	};
}

function optional(pred, func) {
	return pred && func || null;
}

function instance$c($$self, $$props, $$invalidate) {
	const omit_props_names = [
		"activeContent","arrow","offset","placement","trigger","triggeredBy","strategy","open","yOnly"
	];

	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	let { activeContent = false } = $$props;
	let { arrow = true } = $$props;
	let { offset = 8 } = $$props;
	let { placement = 'top' } = $$props;
	let { trigger = 'hover' } = $$props;
	let { triggeredBy = undefined } = $$props;
	let { strategy = 'absolute' } = $$props;
	let { open = false } = $$props;
	let { yOnly = false } = $$props;
	const dispatch = createEventDispatcher();
	let clickable;
	let triggerEl;
	let contentEl;
	let triggerEls = [];
	let popper;
	let _blocked = false; // managment of the race condition between focusin and click events
	const block = () => (_blocked = true, setTimeout(() => _blocked = false, 250));

	const showHandler = ev => {
		if (triggerEl === undefined) console.error('trigger undefined');

		if (triggerEls.includes(ev.target) && triggerEl !== ev.target) {
			$$invalidate(3, triggerEl = ev.target);
			block();
		}

		if (clickable && ev.type === 'focusin' && !open) block();

		$$invalidate(0, open = clickable && ev.type === 'click' && !_blocked
		? !open
		: true);
	};

	// typescript typeguards - poper.state.element.reference: Element|HTMLElement|VirtualElement
	const hasHover = el => el.matches && el.matches(':hover');

	const hasFocus = el => el.contains && el.contains(document.activeElement);

	const hideHandler = ev => {
		if (activeContent) {
			setTimeout(
				() => {
					const elements = Object.values(popper?.state.elements ?? {});
					if (ev.type === 'mouseleave' && elements.some(hasHover)) return;
					if (ev.type === 'focusout' && elements.some(hasFocus)) return;
					$$invalidate(0, open = false);
				},
				100
			);
		} else $$invalidate(0, open = false);
	};

	function init(node, _triggerEl) {
		$$invalidate(17, popper = createPopper(_triggerEl, node, {
			placement,
			strategy,
			modifiers: [
				{
					name: 'offset',
					options: {
						offset: ({ reference, popper }) => {
							// for full screen mega menu
							return [
								yOnly
								? popper.width / 2 - reference.width / 2 - reference.x
								: 0,
								offset
							];
						}
					}
				},
				{ name: 'eventListeners', enabled: open },
				{ name: 'flip', enabled: false }
			]
		}));

		return {
			update(_triggerEl) {
				$$invalidate(17, popper.state.elements.reference = _triggerEl, popper);
				popper.update();
			},
			destroy() {
				popper.destroy();
			}
		};
	}

	onMount(() => {
		const events = [
			['focusin', showHandler, true],
			['focusout', hideHandler, true],
			['click', showHandler, clickable],
			['mouseenter', showHandler, !clickable],
			['mouseleave', hideHandler, !clickable]
		];

		if (triggeredBy) triggerEls = [...document.querySelectorAll(triggeredBy)]; else triggerEls = contentEl.previousElementSibling
		? [contentEl.previousElementSibling]
		: [];

		if (!triggerEls.length) {
			console.error('No triggers found.');
		}

		triggerEls.forEach(element => {
			if (element.tabIndex < 0) element.tabIndex = 0; // trigger must be focusable
			for (const [name, handler, cond] of events) if (cond) element.addEventListener(name, handler);
		});

		$$invalidate(3, triggerEl = triggerEls[0]);

		return () => {
			triggerEls.forEach(element => {
				if (element) {
					for (const [name, handler] of events) element.removeEventListener(name, handler);
				}
			});
		};
	});

	function div_binding($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			contentEl = $$value;
			$$invalidate(5, contentEl);
		});
	}

	$$self.$$set = $$new_props => {
		$$invalidate(10, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(9, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('activeContent' in $$new_props) $$invalidate(1, activeContent = $$new_props.activeContent);
		if ('arrow' in $$new_props) $$invalidate(2, arrow = $$new_props.arrow);
		if ('offset' in $$new_props) $$invalidate(11, offset = $$new_props.offset);
		if ('placement' in $$new_props) $$invalidate(12, placement = $$new_props.placement);
		if ('trigger' in $$new_props) $$invalidate(13, trigger = $$new_props.trigger);
		if ('triggeredBy' in $$new_props) $$invalidate(14, triggeredBy = $$new_props.triggeredBy);
		if ('strategy' in $$new_props) $$invalidate(15, strategy = $$new_props.strategy);
		if ('open' in $$new_props) $$invalidate(0, open = $$new_props.open);
		if ('yOnly' in $$new_props) $$invalidate(16, yOnly = $$new_props.yOnly);
		if ('$$scope' in $$new_props) $$invalidate(20, $$scope = $$new_props.$$scope);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*trigger*/ 8192) {
			$$invalidate(4, clickable = trigger === 'click');
		}

		if ($$self.$$.dirty & /*triggerEl, open*/ 9) {
			dispatch('show', triggerEl, open);
		}

		if ($$self.$$.dirty & /*popper, placement*/ 135168) {
			// reactivity
			popper && popper.setOptions({ placement });
		}
	};

	$$props = exclude_internal_props($$props);

	return [
		open,
		activeContent,
		arrow,
		triggerEl,
		clickable,
		contentEl,
		showHandler,
		hideHandler,
		init,
		$$restProps,
		$$props,
		offset,
		placement,
		trigger,
		triggeredBy,
		strategy,
		yOnly,
		popper,
		slots,
		div_binding,
		$$scope
	];
}

let Component$c = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$c, create_fragment$c, safe_not_equal, {
			activeContent: 1,
			arrow: 2,
			offset: 11,
			placement: 12,
			trigger: 13,
			triggeredBy: 14,
			strategy: 15,
			open: 0,
			yOnly: 16
		});
	}
};

/* generated by Svelte v3.59.1 */
const get_footer_slot_changes = dirty => ({});
const get_footer_slot_context = ctx => ({});
const get_header_slot_changes = dirty => ({});
const get_header_slot_context = ctx => ({});

// (19:2) {#if $$slots.header}
function create_if_block_1$1(ctx) {
	let div;
	let current;
	const header_slot_template = /*#slots*/ ctx[6].header;
	const header_slot = create_slot(header_slot_template, ctx, /*$$scope*/ ctx[9], get_header_slot_context);

	return {
		c() {
			div = element("div");
			if (header_slot) header_slot.c();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			if (header_slot) header_slot.l(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "py-1 overflow-hidden rounded-t");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);

			if (header_slot) {
				header_slot.m(div, null);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (header_slot) {
				if (header_slot.p && (!current || dirty & /*$$scope*/ 512)) {
					update_slot_base(
						header_slot,
						header_slot_template,
						ctx,
						/*$$scope*/ ctx[9],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[9])
						: get_slot_changes(header_slot_template, /*$$scope*/ ctx[9], dirty, get_header_slot_changes),
						get_header_slot_context
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(header_slot, local);
			current = true;
		},
		o(local) {
			transition_out(header_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			if (header_slot) header_slot.d(detaching);
		}
	};
}

// (27:2) {#if $$slots.footer}
function create_if_block$3(ctx) {
	let div;
	let current;
	const footer_slot_template = /*#slots*/ ctx[6].footer;
	const footer_slot = create_slot(footer_slot_template, ctx, /*$$scope*/ ctx[9], get_footer_slot_context);

	return {
		c() {
			div = element("div");
			if (footer_slot) footer_slot.c();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			if (footer_slot) footer_slot.l(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "py-1 overflow-hidden rounded-b");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);

			if (footer_slot) {
				footer_slot.m(div, null);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (footer_slot) {
				if (footer_slot.p && (!current || dirty & /*$$scope*/ 512)) {
					update_slot_base(
						footer_slot,
						footer_slot_template,
						ctx,
						/*$$scope*/ ctx[9],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[9])
						: get_slot_changes(footer_slot_template, /*$$scope*/ ctx[9], dirty, get_footer_slot_changes),
						get_footer_slot_context
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(footer_slot, local);
			current = true;
		},
		o(local) {
			transition_out(footer_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			if (footer_slot) footer_slot.d(detaching);
		}
	};
}

// (18:0) <Popper activeContent {...$$restProps} class={popoverClass} on:show bind:open>
function create_default_slot$5(ctx) {
	let t0;
	let ul;
	let ul_class_value;
	let t1;
	let if_block1_anchor;
	let current;
	let if_block0 = /*$$slots*/ ctx[3].header && create_if_block_1$1(ctx);
	const default_slot_template = /*#slots*/ ctx[6].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[9], null);
	let if_block1 = /*$$slots*/ ctx[3].footer && create_if_block$3(ctx);

	return {
		c() {
			if (if_block0) if_block0.c();
			t0 = space();
			ul = element("ul");
			if (default_slot) default_slot.c();
			t1 = space();
			if (if_block1) if_block1.c();
			if_block1_anchor = empty();
			this.h();
		},
		l(nodes) {
			if (if_block0) if_block0.l(nodes);
			t0 = claim_space(nodes);
			ul = claim_element(nodes, "UL", { class: true });
			var ul_nodes = children(ul);
			if (default_slot) default_slot.l(ul_nodes);
			ul_nodes.forEach(detach);
			t1 = claim_space(nodes);
			if (if_block1) if_block1.l(nodes);
			if_block1_anchor = empty();
			this.h();
		},
		h() {
			attr(ul, "class", ul_class_value = /*$$props*/ ctx[4].class ?? 'py-1 w-44');
		},
		m(target, anchor) {
			if (if_block0) if_block0.m(target, anchor);
			insert_hydration(target, t0, anchor);
			insert_hydration(target, ul, anchor);

			if (default_slot) {
				default_slot.m(ul, null);
			}

			insert_hydration(target, t1, anchor);
			if (if_block1) if_block1.m(target, anchor);
			insert_hydration(target, if_block1_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			if (/*$$slots*/ ctx[3].header) {
				if (if_block0) {
					if_block0.p(ctx, dirty);

					if (dirty & /*$$slots*/ 8) {
						transition_in(if_block0, 1);
					}
				} else {
					if_block0 = create_if_block_1$1(ctx);
					if_block0.c();
					transition_in(if_block0, 1);
					if_block0.m(t0.parentNode, t0);
				}
			} else if (if_block0) {
				group_outros();

				transition_out(if_block0, 1, 1, () => {
					if_block0 = null;
				});

				check_outros();
			}

			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 512)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[9],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[9])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[9], dirty, null),
						null
					);
				}
			}

			if (!current || dirty & /*$$props*/ 16 && ul_class_value !== (ul_class_value = /*$$props*/ ctx[4].class ?? 'py-1 w-44')) {
				attr(ul, "class", ul_class_value);
			}

			if (/*$$slots*/ ctx[3].footer) {
				if (if_block1) {
					if_block1.p(ctx, dirty);

					if (dirty & /*$$slots*/ 8) {
						transition_in(if_block1, 1);
					}
				} else {
					if_block1 = create_if_block$3(ctx);
					if_block1.c();
					transition_in(if_block1, 1);
					if_block1.m(if_block1_anchor.parentNode, if_block1_anchor);
				}
			} else if (if_block1) {
				group_outros();

				transition_out(if_block1, 1, 1, () => {
					if_block1 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block0);
			transition_in(default_slot, local);
			transition_in(if_block1);
			current = true;
		},
		o(local) {
			transition_out(if_block0);
			transition_out(default_slot, local);
			transition_out(if_block1);
			current = false;
		},
		d(detaching) {
			if (if_block0) if_block0.d(detaching);
			if (detaching) detach(t0);
			if (detaching) detach(ul);
			if (default_slot) default_slot.d(detaching);
			if (detaching) detach(t1);
			if (if_block1) if_block1.d(detaching);
			if (detaching) detach(if_block1_anchor);
		}
	};
}

function create_fragment$b(ctx) {
	let popper;
	let updating_open;
	let current;

	const popper_spread_levels = [
		{ activeContent: true },
		/*$$restProps*/ ctx[2],
		{ class: /*popoverClass*/ ctx[1] }
	];

	function popper_open_binding(value) {
		/*popper_open_binding*/ ctx[7](value);
	}

	let popper_props = {
		$$slots: { default: [create_default_slot$5] },
		$$scope: { ctx }
	};

	for (let i = 0; i < popper_spread_levels.length; i += 1) {
		popper_props = assign(popper_props, popper_spread_levels[i]);
	}

	if (/*open*/ ctx[0] !== void 0) {
		popper_props.open = /*open*/ ctx[0];
	}

	popper = new Component$c({ props: popper_props });
	binding_callbacks.push(() => bind(popper, 'open', popper_open_binding));
	popper.$on("show", /*show_handler*/ ctx[8]);

	return {
		c() {
			create_component(popper.$$.fragment);
		},
		l(nodes) {
			claim_component(popper.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(popper, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const popper_changes = (dirty & /*$$restProps, popoverClass*/ 6)
			? get_spread_update(popper_spread_levels, [
					popper_spread_levels[0],
					dirty & /*$$restProps*/ 4 && get_spread_object(/*$$restProps*/ ctx[2]),
					dirty & /*popoverClass*/ 2 && { class: /*popoverClass*/ ctx[1] }
				])
			: {};

			if (dirty & /*$$scope, $$slots, $$props*/ 536) {
				popper_changes.$$scope = { dirty, ctx };
			}

			if (!updating_open && dirty & /*open*/ 1) {
				updating_open = true;
				popper_changes.open = /*open*/ ctx[0];
				add_flush_callback(() => updating_open = false);
			}

			popper.$set(popper_changes);
		},
		i(local) {
			if (current) return;
			transition_in(popper.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(popper.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(popper, detaching);
		}
	};
}

function instance$b($$self, $$props, $$invalidate) {
	const omit_props_names = ["open","frameClass"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	const $$slots = compute_slots(slots);
	let { open = false } = $$props;
	let { frameClass = '' } = $$props;
	let popoverClass;

	function popper_open_binding(value) {
		open = value;
		$$invalidate(0, open);
	}

	function show_handler(event) {
		bubble.call(this, $$self, event);
	}

	$$self.$$set = $$new_props => {
		$$invalidate(4, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(2, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('open' in $$new_props) $$invalidate(0, open = $$new_props.open);
		if ('frameClass' in $$new_props) $$invalidate(5, frameClass = $$new_props.frameClass);
		if ('$$scope' in $$new_props) $$invalidate(9, $$scope = $$new_props.$$scope);
	};

	$$self.$$.update = () => {
		{
			// set default values
			$$invalidate(2, $$restProps.arrow = $$restProps.arrow ?? false, $$restProps);

			$$invalidate(2, $$restProps.trigger = $$restProps.trigger ?? 'click', $$restProps);
			$$invalidate(2, $$restProps.placement = $$restProps.placement ?? 'bottom', $$restProps);
			$$invalidate(2, $$restProps.color = $$restProps.color ?? 'dropdown', $$restProps);
			$$invalidate(2, $$restProps.shadow = $$restProps.shadow ?? true, $$restProps);
			$$invalidate(2, $$restProps.rounded = $$restProps.rounded ?? true, $$restProps);
		}

		if ($$self.$$.dirty & /*frameClass*/ 32) {
			$$invalidate(1, popoverClass = classNames('divide-y divide-gray-100 dark:divide-gray-600', frameClass));
		}
	};

	$$props = exclude_internal_props($$props);

	return [
		open,
		popoverClass,
		$$restProps,
		$$slots,
		$$props,
		frameClass,
		slots,
		popper_open_binding,
		show_handler,
		$$scope
	];
}

let Component$b = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$b, create_fragment$b, safe_not_equal, { open: 0, frameClass: 5 });
	}
};

/* generated by Svelte v3.59.1 */

function create_fragment$a(ctx) {
	let div;
	let div_class_value;

	let div_levels = [
		/*$$restProps*/ ctx[1],
		{
			class: div_class_value = classNames(/*divClass*/ ctx[0], /*$$props*/ ctx[2].class)
		}
	];

	let div_data = {};

	for (let i = 0; i < div_levels.length; i += 1) {
		div_data = assign(div_data, div_levels[i]);
	}

	return {
		c() {
			div = element("div");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			children(div).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(div, div_data);
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
		},
		p(ctx, [dirty]) {
			set_attributes(div, div_data = get_spread_update(div_levels, [
				dirty & /*$$restProps*/ 2 && /*$$restProps*/ ctx[1],
				dirty & /*divClass, $$props*/ 5 && div_class_value !== (div_class_value = classNames(/*divClass*/ ctx[0], /*$$props*/ ctx[2].class)) && { class: div_class_value }
			]));
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function instance$a($$self, $$props, $$invalidate) {
	const omit_props_names = ["divClass"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { divClass = 'my-1 h-px bg-gray-100 dark:bg-gray-600' } = $$props;

	$$self.$$set = $$new_props => {
		$$invalidate(2, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(1, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('divClass' in $$new_props) $$invalidate(0, divClass = $$new_props.divClass);
	};

	$$props = exclude_internal_props($$props);
	return [divClass, $$restProps, $$props];
}

let Component$a = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$a, create_fragment$a, safe_not_equal, { divClass: 0 });
	}
};

/* generated by Svelte v3.59.1 */

function create_else_block$2(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[5].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[4], null);

	return {
		c() {
			if (default_slot) default_slot.c();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 16)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[4],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[4])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[4], dirty, null),
						null
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
		}
	};
}

// (6:0) {#if show}
function create_if_block$2(ctx) {
	let previous_tag = /*tag*/ ctx[0];
	let svelte_element_anchor;
	let current;
	let svelte_element = /*tag*/ ctx[0] && create_dynamic_element$2(ctx);

	return {
		c() {
			if (svelte_element) svelte_element.c();
			svelte_element_anchor = empty();
		},
		l(nodes) {
			if (svelte_element) svelte_element.l(nodes);
			svelte_element_anchor = empty();
		},
		m(target, anchor) {
			if (svelte_element) svelte_element.m(target, anchor);
			insert_hydration(target, svelte_element_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			if (/*tag*/ ctx[0]) {
				if (!previous_tag) {
					svelte_element = create_dynamic_element$2(ctx);
					previous_tag = /*tag*/ ctx[0];
					svelte_element.c();
					svelte_element.m(svelte_element_anchor.parentNode, svelte_element_anchor);
				} else if (safe_not_equal(previous_tag, /*tag*/ ctx[0])) {
					svelte_element.d(1);
					svelte_element = create_dynamic_element$2(ctx);
					previous_tag = /*tag*/ ctx[0];
					svelte_element.c();
					svelte_element.m(svelte_element_anchor.parentNode, svelte_element_anchor);
				} else {
					svelte_element.p(ctx, dirty);
				}
			} else if (previous_tag) {
				svelte_element.d(1);
				svelte_element = null;
				previous_tag = /*tag*/ ctx[0];
			}
		},
		i(local) {
			if (current) return;
			transition_in(svelte_element);
			current = true;
		},
		o(local) {
			transition_out(svelte_element);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(svelte_element_anchor);
			if (svelte_element) svelte_element.d(detaching);
		}
	};
}

// (7:2) <svelte:element this={tag} use:use {...$$restProps}>
function create_dynamic_element$2(ctx) {
	let svelte_element;
	let current;
	let mounted;
	let dispose;
	const default_slot_template = /*#slots*/ ctx[5].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[4], null);
	let svelte_element_levels = [/*$$restProps*/ ctx[3]];
	let svelte_element_data = {};

	for (let i = 0; i < svelte_element_levels.length; i += 1) {
		svelte_element_data = assign(svelte_element_data, svelte_element_levels[i]);
	}

	return {
		c() {
			svelte_element = element(/*tag*/ ctx[0]);
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			svelte_element = claim_element(nodes, (/*tag*/ ctx[0] || 'null').toUpperCase(), {});
			var svelte_element_nodes = children(svelte_element);
			if (default_slot) default_slot.l(svelte_element_nodes);
			svelte_element_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_dynamic_element_data(/*tag*/ ctx[0])(svelte_element, svelte_element_data);
		},
		m(target, anchor) {
			insert_hydration(target, svelte_element, anchor);

			if (default_slot) {
				default_slot.m(svelte_element, null);
			}

			current = true;

			if (!mounted) {
				dispose = action_destroyer(/*use*/ ctx[2].call(null, svelte_element));
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 16)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[4],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[4])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[4], dirty, null),
						null
					);
				}
			}

			set_dynamic_element_data(/*tag*/ ctx[0])(svelte_element, svelte_element_data = get_spread_update(svelte_element_levels, [dirty & /*$$restProps*/ 8 && /*$$restProps*/ ctx[3]]));
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(svelte_element);
			if (default_slot) default_slot.d(detaching);
			mounted = false;
			dispose();
		}
	};
}

function create_fragment$9(ctx) {
	let current_block_type_index;
	let if_block;
	let if_block_anchor;
	let current;
	const if_block_creators = [create_if_block$2, create_else_block$2];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*show*/ ctx[1]) return 0;
		return 1;
	}

	current_block_type_index = select_block_type(ctx);
	if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_blocks[current_block_type_index].m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if_blocks[current_block_type_index].p(ctx, dirty);
			} else {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block = if_blocks[current_block_type_index];

				if (!if_block) {
					if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block.c();
				} else {
					if_block.p(ctx, dirty);
				}

				transition_in(if_block, 1);
				if_block.m(if_block_anchor.parentNode, if_block_anchor);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if_blocks[current_block_type_index].d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$9($$self, $$props, $$invalidate) {
	const omit_props_names = ["tag","show","use"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	let { tag = 'div' } = $$props;
	let { show } = $$props;

	let { use = () => {
		
	} } = $$props;

	$$self.$$set = $$new_props => {
		$$props = assign(assign({}, $$props), exclude_internal_props($$new_props));
		$$invalidate(3, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('tag' in $$new_props) $$invalidate(0, tag = $$new_props.tag);
		if ('show' in $$new_props) $$invalidate(1, show = $$new_props.show);
		if ('use' in $$new_props) $$invalidate(2, use = $$new_props.use);
		if ('$$scope' in $$new_props) $$invalidate(4, $$scope = $$new_props.$$scope);
	};

	return [tag, show, use, $$restProps, $$scope, slots];
}

let Component$9 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$9, create_fragment$9, safe_not_equal, { tag: 0, show: 1, use: 2 });
	}
};

/* generated by Svelte v3.59.1 */

function create_dynamic_element$1(ctx) {
	let svelte_element;
	let svelte_element_type_value;
	let current;
	let mounted;
	let dispose;
	const default_slot_template = /*#slots*/ ctx[6].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[15], null);

	let svelte_element_levels = [
		{ href: /*href*/ ctx[0] },
		{
			type: svelte_element_type_value = /*href*/ ctx[0] ? undefined : 'button'
		},
		/*$$restProps*/ ctx[4],
		{ class: /*liClass*/ ctx[1] }
	];

	let svelte_element_data = {};

	for (let i = 0; i < svelte_element_levels.length; i += 1) {
		svelte_element_data = assign(svelte_element_data, svelte_element_levels[i]);
	}

	return {
		c() {
			svelte_element = element(/*href*/ ctx[0] ? 'a' : 'button');
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			svelte_element = claim_element(nodes, ((/*href*/ ctx[0] ? 'a' : 'button') || 'null').toUpperCase(), { href: true, type: true, class: true });
			var svelte_element_nodes = children(svelte_element);
			if (default_slot) default_slot.l(svelte_element_nodes);
			svelte_element_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_dynamic_element_data(/*href*/ ctx[0] ? 'a' : 'button')(svelte_element, svelte_element_data);
		},
		m(target, anchor) {
			insert_hydration(target, svelte_element, anchor);

			if (default_slot) {
				default_slot.m(svelte_element, null);
			}

			current = true;

			if (!mounted) {
				dispose = [
					listen(svelte_element, "click", /*click_handler*/ ctx[7]),
					listen(svelte_element, "change", /*change_handler*/ ctx[8]),
					listen(svelte_element, "keydown", /*keydown_handler*/ ctx[9]),
					listen(svelte_element, "keyup", /*keyup_handler*/ ctx[10]),
					listen(svelte_element, "focus", /*focus_handler*/ ctx[11]),
					listen(svelte_element, "blur", /*blur_handler*/ ctx[12]),
					listen(svelte_element, "mouseenter", /*mouseenter_handler*/ ctx[13]),
					listen(svelte_element, "mouseleave", /*mouseleave_handler*/ ctx[14])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 32768)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[15],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[15])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[15], dirty, null),
						null
					);
				}
			}

			set_dynamic_element_data(/*href*/ ctx[0] ? 'a' : 'button')(svelte_element, svelte_element_data = get_spread_update(svelte_element_levels, [
				(!current || dirty & /*href*/ 1) && { href: /*href*/ ctx[0] },
				(!current || dirty & /*href*/ 1 && svelte_element_type_value !== (svelte_element_type_value = /*href*/ ctx[0] ? undefined : 'button')) && { type: svelte_element_type_value },
				dirty & /*$$restProps*/ 16 && /*$$restProps*/ ctx[4],
				(!current || dirty & /*liClass*/ 2) && { class: /*liClass*/ ctx[1] }
			]));
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(svelte_element);
			if (default_slot) default_slot.d(detaching);
			mounted = false;
			run_all(dispose);
		}
	};
}

// (13:0) <Wrapper tag="li" show={wrap} use={init}>
function create_default_slot$4(ctx) {
	let previous_tag = /*href*/ ctx[0] ? 'a' : 'button';
	let svelte_element_anchor;
	let current;
	let svelte_element = (/*href*/ ctx[0] ? 'a' : 'button') && create_dynamic_element$1(ctx);

	return {
		c() {
			if (svelte_element) svelte_element.c();
			svelte_element_anchor = empty();
		},
		l(nodes) {
			if (svelte_element) svelte_element.l(nodes);
			svelte_element_anchor = empty();
		},
		m(target, anchor) {
			if (svelte_element) svelte_element.m(target, anchor);
			insert_hydration(target, svelte_element_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			if (/*href*/ ctx[0] ? 'a' : 'button') {
				if (!previous_tag) {
					svelte_element = create_dynamic_element$1(ctx);
					previous_tag = /*href*/ ctx[0] ? 'a' : 'button';
					svelte_element.c();
					svelte_element.m(svelte_element_anchor.parentNode, svelte_element_anchor);
				} else if (safe_not_equal(previous_tag, /*href*/ ctx[0] ? 'a' : 'button')) {
					svelte_element.d(1);
					svelte_element = create_dynamic_element$1(ctx);
					previous_tag = /*href*/ ctx[0] ? 'a' : 'button';
					svelte_element.c();
					svelte_element.m(svelte_element_anchor.parentNode, svelte_element_anchor);
				} else {
					svelte_element.p(ctx, dirty);
				}
			} else if (previous_tag) {
				svelte_element.d(1);
				svelte_element = null;
				previous_tag = /*href*/ ctx[0] ? 'a' : 'button';
			}
		},
		i(local) {
			if (current) return;
			transition_in(svelte_element);
			current = true;
		},
		o(local) {
			transition_out(svelte_element);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(svelte_element_anchor);
			if (svelte_element) svelte_element.d(detaching);
		}
	};
}

function create_fragment$8(ctx) {
	let wrapper;
	let current;

	wrapper = new Component$9({
			props: {
				tag: "li",
				show: /*wrap*/ ctx[2],
				use: /*init*/ ctx[3],
				$$slots: { default: [create_default_slot$4] },
				$$scope: { ctx }
			}
		});

	return {
		c() {
			create_component(wrapper.$$.fragment);
		},
		l(nodes) {
			claim_component(wrapper.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(wrapper, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const wrapper_changes = {};
			if (dirty & /*wrap*/ 4) wrapper_changes.show = /*wrap*/ ctx[2];

			if (dirty & /*$$scope, href, $$restProps, liClass*/ 32787) {
				wrapper_changes.$$scope = { dirty, ctx };
			}

			wrapper.$set(wrapper_changes);
		},
		i(local) {
			if (current) return;
			transition_in(wrapper.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(wrapper.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(wrapper, detaching);
		}
	};
}

function instance$8($$self, $$props, $$invalidate) {
	const omit_props_names = ["defaultClass","href"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	let { defaultClass = 'font-medium py-2 px-4 text-sm hover:bg-gray-100 dark:hover:bg-gray-600' } = $$props;
	let { href = undefined } = $$props;
	let liClass;
	let wrap = true;

	function init(node) {
		$$invalidate(2, wrap = node.parentElement?.tagName === 'UL');
	}

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	function change_handler(event) {
		bubble.call(this, $$self, event);
	}

	function keydown_handler(event) {
		bubble.call(this, $$self, event);
	}

	function keyup_handler(event) {
		bubble.call(this, $$self, event);
	}

	function focus_handler(event) {
		bubble.call(this, $$self, event);
	}

	function blur_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler(event) {
		bubble.call(this, $$self, event);
	}

	$$self.$$set = $$new_props => {
		$$invalidate(16, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(4, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('defaultClass' in $$new_props) $$invalidate(5, defaultClass = $$new_props.defaultClass);
		if ('href' in $$new_props) $$invalidate(0, href = $$new_props.href);
		if ('$$scope' in $$new_props) $$invalidate(15, $$scope = $$new_props.$$scope);
	};

	$$self.$$.update = () => {
		$$invalidate(1, liClass = classNames(defaultClass, href ? 'block' : 'w-full text-left', $$props.class));
	};

	$$props = exclude_internal_props($$props);

	return [
		href,
		liClass,
		wrap,
		init,
		$$restProps,
		defaultClass,
		slots,
		click_handler,
		change_handler,
		keydown_handler,
		keyup_handler,
		focus_handler,
		blur_handler,
		mouseenter_handler,
		mouseleave_handler,
		$$scope
	];
}

let Component$8 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$8, create_fragment$8, safe_not_equal, { defaultClass: 5, href: 0 });
	}
};

/* generated by Svelte v3.59.1 */
const get_default_slot_changes = dirty => ({ hidden: dirty & /*hidden*/ 16 });

const get_default_slot_context = ctx => ({
	hidden: /*hidden*/ ctx[4],
	toggle: /*toggle*/ ctx[5]
});

// (13:0) <Frame tag="nav" {color} {...$$restProps} class={classNames(navClass, $$props.class)}>
function create_default_slot$3(ctx) {
	let div;
	let div_class_value;
	let current;
	const default_slot_template = /*#slots*/ ctx[8].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[9], get_default_slot_context);

	return {
		c() {
			div = element("div");
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			if (default_slot) default_slot.l(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", div_class_value = classNames(/*navDivClass*/ ctx[1], /*fluid*/ ctx[2] || 'container'));
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);

			if (default_slot) {
				default_slot.m(div, null);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope, hidden*/ 528)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[9],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[9])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[9], dirty, get_default_slot_changes),
						get_default_slot_context
					);
				}
			}

			if (!current || dirty & /*navDivClass, fluid*/ 6 && div_class_value !== (div_class_value = classNames(/*navDivClass*/ ctx[1], /*fluid*/ ctx[2] || 'container'))) {
				attr(div, "class", div_class_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function create_fragment$7(ctx) {
	let frame;
	let current;

	const frame_spread_levels = [
		{ tag: "nav" },
		{ color: /*color*/ ctx[3] },
		/*$$restProps*/ ctx[6],
		{
			class: classNames(/*navClass*/ ctx[0], /*$$props*/ ctx[7].class)
		}
	];

	let frame_props = {
		$$slots: { default: [create_default_slot$3] },
		$$scope: { ctx }
	};

	for (let i = 0; i < frame_spread_levels.length; i += 1) {
		frame_props = assign(frame_props, frame_spread_levels[i]);
	}

	frame = new Component$e({ props: frame_props });

	return {
		c() {
			create_component(frame.$$.fragment);
		},
		l(nodes) {
			claim_component(frame.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(frame, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const frame_changes = (dirty & /*color, $$restProps, classNames, navClass, $$props*/ 201)
			? get_spread_update(frame_spread_levels, [
					frame_spread_levels[0],
					dirty & /*color*/ 8 && { color: /*color*/ ctx[3] },
					dirty & /*$$restProps*/ 64 && get_spread_object(/*$$restProps*/ ctx[6]),
					dirty & /*classNames, navClass, $$props*/ 129 && {
						class: classNames(/*navClass*/ ctx[0], /*$$props*/ ctx[7].class)
					}
				])
			: {};

			if (dirty & /*$$scope, navDivClass, fluid, hidden*/ 534) {
				frame_changes.$$scope = { dirty, ctx };
			}

			frame.$set(frame_changes);
		},
		i(local) {
			if (current) return;
			transition_in(frame.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(frame.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(frame, detaching);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	const omit_props_names = ["navClass","navDivClass","fluid","color"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	let { navClass = 'px-2 sm:px-4 py-2.5 w-full' } = $$props;
	let { navDivClass = 'mx-auto flex flex-wrap justify-between items-center ' } = $$props;
	let { fluid = false } = $$props;
	let { color = 'navbar' } = $$props;
	let hidden = true;

	let toggle = () => {
		$$invalidate(4, hidden = !hidden);
	};

	$$self.$$set = $$new_props => {
		$$invalidate(7, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(6, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('navClass' in $$new_props) $$invalidate(0, navClass = $$new_props.navClass);
		if ('navDivClass' in $$new_props) $$invalidate(1, navDivClass = $$new_props.navDivClass);
		if ('fluid' in $$new_props) $$invalidate(2, fluid = $$new_props.fluid);
		if ('color' in $$new_props) $$invalidate(3, color = $$new_props.color);
		if ('$$scope' in $$new_props) $$invalidate(9, $$scope = $$new_props.$$scope);
	};

	$$props = exclude_internal_props($$props);

	return [
		navClass,
		navDivClass,
		fluid,
		color,
		hidden,
		toggle,
		$$restProps,
		$$props,
		slots,
		$$scope
	];
}

let Component$7 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$7, safe_not_equal, {
			navClass: 0,
			navDivClass: 1,
			fluid: 2,
			color: 3
		});
	}
};

/* generated by Svelte v3.59.1 */

function create_fragment$6(ctx) {
	let a;
	let a_class_value;
	let current;
	const default_slot_template = /*#slots*/ ctx[4].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[3], null);

	let a_levels = [
		{ href: /*href*/ ctx[0] },
		/*$$restProps*/ ctx[1],
		{
			class: a_class_value = classNames('flex items-center', /*$$props*/ ctx[2].class)
		}
	];

	let a_data = {};

	for (let i = 0; i < a_levels.length; i += 1) {
		a_data = assign(a_data, a_levels[i]);
	}

	return {
		c() {
			a = element("a");
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			if (default_slot) default_slot.l(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_attributes(a, a_data);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);

			if (default_slot) {
				default_slot.m(a, null);
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 8)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[3],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[3])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[3], dirty, null),
						null
					);
				}
			}

			set_attributes(a, a_data = get_spread_update(a_levels, [
				(!current || dirty & /*href*/ 1) && { href: /*href*/ ctx[0] },
				dirty & /*$$restProps*/ 2 && /*$$restProps*/ ctx[1],
				(!current || dirty & /*$$props*/ 4 && a_class_value !== (a_class_value = classNames('flex items-center', /*$$props*/ ctx[2].class))) && { class: a_class_value }
			]));
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	const omit_props_names = ["href"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	let { href = '' } = $$props;

	$$self.$$set = $$new_props => {
		$$invalidate(2, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(1, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('href' in $$new_props) $$invalidate(0, href = $$new_props.href);
		if ('$$scope' in $$new_props) $$invalidate(3, $$scope = $$new_props.$$scope);
	};

	$$props = exclude_internal_props($$props);
	return [href, $$restProps, $$props, $$scope, slots];
}

let Component$6 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$6, create_fragment$6, safe_not_equal, { href: 0 });
	}
};

/* generated by Svelte v3.59.1 */

function create_fragment$5(ctx) {
	let svg;
	let svg_class_value;
	let mounted;
	let dispose;

	let svg_levels = [
		{ xmlns: "http://www.w3.org/2000/svg" },
		{ width: /*size*/ ctx[0] },
		{ height: /*size*/ ctx[0] },
		{
			class: svg_class_value = /*$$props*/ ctx[4].class
		},
		/*$$restProps*/ ctx[5],
		{ "aria-label": /*ariaLabel*/ ctx[1] },
		{ fill: "none" },
		{ viewBox: /*viewBox*/ ctx[2] },
		{ "stroke-width": "2" }
	];

	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {
				xmlns: true,
				width: true,
				height: true,
				class: true,
				"aria-label": true,
				fill: true,
				viewBox: true,
				"stroke-width": true
			});

			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = /*svgpath*/ ctx[3];

			if (!mounted) {
				dispose = listen(svg, "click", /*click_handler*/ ctx[8]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*svgpath*/ 8) svg.innerHTML = /*svgpath*/ ctx[3];
			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [
				{ xmlns: "http://www.w3.org/2000/svg" },
				dirty & /*size*/ 1 && { width: /*size*/ ctx[0] },
				dirty & /*size*/ 1 && { height: /*size*/ ctx[0] },
				dirty & /*$$props*/ 16 && svg_class_value !== (svg_class_value = /*$$props*/ ctx[4].class) && { class: svg_class_value },
				dirty & /*$$restProps*/ 32 && /*$$restProps*/ ctx[5],
				dirty & /*ariaLabel*/ 2 && { "aria-label": /*ariaLabel*/ ctx[1] },
				{ fill: "none" },
				dirty & /*viewBox*/ 4 && { viewBox: /*viewBox*/ ctx[2] },
				{ "stroke-width": "2" }
			]));
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(svg);
			mounted = false;
			dispose();
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	const omit_props_names = ["size","color","variation","ariaLabel"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { size = '24' } = $$props;
	let { color = 'currentColor' } = $$props;
	let { variation = 'outline' } = $$props;
	let viewBox;
	let svgpath;
	let svgoutline = `<path d="M3.75 6.75H20.25M3.75 12H20.25M3.75 17.25H20.25" stroke="${color}" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/> `;
	let svgsolid = `<path fill-rule="evenodd" clip-rule="evenodd" d="M3 6.75C3 6.33579 3.33579 6 3.75 6H20.25C20.6642 6 21 6.33579 21 6.75C21 7.16421 20.6642 7.5 20.25 7.5H3.75C3.33579 7.5 3 7.16421 3 6.75ZM3 12C3 11.5858 3.33579 11.25 3.75 11.25H20.25C20.6642 11.25 21 11.5858 21 12C21 12.4142 20.6642 12.75 20.25 12.75H3.75C3.33579 12.75 3 12.4142 3 12ZM3 17.25C3 16.8358 3.33579 16.5 3.75 16.5H20.25C20.6642 16.5 21 16.8358 21 17.25C21 17.6642 20.6642 18 20.25 18H3.75C3.33579 18 3 17.6642 3 17.25Z" fill="${color}"/> `;
	let { ariaLabel = 'bars 3' } = $$props;

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	$$self.$$set = $$new_props => {
		$$invalidate(4, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(5, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('size' in $$new_props) $$invalidate(0, size = $$new_props.size);
		if ('color' in $$new_props) $$invalidate(6, color = $$new_props.color);
		if ('variation' in $$new_props) $$invalidate(7, variation = $$new_props.variation);
		if ('ariaLabel' in $$new_props) $$invalidate(1, ariaLabel = $$new_props.ariaLabel);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*variation*/ 128) {
			switch (variation) {
				case 'outline':
					$$invalidate(3, svgpath = svgoutline);
					$$invalidate(2, viewBox = '0 0 24 24');
					break;
				case 'solid':
					$$invalidate(3, svgpath = svgsolid);
					$$invalidate(2, viewBox = '0 0 24 24');
					break;
				default:
					$$invalidate(3, svgpath = svgoutline);
					$$invalidate(2, viewBox = '0 0 24 24');
			}
		}
	};

	$$props = exclude_internal_props($$props);

	return [
		size,
		ariaLabel,
		viewBox,
		svgpath,
		$$props,
		$$restProps,
		color,
		variation,
		click_handler
	];
}

let Component$5 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			size: 0,
			color: 6,
			variation: 7,
			ariaLabel: 1
		});
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot$2(ctx) {
	let menu;
	let current;
	menu = new Component$5({ props: { class: "h-6 w-6 shrink-0" } });

	return {
		c() {
			create_component(menu.$$.fragment);
		},
		l(nodes) {
			claim_component(menu.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(menu, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(menu.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(menu.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(menu, detaching);
		}
	};
}

function create_fragment$4(ctx) {
	let toolbarbutton;
	let current;

	const toolbarbutton_spread_levels = [
		{ name: "Open main menu" },
		/*$$restProps*/ ctx[1],
		{
			class: classNames(/*btnClass*/ ctx[0], /*$$props*/ ctx[2].class)
		}
	];

	let toolbarbutton_props = {
		$$slots: { default: [create_default_slot$2] },
		$$scope: { ctx }
	};

	for (let i = 0; i < toolbarbutton_spread_levels.length; i += 1) {
		toolbarbutton_props = assign(toolbarbutton_props, toolbarbutton_spread_levels[i]);
	}

	toolbarbutton = new Component$d({ props: toolbarbutton_props });
	toolbarbutton.$on("click", /*click_handler*/ ctx[3]);

	return {
		c() {
			create_component(toolbarbutton.$$.fragment);
		},
		l(nodes) {
			claim_component(toolbarbutton.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(toolbarbutton, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const toolbarbutton_changes = (dirty & /*$$restProps, classNames, btnClass, $$props*/ 7)
			? get_spread_update(toolbarbutton_spread_levels, [
					toolbarbutton_spread_levels[0],
					dirty & /*$$restProps*/ 2 && get_spread_object(/*$$restProps*/ ctx[1]),
					dirty & /*classNames, btnClass, $$props*/ 5 && {
						class: classNames(/*btnClass*/ ctx[0], /*$$props*/ ctx[2].class)
					}
				])
			: {};

			if (dirty & /*$$scope*/ 16) {
				toolbarbutton_changes.$$scope = { dirty, ctx };
			}

			toolbarbutton.$set(toolbarbutton_changes);
		},
		i(local) {
			if (current) return;
			transition_in(toolbarbutton.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(toolbarbutton.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(toolbarbutton, detaching);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	const omit_props_names = ["btnClass"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { btnClass = 'ml-3 md:hidden' } = $$props;

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	$$self.$$set = $$new_props => {
		$$invalidate(2, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(1, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('btnClass' in $$new_props) $$invalidate(0, btnClass = $$new_props.btnClass);
	};

	$$props = exclude_internal_props($$props);
	return [btnClass, $$restProps, $$props, click_handler];
}

let Component$4 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$4, create_fragment$4, safe_not_equal, { btnClass: 0 });
	}
};

/* generated by Svelte v3.59.1 */

function create_dynamic_element(ctx) {
	let svelte_element;
	let current;
	let mounted;
	let dispose;
	const default_slot_template = /*#slots*/ ctx[7].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[6], null);

	let svelte_element_levels = [
		{ href: /*href*/ ctx[0] },
		/*$$restProps*/ ctx[2],
		{ class: /*liClass*/ ctx[1] }
	];

	let svelte_element_data = {};

	for (let i = 0; i < svelte_element_levels.length; i += 1) {
		svelte_element_data = assign(svelte_element_data, svelte_element_levels[i]);
	}

	return {
		c() {
			svelte_element = element(/*href*/ ctx[0] ? 'a' : 'div');
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			svelte_element = claim_element(nodes, ((/*href*/ ctx[0] ? 'a' : 'div') || 'null').toUpperCase(), { href: true, class: true });
			var svelte_element_nodes = children(svelte_element);
			if (default_slot) default_slot.l(svelte_element_nodes);
			svelte_element_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_dynamic_element_data(/*href*/ ctx[0] ? 'a' : 'div')(svelte_element, svelte_element_data);
		},
		m(target, anchor) {
			insert_hydration(target, svelte_element, anchor);

			if (default_slot) {
				default_slot.m(svelte_element, null);
			}

			current = true;

			if (!mounted) {
				dispose = [
					listen(svelte_element, "blur", /*blur_handler*/ ctx[8]),
					listen(svelte_element, "change", /*change_handler*/ ctx[9]),
					listen(svelte_element, "click", /*click_handler*/ ctx[10]),
					listen(svelte_element, "focus", /*focus_handler*/ ctx[11]),
					listen(svelte_element, "keydown", /*keydown_handler*/ ctx[12]),
					listen(svelte_element, "keypress", /*keypress_handler*/ ctx[13]),
					listen(svelte_element, "keyup", /*keyup_handler*/ ctx[14]),
					listen(svelte_element, "mouseenter", /*mouseenter_handler*/ ctx[15]),
					listen(svelte_element, "mouseleave", /*mouseleave_handler*/ ctx[16]),
					listen(svelte_element, "mouseover", /*mouseover_handler*/ ctx[17])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 64)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[6],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[6])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[6], dirty, null),
						null
					);
				}
			}

			set_dynamic_element_data(/*href*/ ctx[0] ? 'a' : 'div')(svelte_element, svelte_element_data = get_spread_update(svelte_element_levels, [
				(!current || dirty & /*href*/ 1) && { href: /*href*/ ctx[0] },
				dirty & /*$$restProps*/ 4 && /*$$restProps*/ ctx[2],
				(!current || dirty & /*liClass*/ 2) && { class: /*liClass*/ ctx[1] }
			]));
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(svelte_element);
			if (default_slot) default_slot.d(detaching);
			mounted = false;
			run_all(dispose);
		}
	};
}

function create_fragment$3(ctx) {
	let li;
	let previous_tag = /*href*/ ctx[0] ? 'a' : 'div';
	let current;
	let svelte_element = (/*href*/ ctx[0] ? 'a' : 'div') && create_dynamic_element(ctx);

	return {
		c() {
			li = element("li");
			if (svelte_element) svelte_element.c();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", {});
			var li_nodes = children(li);
			if (svelte_element) svelte_element.l(li_nodes);
			li_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			if (svelte_element) svelte_element.m(li, null);
			current = true;
		},
		p(ctx, [dirty]) {
			if (/*href*/ ctx[0] ? 'a' : 'div') {
				if (!previous_tag) {
					svelte_element = create_dynamic_element(ctx);
					previous_tag = /*href*/ ctx[0] ? 'a' : 'div';
					svelte_element.c();
					svelte_element.m(li, null);
				} else if (safe_not_equal(previous_tag, /*href*/ ctx[0] ? 'a' : 'div')) {
					svelte_element.d(1);
					svelte_element = create_dynamic_element(ctx);
					previous_tag = /*href*/ ctx[0] ? 'a' : 'div';
					svelte_element.c();
					svelte_element.m(li, null);
				} else {
					svelte_element.p(ctx, dirty);
				}
			} else if (previous_tag) {
				svelte_element.d(1);
				svelte_element = null;
				previous_tag = /*href*/ ctx[0] ? 'a' : 'div';
			}
		},
		i(local) {
			if (current) return;
			transition_in(svelte_element);
			current = true;
		},
		o(local) {
			transition_out(svelte_element);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			if (svelte_element) svelte_element.d(detaching);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	const omit_props_names = ["href","active","activeClass","nonActiveClass"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	let { href = '' } = $$props;
	let { active = false } = $$props;
	let { activeClass = undefined } = $$props;
	let { nonActiveClass = undefined } = $$props;
	const context = getContext('navbar') ?? {};
	let liClass;

	function blur_handler(event) {
		bubble.call(this, $$self, event);
	}

	function change_handler(event) {
		bubble.call(this, $$self, event);
	}

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	function focus_handler(event) {
		bubble.call(this, $$self, event);
	}

	function keydown_handler(event) {
		bubble.call(this, $$self, event);
	}

	function keypress_handler(event) {
		bubble.call(this, $$self, event);
	}

	function keyup_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler(event) {
		bubble.call(this, $$self, event);
	}

	$$self.$$set = $$new_props => {
		$$invalidate(19, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(2, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('href' in $$new_props) $$invalidate(0, href = $$new_props.href);
		if ('active' in $$new_props) $$invalidate(3, active = $$new_props.active);
		if ('activeClass' in $$new_props) $$invalidate(4, activeClass = $$new_props.activeClass);
		if ('nonActiveClass' in $$new_props) $$invalidate(5, nonActiveClass = $$new_props.nonActiveClass);
		if ('$$scope' in $$new_props) $$invalidate(6, $$scope = $$new_props.$$scope);
	};

	$$self.$$.update = () => {
		$$invalidate(1, liClass = classNames(
			'block py-2 pr-4 pl-3 md:p-0 rounded md:border-0',
			active
			? activeClass ?? context.activeClass
			: nonActiveClass ?? context.nonActiveClass,
			$$props.class
		));
	};

	$$props = exclude_internal_props($$props);

	return [
		href,
		liClass,
		$$restProps,
		active,
		activeClass,
		nonActiveClass,
		$$scope,
		slots,
		blur_handler,
		change_handler,
		click_handler,
		focus_handler,
		keydown_handler,
		keypress_handler,
		keyup_handler,
		mouseenter_handler,
		mouseleave_handler,
		mouseover_handler
	];
}

let Component$3 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			href: 0,
			active: 3,
			activeClass: 4,
			nonActiveClass: 5
		});
	}
};

/* generated by Svelte v3.59.1 */

function create_else_block$1(ctx) {
	let div;
	let ul;
	let current;
	const default_slot_template = /*#slots*/ ctx[9].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[10], null);

	let div_levels = [
		/*$$restProps*/ ctx[4],
		{ class: /*_divClass*/ ctx[2] },
		{ hidden: /*hidden*/ ctx[0] }
	];

	let div_data = {};

	for (let i = 0; i < div_levels.length; i += 1) {
		div_data = assign(div_data, div_levels[i]);
	}

	return {
		c() {
			div = element("div");
			ul = element("ul");
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			ul = claim_element(div_nodes, "UL", { class: true });
			var ul_nodes = children(ul);
			if (default_slot) default_slot.l(ul_nodes);
			ul_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(ul, "class", /*_ulClass*/ ctx[3]);
			set_attributes(div, div_data);
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, ul);

			if (default_slot) {
				default_slot.m(ul, null);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 1024)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[10],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[10])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[10], dirty, null),
						null
					);
				}
			}

			if (!current || dirty & /*_ulClass*/ 8) {
				attr(ul, "class", /*_ulClass*/ ctx[3]);
			}

			set_attributes(div, div_data = get_spread_update(div_levels, [
				dirty & /*$$restProps*/ 16 && /*$$restProps*/ ctx[4],
				(!current || dirty & /*_divClass*/ 4) && { class: /*_divClass*/ ctx[2] },
				(!current || dirty & /*hidden*/ 1) && { hidden: /*hidden*/ ctx[0] }
			]));
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			if (default_slot) default_slot.d(detaching);
		}
	};
}

// (24:0) {#if !hidden}
function create_if_block$1(ctx) {
	let div;
	let frame;
	let div_transition;
	let current;

	frame = new Component$e({
			props: {
				tag: "ul",
				border: true,
				rounded: true,
				color: "navbarUl",
				class: /*_ulClass*/ ctx[3],
				$$slots: { default: [create_default_slot$1] },
				$$scope: { ctx }
			}
		});

	let div_levels = [/*$$restProps*/ ctx[4], { class: /*_divClass*/ ctx[2] }];
	let div_data = {};

	for (let i = 0; i < div_levels.length; i += 1) {
		div_data = assign(div_data, div_levels[i]);
	}

	return {
		c() {
			div = element("div");
			create_component(frame.$$.fragment);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			claim_component(frame.$$.fragment, div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_attributes(div, div_data);
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			mount_component(frame, div, null);
			current = true;
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			const frame_changes = {};
			if (dirty & /*_ulClass*/ 8) frame_changes.class = /*_ulClass*/ ctx[3];

			if (dirty & /*$$scope*/ 1024) {
				frame_changes.$$scope = { dirty, ctx };
			}

			frame.$set(frame_changes);

			set_attributes(div, div_data = get_spread_update(div_levels, [
				dirty & /*$$restProps*/ 16 && /*$$restProps*/ ctx[4],
				(!current || dirty & /*_divClass*/ 4) && { class: /*_divClass*/ ctx[2] }
			]));
		},
		i(local) {
			if (current) return;
			transition_in(frame.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!div_transition) div_transition = create_bidirectional_transition(div, slide, /*slideParams*/ ctx[1], true);
				div_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(frame.$$.fragment, local);
			if (!div_transition) div_transition = create_bidirectional_transition(div, slide, /*slideParams*/ ctx[1], false);
			div_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_component(frame);
			if (detaching && div_transition) div_transition.end();
		}
	};
}

// (26:4) <Frame tag="ul" border rounded color="navbarUl" class={_ulClass}>
function create_default_slot$1(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[9].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[10], null);

	return {
		c() {
			if (default_slot) default_slot.c();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 1024)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[10],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[10])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[10], dirty, null),
						null
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function create_fragment$2(ctx) {
	let current_block_type_index;
	let if_block;
	let if_block_anchor;
	let current;
	const if_block_creators = [create_if_block$1, create_else_block$1];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (!/*hidden*/ ctx[0]) return 0;
		return 1;
	}

	current_block_type_index = select_block_type(ctx);
	if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_blocks[current_block_type_index].m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if_blocks[current_block_type_index].p(ctx, dirty);
			} else {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block = if_blocks[current_block_type_index];

				if (!if_block) {
					if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block.c();
				} else {
					if_block.p(ctx, dirty);
				}

				transition_in(if_block, 1);
				if_block.m(if_block_anchor.parentNode, if_block_anchor);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if_blocks[current_block_type_index].d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	const omit_props_names = ["divClass","ulClass","hidden","slideParams","activeClass","nonActiveClass"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	let { divClass = 'w-full md:block md:w-auto' } = $$props;
	let { ulClass = 'flex flex-col p-4 mt-4 md:flex-row md:space-x-8 md:mt-0 md:text-sm md:font-medium' } = $$props;
	let { hidden = true } = $$props;

	let { slideParams = {
		delay: 250,
		duration: 500,
		easing: quintOut
	} } = $$props;

	let { activeClass = 'text-white bg-blue-700 md:bg-transparent md:text-blue-700 md:dark:text-white dark:bg-blue-600 md:dark:bg-transparent' } = $$props;
	let { nonActiveClass = 'text-gray-700 hover:bg-gray-100 md:hover:bg-transparent md:border-0 md:hover:text-blue-700 dark:text-gray-400 md:dark:hover:text-white dark:hover:bg-gray-700 dark:hover:text-white md:dark:hover:bg-transparent' } = $$props;
	setContext('navbar', { activeClass, nonActiveClass });
	let _divClass;
	let _ulClass;

	$$self.$$set = $$new_props => {
		$$invalidate(11, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(4, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('divClass' in $$new_props) $$invalidate(5, divClass = $$new_props.divClass);
		if ('ulClass' in $$new_props) $$invalidate(6, ulClass = $$new_props.ulClass);
		if ('hidden' in $$new_props) $$invalidate(0, hidden = $$new_props.hidden);
		if ('slideParams' in $$new_props) $$invalidate(1, slideParams = $$new_props.slideParams);
		if ('activeClass' in $$new_props) $$invalidate(7, activeClass = $$new_props.activeClass);
		if ('nonActiveClass' in $$new_props) $$invalidate(8, nonActiveClass = $$new_props.nonActiveClass);
		if ('$$scope' in $$new_props) $$invalidate(10, $$scope = $$new_props.$$scope);
	};

	$$self.$$.update = () => {
		$$invalidate(2, _divClass = classNames(divClass, $$props.class));

		$$invalidate(3, _ulClass = classNames(ulClass, // 'divide-y md:divide-y-0 divide-gray-100 dark:divide-gray-700',
		$$props.class));
	};

	$$props = exclude_internal_props($$props);

	return [
		hidden,
		slideParams,
		_divClass,
		_ulClass,
		$$restProps,
		divClass,
		ulClass,
		activeClass,
		nonActiveClass,
		slots,
		$$scope
	];
}

let Component$2 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			divClass: 5,
			ulClass: 6,
			hidden: 0,
			slideParams: 1,
			activeClass: 7,
			nonActiveClass: 8
		});
	}
};

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      // Allow provider without '@': "provider:prefix:name"
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!// Check prefix: cannot be empty, unless allowSimpleName is enabled
  // Check name: cannot be empty
  ((allowSimpleName && icon.prefix === "" || !!icon.prefix) && !!icon.name);
};

const defaultIconDimensions = Object.freeze(
  {
    left: 0,
    top: 0,
    width: 16,
    height: 16
  }
);
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});

function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}

function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}

function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}

function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(
      icons[name2] || aliases[name2],
      currentProps
    );
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}

function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}

const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (
      // Name cannot be empty
      !name || // Must have body
      typeof icon.body !== "string" || // Check other props
      !checkOptionalProps(
        icon,
        defaultExtendedIconProps
      )
    ) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (
      // Name cannot be empty
      !name || // Parent must be set and point to existing icon
      typeof parent !== "string" || !icons[parent] && !aliases[parent] || // Check other props
      !checkOptionalProps(
        icon,
        defaultExtendedIconProps
      )
    ) {
      return null;
    }
  }
  return data;
}

const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage.icons[name] = icon;
    } else {
      storage.missing.add(name);
    }
  });
}
function addIconToStorage(storage, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage.icons[name] = { ...icon };
      return true;
    }
  } catch (err) {
  }
  return false;
}

let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage.icons[iconName] || (storage.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage = getStorage(icon.provider, icon.prefix);
  if (data) {
    return addIconToStorage(storage, icon.name, data);
  } else {
    storage.missing.add(icon.name);
    return true;
  }
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage = getStorage(provider, prefix);
  return !!addIconSet(storage, data);
}

const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  // Dimensions
  ...defaultIconSizeCustomisations,
  // Transformations
  ...defaultIconTransformations
});

const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}

function splitSVGDefs(content, tag = "defs") {
  let defs = "";
  const index = content.indexOf("<" + tag);
  while (index >= 0) {
    const start = content.indexOf(">", index);
    const end = content.indexOf("</" + tag);
    if (start === -1 || end === -1) {
      break;
    }
    const endEnd = content.indexOf(">", end);
    if (endEnd === -1) {
      break;
    }
    defs += content.slice(start + 1, end).trim();
    content = content.slice(0, index).trim() + content.slice(endEnd + 1);
  }
  return {
    defs,
    content
  };
}
function mergeDefsAndContent(defs, content) {
  return defs ? "<defs>" + defs + "</defs>" + content : content;
}
function wrapSVGContent(body, start, end) {
  const split = splitSVGDefs(body);
  return mergeDefsAndContent(split.defs, start + split.content + end);
}

const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push(
          "translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")"
        );
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push(
        "translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")"
      );
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift(
          "rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")"
        );
        break;
      case 2:
        transformations.unshift(
          "rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")"
        );
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift(
          "rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")"
        );
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = wrapSVGContent(
        body,
        '<g transform="' + transformations.join(" ") + '">',
        "</g>"
      );
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  const viewBox = [box.left, box.top, boxWidth, boxHeight];
  attributes.viewBox = viewBox.join(" ");
  return {
    attributes,
    viewBox,
    body
  };
}

const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(
      // Allowed characters before id: [#;"]
      // Allowed characters after id: [)"], .[a-z]
      new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"),
      "$1" + newID + suffix + "$3"
    );
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}

const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}

function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    // API hosts
    resources,
    // Root path
    path: source.path || "/",
    // URL length limit
    maxURL: source.maxURL || 500,
    // Timeout before next host is used.
    rotate: source.rotate || 750,
    // Timeout before failing query.
    timeout: source.timeout || 5e3,
    // Randomise default API end point.
    random: source.random === true,
    // Start index
    index: source.index || 0,
    // Receive data after time out (used if time out kicks in first, then API module sends data anyway).
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}

const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};

function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage[provider] || (storage[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}

function removeCallback(storages, id) {
  storages.forEach((storage) => {
    const items = storage.loaderCallbacks;
    if (items) {
      storage.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage) {
  if (!storage.pendingCallbacksFlag) {
    storage.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage.pendingCallbacksFlag = false;
      const items = storage.loaderCallbacks ? storage.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage.provider;
      const prefix = storage.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage], item.id);
          }
          item.callback(
            icons.loaded.slice(0),
            icons.missing.slice(0),
            icons.pending.slice(0),
            item.abort
          );
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage) => {
    (storage.loaderCallbacks || (storage.loaderCallbacks = [])).push(item);
  });
  return abort;
}

function listToIcons(list, validate = true, simpleNames = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}

// src/config.ts
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};

// src/query.ts
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}

// src/index.ts
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(
      config,
      payload,
      queryCallback,
      (data, error) => {
        cleanup();
        if (doneCallback) {
          doneCallback(data, error);
        }
      }
    );
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}

function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send = api.send;
      }
    }
  }
  if (!redundancy || !send) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send, callback)().abort;
}

function emptyCallback() {
}
function loadedNewIcons(storage) {
  if (!storage.iconsLoaderFlag) {
    storage.iconsLoaderFlag = true;
    setTimeout(() => {
      storage.iconsLoaderFlag = false;
      updateCallbacks(storage);
    });
  }
}
function checkIconNamesForAPI(icons) {
  const valid = [];
  const invalid = [];
  icons.forEach((name) => {
    (name.match(matchIconName) ? valid : invalid).push(name);
  });
  return {
    valid,
    invalid
  };
}
function parseLoaderResponse(storage, icons, data) {
  function checkMissing() {
    const pending = storage.pendingIcons;
    icons.forEach((name) => {
      if (pending) {
        pending.delete(name);
      }
      if (!storage.icons[name]) {
        storage.missing.add(name);
      }
    });
  }
  if (data && typeof data === "object") {
    try {
      const parsed = addIconSet(storage, data);
      if (!parsed.length) {
        checkMissing();
        return;
      }
    } catch (err) {
      console.error(err);
    }
  }
  checkMissing();
  loadedNewIcons(storage);
}
function parsePossiblyAsyncResponse(response, callback) {
  if (response instanceof Promise) {
    response.then((data) => {
      callback(data);
    }).catch(() => {
      callback(null);
    });
  } else {
    callback(response);
  }
}
function loadNewIcons(storage, icons) {
  if (!storage.iconsToLoad) {
    storage.iconsToLoad = icons;
  } else {
    storage.iconsToLoad = storage.iconsToLoad.concat(icons).sort();
  }
  if (!storage.iconsQueueFlag) {
    storage.iconsQueueFlag = true;
    setTimeout(() => {
      storage.iconsQueueFlag = false;
      const { provider, prefix } = storage;
      const icons2 = storage.iconsToLoad;
      delete storage.iconsToLoad;
      if (!icons2 || !icons2.length) {
        return;
      }
      const customIconLoader = storage.loadIcon;
      if (storage.loadIcons && (icons2.length > 1 || !customIconLoader)) {
        parsePossiblyAsyncResponse(
          storage.loadIcons(icons2, prefix, provider),
          (data) => {
            parseLoaderResponse(storage, icons2, data);
          }
        );
        return;
      }
      if (customIconLoader) {
        icons2.forEach((name) => {
          const response = customIconLoader(name, prefix, provider);
          parsePossiblyAsyncResponse(response, (data) => {
            const iconSet = data ? {
              prefix,
              icons: {
                [name]: data
              }
            } : null;
            parseLoaderResponse(storage, [name], iconSet);
          });
        });
        return;
      }
      const { valid, invalid } = checkIconNamesForAPI(icons2);
      if (invalid.length) {
        parseLoaderResponse(storage, invalid, null);
      }
      if (!valid.length) {
        return;
      }
      const api = prefix.match(matchIconName) ? getAPIModule(provider) : null;
      if (!api) {
        parseLoaderResponse(storage, valid, null);
        return;
      }
      const params = api.prepare(provider, prefix, valid);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          parseLoaderResponse(storage, item.icons, data);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(
            sortedIcons.loaded,
            sortedIcons.missing,
            sortedIcons.pending,
            emptyCallback
          );
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const { provider, prefix } = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const { provider, prefix, name } = icon;
    const storage = getStorage(provider, prefix);
    const pendingQueue = storage.pendingIcons || (storage.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage) => {
    const list = newIcons[storage.provider][storage.prefix];
    if (list.length) {
      loadNewIcons(storage, list);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};

function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}

const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}

function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}

function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}

function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}

const defaultExtendedIconCustomisations = {
    ...defaultIconCustomisations,
    inline: false,
};

/**
 * Default SVG attributes
 */
const svgDefaults = {
    'xmlns': 'http://www.w3.org/2000/svg',
    'xmlns:xlink': 'http://www.w3.org/1999/xlink',
    'aria-hidden': true,
    'role': 'img',
};
/**
 * Style modes
 */
const commonProps = {
    display: 'inline-block',
};
const monotoneProps = {
    'background-color': 'currentColor',
};
const coloredProps = {
    'background-color': 'transparent',
};
// Dynamically add common props to variables above
const propsToAdd = {
    image: 'var(--svg)',
    repeat: 'no-repeat',
    size: '100% 100%',
};
const propsToAddTo = {
    '-webkit-mask': monotoneProps,
    'mask': monotoneProps,
    'background': coloredProps,
};
for (const prefix in propsToAddTo) {
    const list = propsToAddTo[prefix];
    for (const prop in propsToAdd) {
        list[prefix + '-' + prop] = propsToAdd[prop];
    }
}
/**
 * Fix size: add 'px' to numbers
 */
function fixSize(value) {
    return value + (value.match(/^[-0-9.]+$/) ? 'px' : '');
}
/**
 * Generate icon from properties
 */
function render(
// Icon must be validated before calling this function
icon, 
// Properties
props) {
    const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
    // Check mode
    const mode = props.mode || 'svg';
    const componentProps = (mode === 'svg' ? { ...svgDefaults } : {});
    if (icon.body.indexOf('xlink:') === -1) {
        delete componentProps['xmlns:xlink'];
    }
    // Create style if missing
    let style = typeof props.style === 'string' ? props.style : '';
    // Get element properties
    for (let key in props) {
        const value = props[key];
        if (value === void 0) {
            continue;
        }
        switch (key) {
            // Properties to ignore
            case 'icon':
            case 'style':
            case 'onLoad':
            case 'mode':
            case 'ssr':
                break;
            // Boolean attributes
            case 'inline':
            case 'hFlip':
            case 'vFlip':
                customisations[key] =
                    value === true || value === 'true' || value === 1;
                break;
            // Flip as string: 'horizontal,vertical'
            case 'flip':
                if (typeof value === 'string') {
                    flipFromString(customisations, value);
                }
                break;
            // Color: copy to style, add extra ';' in case style is missing it
            case 'color':
                style =
                    style +
                        (style.length > 0 && style.trim().slice(-1) !== ';'
                            ? ';'
                            : '') +
                        'color: ' +
                        value +
                        '; ';
                break;
            // Rotation as string
            case 'rotate':
                if (typeof value === 'string') {
                    customisations[key] = rotateFromString(value);
                }
                else if (typeof value === 'number') {
                    customisations[key] = value;
                }
                break;
            // Remove aria-hidden
            case 'ariaHidden':
            case 'aria-hidden':
                if (value !== true && value !== 'true') {
                    delete componentProps['aria-hidden'];
                }
                break;
            default:
                if (key.slice(0, 3) === 'on:') {
                    // Svelte event
                    break;
                }
                // Copy missing property if it does not exist in customisations
                if (defaultExtendedIconCustomisations[key] === void 0) {
                    componentProps[key] = value;
                }
        }
    }
    // Generate icon
    const item = iconToSVG(icon, customisations);
    const renderAttribs = item.attributes;
    // Inline display
    if (customisations.inline) {
        // Style overrides it
        style = 'vertical-align: -0.125em; ' + style;
    }
    if (mode === 'svg') {
        // Add icon stuff
        Object.assign(componentProps, renderAttribs);
        // Style
        if (style !== '') {
            componentProps.style = style;
        }
        // Counter for ids based on "id" property to render icons consistently on server and client
        let localCounter = 0;
        let id = props.id;
        if (typeof id === 'string') {
            // Convert '-' to '_' to avoid errors in animations
            id = id.replace(/-/g, '_');
        }
        // Generate HTML
        return {
            svg: true,
            attributes: componentProps,
            body: replaceIDs(item.body, id ? () => id + 'ID' + localCounter++ : 'iconifySvelte'),
        };
    }
    // Render <span> with style
    const { body, width, height } = icon;
    const useMask = mode === 'mask' ||
        (mode === 'bg' ? false : body.indexOf('currentColor') !== -1);
    // Generate SVG
    const html = iconToHTML(body, {
        ...renderAttribs,
        width: width + '',
        height: height + '',
    });
    // Generate style
    const url = svgToURL(html);
    const styles = {
        '--svg': url,
    };
    const size = (prop) => {
        const value = renderAttribs[prop];
        if (value) {
            styles[prop] = fixSize(value);
        }
    };
    size('width');
    size('height');
    Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
    let customStyle = '';
    for (const key in styles) {
        customStyle += key + ': ' + styles[key] + ';';
    }
    componentProps.style = customStyle + style;
    return {
        svg: false,
        attributes: componentProps,
    };
}
/**
 * Initialise stuff
 */
// Enable short names
allowSimpleNames(true);
// Set API module
setAPIModule('', fetchAPIModule);
/**
 * Browser stuff
 */
if (typeof document !== 'undefined' && typeof window !== 'undefined') {
    const _window = window;
    // Load icons from global "IconifyPreload"
    if (_window.IconifyPreload !== void 0) {
        const preload = _window.IconifyPreload;
        const err = 'Invalid IconifyPreload syntax.';
        if (typeof preload === 'object' && preload !== null) {
            (preload instanceof Array ? preload : [preload]).forEach((item) => {
                try {
                    if (
                    // Check if item is an object and not null/array
                    typeof item !== 'object' ||
                        item === null ||
                        item instanceof Array ||
                        // Check for 'icons' and 'prefix'
                        typeof item.icons !== 'object' ||
                        typeof item.prefix !== 'string' ||
                        // Add icon set
                        !addCollection(item)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            });
        }
    }
    // Set API from global "IconifyProviders"
    if (_window.IconifyProviders !== void 0) {
        const providers = _window.IconifyProviders;
        if (typeof providers === 'object' && providers !== null) {
            for (let key in providers) {
                const err = 'IconifyProviders[' + key + '] is invalid.';
                try {
                    const value = providers[key];
                    if (typeof value !== 'object' ||
                        !value ||
                        value.resources === void 0) {
                        continue;
                    }
                    if (!addAPIProvider(key, value)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            }
        }
    }
}
/**
 * Check if component needs to be updated
 */
function checkIconState(icon, state, mounted, callback, onload) {
    // Abort loading icon
    function abortLoading() {
        if (state.loading) {
            state.loading.abort();
            state.loading = null;
        }
    }
    // Icon is an object
    if (typeof icon === 'object' &&
        icon !== null &&
        typeof icon.body === 'string') {
        // Stop loading
        state.name = '';
        abortLoading();
        return { data: { ...defaultIconProps, ...icon } };
    }
    // Invalid icon?
    let iconName;
    if (typeof icon !== 'string' ||
        (iconName = stringToIcon(icon, false, true)) === null) {
        abortLoading();
        return null;
    }
    // Load icon
    const data = getIconData(iconName);
    if (!data) {
        // Icon data is not available
        // Do not load icon until component is mounted
        if (mounted && (!state.loading || state.loading.name !== icon)) {
            // New icon to load
            abortLoading();
            state.name = '';
            state.loading = {
                name: icon,
                abort: loadIcons([iconName], callback),
            };
        }
        return null;
    }
    // Icon data is available
    abortLoading();
    if (state.name !== icon) {
        state.name = icon;
        if (onload && !state.destroyed) {
            onload(icon);
        }
    }
    // Add classes
    const classes = ['iconify'];
    if (iconName.prefix !== '') {
        classes.push('iconify--' + iconName.prefix);
    }
    if (iconName.provider !== '') {
        classes.push('iconify--' + iconName.provider);
    }
    return { data, classes };
}
/**
 * Generate icon
 */
function generateIcon(icon, props) {
    return icon
        ? render({
            ...defaultIconProps,
            ...icon,
        }, props)
        : null;
}

/* generated by Svelte v3.59.1 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (120:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (116:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher$1();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		{
			const isMounted = !!$$props.ssr || mounted;
			const iconData = checkIconState($$props.icon, state, isMounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

let Component$1 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot_12(ctx) {
	let img;
	let img_src_value;
	let t0;
	let span;
	let t1;

	return {
		c() {
			img = element("img");
			t0 = space();
			span = element("span");
			t1 = text("Flowbite");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, class: true, alt: true });
			t0 = claim_space(nodes);
			span = claim_element(nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, "Flowbite");
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = "/images/flowbite-svelte-icon-logo.svg")) attr(img, "src", img_src_value);
			attr(img, "class", "me-3 h-6 sm:h-9");
			attr(img, "alt", "Flowbite Logo");
			attr(span, "class", "self-center whitespace-nowrap text-xl font-semibold dark:text-white");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
			insert_hydration(target, t0, anchor);
			insert_hydration(target, span, anchor);
			append_hydration(span, t1);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(img);
			if (detaching) detach(t0);
			if (detaching) detach(span);
		}
	};
}

// (18:4) <NavLi href="/">
function create_default_slot_11(ctx) {
	let t;

	return {
		c() {
			t = text("Home");
		},
		l(nodes) {
			t = claim_text(nodes, "Home");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (19:4) <NavLi class="cursor-pointer">
function create_default_slot_10(ctx) {
	let icon;
	let current;
	icon = new Component$1({ props: { icon: "lucide:chevron-down" } });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

// (23:6) <DropdownItem href="/">
function create_default_slot_9(ctx) {
	let t;

	return {
		c() {
			t = text("Dashboard");
		},
		l(nodes) {
			t = claim_text(nodes, "Dashboard");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (24:6) <DropdownItem href="/docs/components/navbar">
function create_default_slot_8(ctx) {
	let t;

	return {
		c() {
			t = text("Settings");
		},
		l(nodes) {
			t = claim_text(nodes, "Settings");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (25:6) <DropdownItem href="/">
function create_default_slot_7(ctx) {
	let t;

	return {
		c() {
			t = text("Earnings");
		},
		l(nodes) {
			t = claim_text(nodes, "Earnings");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (27:6) <DropdownItem href="/">
function create_default_slot_6(ctx) {
	let t;

	return {
		c() {
			t = text("Sign out");
		},
		l(nodes) {
			t = claim_text(nodes, "Sign out");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (22:4) <Dropdown class="w-44 z-20">
function create_default_slot_5(ctx) {
	let dropdownitem0;
	let t0;
	let dropdownitem1;
	let t1;
	let dropdownitem2;
	let t2;
	let dropdowndivider;
	let t3;
	let dropdownitem3;
	let current;

	dropdownitem0 = new Component$8({
			props: {
				href: "/",
				$$slots: { default: [create_default_slot_9] },
				$$scope: { ctx }
			}
		});

	dropdownitem1 = new Component$8({
			props: {
				href: "/docs/components/navbar",
				$$slots: { default: [create_default_slot_8] },
				$$scope: { ctx }
			}
		});

	dropdownitem2 = new Component$8({
			props: {
				href: "/",
				$$slots: { default: [create_default_slot_7] },
				$$scope: { ctx }
			}
		});

	dropdowndivider = new Component$a({});

	dropdownitem3 = new Component$8({
			props: {
				href: "/",
				$$slots: { default: [create_default_slot_6] },
				$$scope: { ctx }
			}
		});

	return {
		c() {
			create_component(dropdownitem0.$$.fragment);
			t0 = space();
			create_component(dropdownitem1.$$.fragment);
			t1 = space();
			create_component(dropdownitem2.$$.fragment);
			t2 = space();
			create_component(dropdowndivider.$$.fragment);
			t3 = space();
			create_component(dropdownitem3.$$.fragment);
		},
		l(nodes) {
			claim_component(dropdownitem0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(dropdownitem1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(dropdownitem2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(dropdowndivider.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(dropdownitem3.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(dropdownitem0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(dropdownitem1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(dropdownitem2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(dropdowndivider, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(dropdownitem3, target, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const dropdownitem0_changes = {};

			if (dirty & /*$$scope*/ 2) {
				dropdownitem0_changes.$$scope = { dirty, ctx };
			}

			dropdownitem0.$set(dropdownitem0_changes);
			const dropdownitem1_changes = {};

			if (dirty & /*$$scope*/ 2) {
				dropdownitem1_changes.$$scope = { dirty, ctx };
			}

			dropdownitem1.$set(dropdownitem1_changes);
			const dropdownitem2_changes = {};

			if (dirty & /*$$scope*/ 2) {
				dropdownitem2_changes.$$scope = { dirty, ctx };
			}

			dropdownitem2.$set(dropdownitem2_changes);
			const dropdownitem3_changes = {};

			if (dirty & /*$$scope*/ 2) {
				dropdownitem3_changes.$$scope = { dirty, ctx };
			}

			dropdownitem3.$set(dropdownitem3_changes);
		},
		i(local) {
			if (current) return;
			transition_in(dropdownitem0.$$.fragment, local);
			transition_in(dropdownitem1.$$.fragment, local);
			transition_in(dropdownitem2.$$.fragment, local);
			transition_in(dropdowndivider.$$.fragment, local);
			transition_in(dropdownitem3.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(dropdownitem0.$$.fragment, local);
			transition_out(dropdownitem1.$$.fragment, local);
			transition_out(dropdownitem2.$$.fragment, local);
			transition_out(dropdowndivider.$$.fragment, local);
			transition_out(dropdownitem3.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(dropdownitem0, detaching);
			if (detaching) detach(t0);
			destroy_component(dropdownitem1, detaching);
			if (detaching) detach(t1);
			destroy_component(dropdownitem2, detaching);
			if (detaching) detach(t2);
			destroy_component(dropdowndivider, detaching);
			if (detaching) detach(t3);
			destroy_component(dropdownitem3, detaching);
		}
	};
}

// (29:4) <NavLi href="/settings">
function create_default_slot_4(ctx) {
	let t;

	return {
		c() {
			t = text("Setting");
		},
		l(nodes) {
			t = claim_text(nodes, "Setting");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (30:4) <NavLi href="/pricing">
function create_default_slot_3(ctx) {
	let t;

	return {
		c() {
			t = text("Pricing");
		},
		l(nodes) {
			t = claim_text(nodes, "Pricing");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (31:4) <NavLi href="/contact">
function create_default_slot_2(ctx) {
	let t;

	return {
		c() {
			t = text("Contact");
		},
		l(nodes) {
			t = claim_text(nodes, "Contact");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (17:2) <NavUl>
function create_default_slot_1(ctx) {
	let navli0;
	let t0;
	let navli1;
	let t1;
	let dropdown;
	let t2;
	let navli2;
	let t3;
	let navli3;
	let t4;
	let navli4;
	let current;

	navli0 = new Component$3({
			props: {
				href: "/",
				$$slots: { default: [create_default_slot_11] },
				$$scope: { ctx }
			}
		});

	navli1 = new Component$3({
			props: {
				class: "cursor-pointer",
				$$slots: { default: [create_default_slot_10] },
				$$scope: { ctx }
			}
		});

	dropdown = new Component$b({
			props: {
				class: "w-44 z-20",
				$$slots: { default: [create_default_slot_5] },
				$$scope: { ctx }
			}
		});

	navli2 = new Component$3({
			props: {
				href: "/settings",
				$$slots: { default: [create_default_slot_4] },
				$$scope: { ctx }
			}
		});

	navli3 = new Component$3({
			props: {
				href: "/pricing",
				$$slots: { default: [create_default_slot_3] },
				$$scope: { ctx }
			}
		});

	navli4 = new Component$3({
			props: {
				href: "/contact",
				$$slots: { default: [create_default_slot_2] },
				$$scope: { ctx }
			}
		});

	return {
		c() {
			create_component(navli0.$$.fragment);
			t0 = space();
			create_component(navli1.$$.fragment);
			t1 = space();
			create_component(dropdown.$$.fragment);
			t2 = space();
			create_component(navli2.$$.fragment);
			t3 = space();
			create_component(navli3.$$.fragment);
			t4 = space();
			create_component(navli4.$$.fragment);
		},
		l(nodes) {
			claim_component(navli0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(navli1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(dropdown.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(navli2.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(navli3.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(navli4.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(navli0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(navli1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(dropdown, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(navli2, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(navli3, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(navli4, target, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const navli0_changes = {};

			if (dirty & /*$$scope*/ 2) {
				navli0_changes.$$scope = { dirty, ctx };
			}

			navli0.$set(navli0_changes);
			const navli1_changes = {};

			if (dirty & /*$$scope*/ 2) {
				navli1_changes.$$scope = { dirty, ctx };
			}

			navli1.$set(navli1_changes);
			const dropdown_changes = {};

			if (dirty & /*$$scope*/ 2) {
				dropdown_changes.$$scope = { dirty, ctx };
			}

			dropdown.$set(dropdown_changes);
			const navli2_changes = {};

			if (dirty & /*$$scope*/ 2) {
				navli2_changes.$$scope = { dirty, ctx };
			}

			navli2.$set(navli2_changes);
			const navli3_changes = {};

			if (dirty & /*$$scope*/ 2) {
				navli3_changes.$$scope = { dirty, ctx };
			}

			navli3.$set(navli3_changes);
			const navli4_changes = {};

			if (dirty & /*$$scope*/ 2) {
				navli4_changes.$$scope = { dirty, ctx };
			}

			navli4.$set(navli4_changes);
		},
		i(local) {
			if (current) return;
			transition_in(navli0.$$.fragment, local);
			transition_in(navli1.$$.fragment, local);
			transition_in(dropdown.$$.fragment, local);
			transition_in(navli2.$$.fragment, local);
			transition_in(navli3.$$.fragment, local);
			transition_in(navli4.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(navli0.$$.fragment, local);
			transition_out(navli1.$$.fragment, local);
			transition_out(dropdown.$$.fragment, local);
			transition_out(navli2.$$.fragment, local);
			transition_out(navli3.$$.fragment, local);
			transition_out(navli4.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(navli0, detaching);
			if (detaching) detach(t0);
			destroy_component(navli1, detaching);
			if (detaching) detach(t1);
			destroy_component(dropdown, detaching);
			if (detaching) detach(t2);
			destroy_component(navli2, detaching);
			if (detaching) detach(t3);
			destroy_component(navli3, detaching);
			if (detaching) detach(t4);
			destroy_component(navli4, detaching);
		}
	};
}

// (11:10) <Navbar>
function create_default_slot(ctx) {
	let navbrand;
	let t0;
	let navhamburger;
	let t1;
	let navul;
	let current;

	navbrand = new Component$6({
			props: {
				href: "/",
				$$slots: { default: [create_default_slot_12] },
				$$scope: { ctx }
			}
		});

	navhamburger = new Component$4({});

	navul = new Component$2({
			props: {
				$$slots: { default: [create_default_slot_1] },
				$$scope: { ctx }
			}
		});

	return {
		c() {
			create_component(navbrand.$$.fragment);
			t0 = space();
			create_component(navhamburger.$$.fragment);
			t1 = space();
			create_component(navul.$$.fragment);
		},
		l(nodes) {
			claim_component(navbrand.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(navhamburger.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(navul.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(navbrand, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(navhamburger, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(navul, target, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const navbrand_changes = {};

			if (dirty & /*$$scope*/ 2) {
				navbrand_changes.$$scope = { dirty, ctx };
			}

			navbrand.$set(navbrand_changes);
			const navul_changes = {};

			if (dirty & /*$$scope*/ 2) {
				navul_changes.$$scope = { dirty, ctx };
			}

			navul.$set(navul_changes);
		},
		i(local) {
			if (current) return;
			transition_in(navbrand.$$.fragment, local);
			transition_in(navhamburger.$$.fragment, local);
			transition_in(navul.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(navbrand.$$.fragment, local);
			transition_out(navhamburger.$$.fragment, local);
			transition_out(navul.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(navbrand, detaching);
			if (detaching) detach(t0);
			destroy_component(navhamburger, detaching);
			if (detaching) detach(t1);
			destroy_component(navul, detaching);
		}
	};
}

function create_fragment(ctx) {
	let navbar;
	let current;

	navbar = new Component$7({
			props: {
				$$slots: { default: [create_default_slot] },
				$$scope: { ctx }
			}
		});

	return {
		c() {
			create_component(navbar.$$.fragment);
		},
		l(nodes) {
			claim_component(navbar.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(navbar, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const navbar_changes = {};

			if (dirty & /*$$scope*/ 2) {
				navbar_changes.$$scope = { dirty, ctx };
			}

			navbar.$set(navbar_changes);
		},
		i(local) {
			if (current) return;
			transition_in(navbar.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(navbar.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(navbar, detaching);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(0, props = $$props.props);
	};

	return [props];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { props: 0 });
	}
}

export { Component as default };
