// Carbon Components - Updated January 10, 2025
function noop() { }
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
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function subscribe(store, ...callbacks) {
    if (store == null) {
        return noop;
    }
    const unsub = store.subscribe(...callbacks);
    return unsub.unsubscribe ? () => unsub.unsubscribe() : unsub;
}
function get_store_value(store) {
    let value;
    subscribe(store, _ => value = _)();
    return value;
}
function component_subscribe(component, store, callback) {
    component.$$.on_destroy.push(subscribe(store, callback));
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
function set_store_value(store, ret, value) {
    store.set(value);
    return ret;
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
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
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
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function construct_svelte_component(component, props) {
    return new component(props);
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
 * Schedules a callback to run immediately after the component has been updated.
 *
 * The first time the callback runs will be after the initial `onMount`
 */
function afterUpdate(fn) {
    get_current_component().$$.after_update.push(fn);
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
function createEventDispatcher() {
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
function outro_and_destroy_block(block, lookup) {
    transition_out(block, 1, 1, () => {
        lookup.delete(block.key);
    });
}
function update_keyed_each(old_blocks, dirty, get_key, dynamic, ctx, list, lookup, node, destroy, create_each_block, next, get_context) {
    let o = old_blocks.length;
    let n = list.length;
    let i = o;
    const old_indexes = {};
    while (i--)
        old_indexes[old_blocks[i].key] = i;
    const new_blocks = [];
    const new_lookup = new Map();
    const deltas = new Map();
    const updates = [];
    i = n;
    while (i--) {
        const child_ctx = get_context(ctx, list, i);
        const key = get_key(child_ctx);
        let block = lookup.get(key);
        if (!block) {
            block = create_each_block(key, child_ctx);
            block.c();
        }
        else if (dynamic) {
            // defer updates until all the DOM shuffling is done
            updates.push(() => block.p(child_ctx, dirty));
        }
        new_lookup.set(key, new_blocks[i] = block);
        if (key in old_indexes)
            deltas.set(key, Math.abs(i - old_indexes[key]));
    }
    const will_move = new Set();
    const did_move = new Set();
    function insert(block) {
        transition_in(block, 1);
        block.m(node, next);
        lookup.set(block.key, block);
        next = block.first;
        n--;
    }
    while (o && n) {
        const new_block = new_blocks[n - 1];
        const old_block = old_blocks[o - 1];
        const new_key = new_block.key;
        const old_key = old_block.key;
        if (new_block === old_block) {
            // do nothing
            next = new_block.first;
            o--;
            n--;
        }
        else if (!new_lookup.has(old_key)) {
            // remove old block
            destroy(old_block, lookup);
            o--;
        }
        else if (!lookup.has(new_key) || will_move.has(new_key)) {
            insert(new_block);
        }
        else if (did_move.has(old_key)) {
            o--;
        }
        else if (deltas.get(new_key) > deltas.get(old_key)) {
            did_move.add(new_key);
            insert(new_block);
        }
        else {
            will_move.add(old_key);
            o--;
        }
    }
    while (o--) {
        const old_block = old_blocks[o];
        if (!new_lookup.has(old_block.key))
            destroy(old_block, lookup);
    }
    while (n)
        insert(new_blocks[n - 1]);
    run_all(updates);
    return new_blocks;
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

const subscriber_queue = [];
/**
 * Create a `Writable` store that allows both updating and reading by subscription.
 * @param {*=}value initial value
 * @param {StartStopNotifier=} start
 */
function writable(value, start = noop) {
    let stop;
    const subscribers = new Set();
    function set(new_value) {
        if (safe_not_equal(value, new_value)) {
            value = new_value;
            if (stop) { // store is ready
                const run_queue = !subscriber_queue.length;
                for (const subscriber of subscribers) {
                    subscriber[1]();
                    subscriber_queue.push(subscriber, value);
                }
                if (run_queue) {
                    for (let i = 0; i < subscriber_queue.length; i += 2) {
                        subscriber_queue[i][0](subscriber_queue[i + 1]);
                    }
                    subscriber_queue.length = 0;
                }
            }
        }
    }
    function update(fn) {
        set(fn(value));
    }
    function subscribe(run, invalidate = noop) {
        const subscriber = [run, invalidate];
        subscribers.add(subscriber);
        if (subscribers.size === 1) {
            stop = start(set) || noop;
        }
        run(value);
        return () => {
            subscribers.delete(subscriber);
            if (subscribers.size === 0 && stop) {
                stop();
                stop = null;
            }
        };
    }
    return { set, update, subscribe };
}

/* generated by Svelte v3.59.1 */

function create_if_block$7(ctx) {
	let title_1;
	let t;

	return {
		c() {
			title_1 = svg_element("title");
			t = text(/*title*/ ctx[1]);
		},
		l(nodes) {
			title_1 = claim_svg_element(nodes, "title", {});
			var title_1_nodes = children(title_1);
			t = claim_text(title_1_nodes, /*title*/ ctx[1]);
			title_1_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, title_1, anchor);
			append_hydration(title_1, t);
		},
		p(ctx, dirty) {
			if (dirty & /*title*/ 2) set_data(t, /*title*/ ctx[1]);
		},
		d(detaching) {
			if (detaching) detach(title_1);
		}
	};
}

function create_fragment$9(ctx) {
	let svg;
	let path;
	let if_block = /*title*/ ctx[1] && create_if_block$7(ctx);

	let svg_levels = [
		{ xmlns: "http://www.w3.org/2000/svg" },
		{ viewBox: "0 0 32 32" },
		{ fill: "currentColor" },
		{ preserveAspectRatio: "xMidYMid meet" },
		{ width: /*size*/ ctx[0] },
		{ height: /*size*/ ctx[0] },
		/*attributes*/ ctx[2],
		/*$$restProps*/ ctx[3]
	];

	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			if (if_block) if_block.c();
			path = svg_element("path");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {
				xmlns: true,
				viewBox: true,
				fill: true,
				preserveAspectRatio: true,
				width: true,
				height: true
			});

			var svg_nodes = children(svg);
			if (if_block) if_block.l(svg_nodes);
			path = claim_svg_element(svg_nodes, "path", { d: true });
			children(path).forEach(detach);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(path, "d", "M22 16L12 26 10.6 24.6 19.2 16 10.6 7.4 12 6z");
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			if (if_block) if_block.m(svg, null);
			append_hydration(svg, path);
		},
		p(ctx, [dirty]) {
			if (/*title*/ ctx[1]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$7(ctx);
					if_block.c();
					if_block.m(svg, path);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [
				{ xmlns: "http://www.w3.org/2000/svg" },
				{ viewBox: "0 0 32 32" },
				{ fill: "currentColor" },
				{ preserveAspectRatio: "xMidYMid meet" },
				dirty & /*size*/ 1 && { width: /*size*/ ctx[0] },
				dirty & /*size*/ 1 && { height: /*size*/ ctx[0] },
				dirty & /*attributes*/ 4 && /*attributes*/ ctx[2],
				dirty & /*$$restProps*/ 8 && /*$$restProps*/ ctx[3]
			]));
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(svg);
			if (if_block) if_block.d();
		}
	};
}

function instance$9($$self, $$props, $$invalidate) {
	let labelled;
	let attributes;
	const omit_props_names = ["size","title"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { size = 16 } = $$props;
	let { title = undefined } = $$props;

	$$self.$$set = $$new_props => {
		$$invalidate(5, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(3, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('size' in $$new_props) $$invalidate(0, size = $$new_props.size);
		if ('title' in $$new_props) $$invalidate(1, title = $$new_props.title);
	};

	$$self.$$.update = () => {
		$$invalidate(4, labelled = $$props["aria-label"] || $$props["aria-labelledby"] || title);

		$$invalidate(2, attributes = {
			"aria-hidden": labelled ? undefined : true,
			role: labelled ? "img" : undefined,
			focusable: Number($$props["tabindex"]) === 0 ? true : undefined
		});
	};

	$$props = exclude_internal_props($$props);
	return [size, title, attributes, $$restProps, labelled];
}

let Component$9 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$9, create_fragment$9, safe_not_equal, { size: 0, title: 1 });
	}
};

/* generated by Svelte v3.59.1 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i];
	return child_ctx;
}

// (38:0) {:else}
function create_else_block$3(ctx) {
	let p;
	let mounted;
	let dispose;
	let p_levels = [/*$$restProps*/ ctx[7]];
	let p_data = {};

	for (let i = 0; i < p_levels.length; i += 1) {
		p_data = assign(p_data, p_levels[i]);
	}

	return {
		c() {
			p = element("p");
			this.h();
		},
		l(nodes) {
			p = claim_element(nodes, "P", {});
			children(p).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(p, p_data);
			toggle_class(p, "bx--skeleton__text", true);
			toggle_class(p, "bx--skeleton__heading", /*heading*/ ctx[1]);
			set_style(p, "width", /*width*/ ctx[3]);
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);

			if (!mounted) {
				dispose = [
					listen(p, "click", /*click_handler_1*/ ctx[12]),
					listen(p, "mouseover", /*mouseover_handler_1*/ ctx[13]),
					listen(p, "mouseenter", /*mouseenter_handler_1*/ ctx[14]),
					listen(p, "mouseleave", /*mouseleave_handler_1*/ ctx[15])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			set_attributes(p, p_data = get_spread_update(p_levels, [dirty & /*$$restProps*/ 128 && /*$$restProps*/ ctx[7]]));
			toggle_class(p, "bx--skeleton__text", true);
			toggle_class(p, "bx--skeleton__heading", /*heading*/ ctx[1]);
			set_style(p, "width", /*width*/ ctx[3]);
		},
		d(detaching) {
			if (detaching) detach(p);
			mounted = false;
			run_all(dispose);
		}
	};
}

// (21:0) {#if paragraph}
function create_if_block$6(ctx) {
	let div;
	let mounted;
	let dispose;
	let each_value = Array.from({ length: /*lines*/ ctx[0] }).map(/*func*/ ctx[16]);
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	let div_levels = [/*$$restProps*/ ctx[7]];
	let div_data = {};

	for (let i = 0; i < div_levels.length; i += 1) {
		div_data = assign(div_data, div_levels[i]);
	}

	return {
		c() {
			div = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", {});
			var div_nodes = children(div);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div_nodes);
			}

			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_attributes(div, div_data);
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div, null);
				}
			}

			if (!mounted) {
				dispose = [
					listen(div, "click", /*click_handler*/ ctx[8]),
					listen(div, "mouseover", /*mouseover_handler*/ ctx[9]),
					listen(div, "mouseenter", /*mouseenter_handler*/ ctx[10]),
					listen(div, "mouseleave", /*mouseleave_handler*/ ctx[11])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*heading, Array, lines, widthPx, widthNum, Math, RANDOM, width*/ 123) {
				each_value = Array.from({ length: /*lines*/ ctx[0] }).map(/*func*/ ctx[16]);
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			set_attributes(div, div_data = get_spread_update(div_levels, [dirty & /*$$restProps*/ 128 && /*$$restProps*/ ctx[7]]));
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
			mounted = false;
			run_all(dispose);
		}
	};
}

// (24:4) {#each Array.from({ length: lines }).map((_, i) => {       const min = widthPx ? widthNum - 75 : 0;       const max = widthPx ? widthNum : 75;       const rand = Math.floor(RANDOM[i % 3] * (max - min + 1)) + min + "px";        return widthPx ? rand : `calc(${width} - ${rand})`;     }) as width}
function create_each_block$2(ctx) {
	let p;

	return {
		c() {
			p = element("p");
			this.h();
		},
		l(nodes) {
			p = claim_element(nodes, "P", {});
			children(p).forEach(detach);
			this.h();
		},
		h() {
			toggle_class(p, "bx--skeleton__text", true);
			toggle_class(p, "bx--skeleton__heading", /*heading*/ ctx[1]);
			set_style(p, "width", /*width*/ ctx[3]);
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*heading*/ 2) {
				toggle_class(p, "bx--skeleton__heading", /*heading*/ ctx[1]);
			}

			if (dirty & /*lines, widthPx, widthNum, width*/ 57) {
				set_style(p, "width", /*width*/ ctx[3]);
			}
		},
		d(detaching) {
			if (detaching) detach(p);
		}
	};
}

function create_fragment$8(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*paragraph*/ ctx[2]) return create_if_block$6;
		return create_else_block$3;
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
		p(ctx, [dirty]) {
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
		i: noop,
		o: noop,
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$8($$self, $$props, $$invalidate) {
	let widthNum;
	let widthPx;
	const omit_props_names = ["lines","heading","paragraph","width"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { lines = 3 } = $$props;
	let { heading = false } = $$props;
	let { paragraph = false } = $$props;
	let { width = "100%" } = $$props;
	const RANDOM = [0.973, 0.153, 0.567];

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler(event) {
		bubble.call(this, $$self, event);
	}

	function click_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	const func = (_, i) => {
		const min = widthPx ? widthNum - 75 : 0;
		const max = widthPx ? widthNum : 75;
		const rand = Math.floor(RANDOM[i % 3] * (max - min + 1)) + min + "px";
		return widthPx ? rand : `calc(${width} - ${rand})`;
	};

	$$self.$$set = $$new_props => {
		$$props = assign(assign({}, $$props), exclude_internal_props($$new_props));
		$$invalidate(7, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('lines' in $$new_props) $$invalidate(0, lines = $$new_props.lines);
		if ('heading' in $$new_props) $$invalidate(1, heading = $$new_props.heading);
		if ('paragraph' in $$new_props) $$invalidate(2, paragraph = $$new_props.paragraph);
		if ('width' in $$new_props) $$invalidate(3, width = $$new_props.width);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*width*/ 8) {
			$$invalidate(5, widthNum = parseInt(width, 10));
		}

		if ($$self.$$.dirty & /*width*/ 8) {
			$$invalidate(4, widthPx = width.includes("px"));
		}
	};

	return [
		lines,
		heading,
		paragraph,
		width,
		widthPx,
		widthNum,
		RANDOM,
		$$restProps,
		click_handler,
		mouseover_handler,
		mouseenter_handler,
		mouseleave_handler,
		click_handler_1,
		mouseover_handler_1,
		mouseenter_handler_1,
		mouseleave_handler_1,
		func
	];
}

let Component$8 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$8, create_fragment$8, safe_not_equal, {
			lines: 0,
			heading: 1,
			paragraph: 2,
			width: 3
		});
	}
};

/* generated by Svelte v3.59.1 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i];
	return child_ctx;
}

// (39:2) {#if open}
function create_if_block$5(ctx) {
	let li;
	let span;
	let chevronright;
	let t0;
	let skeletontext0;
	let t1;
	let div;
	let skeletontext1;
	let t2;
	let skeletontext2;
	let t3;
	let skeletontext3;
	let current;
	chevronright = new Component$9({ props: { class: "bx--accordion__arrow" } });
	skeletontext0 = new Component$8({ props: { class: "bx--accordion__title" } });
	skeletontext1 = new Component$8({ props: { width: "90%" } });
	skeletontext2 = new Component$8({ props: { width: "80%" } });
	skeletontext3 = new Component$8({ props: { width: "95%" } });

	return {
		c() {
			li = element("li");
			span = element("span");
			create_component(chevronright.$$.fragment);
			t0 = space();
			create_component(skeletontext0.$$.fragment);
			t1 = space();
			div = element("div");
			create_component(skeletontext1.$$.fragment);
			t2 = space();
			create_component(skeletontext2.$$.fragment);
			t3 = space();
			create_component(skeletontext3.$$.fragment);
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", {});
			var li_nodes = children(li);
			span = claim_element(li_nodes, "SPAN", {});
			var span_nodes = children(span);
			claim_component(chevronright.$$.fragment, span_nodes);
			t0 = claim_space(span_nodes);
			claim_component(skeletontext0.$$.fragment, span_nodes);
			span_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			div = claim_element(li_nodes, "DIV", {});
			var div_nodes = children(div);
			claim_component(skeletontext1.$$.fragment, div_nodes);
			t2 = claim_space(div_nodes);
			claim_component(skeletontext2.$$.fragment, div_nodes);
			t3 = claim_space(div_nodes);
			claim_component(skeletontext3.$$.fragment, div_nodes);
			div_nodes.forEach(detach);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			toggle_class(span, "bx--accordion__heading", true);
			toggle_class(div, "bx--accordion__content", true);
			toggle_class(li, "bx--accordion__item", true);
			toggle_class(li, "bx--accordion__item--active", true);
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, span);
			mount_component(chevronright, span, null);
			append_hydration(span, t0);
			mount_component(skeletontext0, span, null);
			append_hydration(li, t1);
			append_hydration(li, div);
			mount_component(skeletontext1, div, null);
			append_hydration(div, t2);
			mount_component(skeletontext2, div, null);
			append_hydration(div, t3);
			mount_component(skeletontext3, div, null);
			current = true;
		},
		i(local) {
			if (current) return;
			transition_in(chevronright.$$.fragment, local);
			transition_in(skeletontext0.$$.fragment, local);
			transition_in(skeletontext1.$$.fragment, local);
			transition_in(skeletontext2.$$.fragment, local);
			transition_in(skeletontext3.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(chevronright.$$.fragment, local);
			transition_out(skeletontext0.$$.fragment, local);
			transition_out(skeletontext1.$$.fragment, local);
			transition_out(skeletontext2.$$.fragment, local);
			transition_out(skeletontext3.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(chevronright);
			destroy_component(skeletontext0);
			destroy_component(skeletontext1);
			destroy_component(skeletontext2);
			destroy_component(skeletontext3);
		}
	};
}

// (55:2) {#each Array.from({ length: open ? count - 1 : count }, (_, i) => i) as item (item)}
function create_each_block$1(key_1, ctx) {
	let li;
	let span;
	let chevronright;
	let t0;
	let skeletontext;
	let t1;
	let current;
	chevronright = new Component$9({ props: { class: "bx--accordion__arrow" } });
	skeletontext = new Component$8({ props: { class: "bx--accordion__title" } });

	return {
		key: key_1,
		first: null,
		c() {
			li = element("li");
			span = element("span");
			create_component(chevronright.$$.fragment);
			t0 = space();
			create_component(skeletontext.$$.fragment);
			t1 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", {});
			var li_nodes = children(li);
			span = claim_element(li_nodes, "SPAN", {});
			var span_nodes = children(span);
			claim_component(chevronright.$$.fragment, span_nodes);
			t0 = claim_space(span_nodes);
			claim_component(skeletontext.$$.fragment, span_nodes);
			span_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			toggle_class(span, "bx--accordion__heading", true);
			toggle_class(li, "bx--accordion__item", true);
			this.first = li;
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, span);
			mount_component(chevronright, span, null);
			append_hydration(span, t0);
			mount_component(skeletontext, span, null);
			append_hydration(li, t1);
			current = true;
		},
		p(new_ctx, dirty) {
		},
		i(local) {
			if (current) return;
			transition_in(chevronright.$$.fragment, local);
			transition_in(skeletontext.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(chevronright.$$.fragment, local);
			transition_out(skeletontext.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(chevronright);
			destroy_component(skeletontext);
		}
	};
}

function create_fragment$7(ctx) {
	let ul;
	let t;
	let each_blocks = [];
	let each_1_lookup = new Map();
	let current;
	let mounted;
	let dispose;
	let if_block = /*open*/ ctx[3] && create_if_block$5();

	let each_value = Array.from(
		{
			length: /*open*/ ctx[3]
			? /*count*/ ctx[0] - 1
			: /*count*/ ctx[0]
		},
		func
	);

	const get_key = ctx => /*item*/ ctx[9];

	for (let i = 0; i < each_value.length; i += 1) {
		let child_ctx = get_each_context$1(ctx, each_value, i);
		let key = get_key(child_ctx);
		each_1_lookup.set(key, each_blocks[i] = create_each_block$1(key));
	}

	let ul_levels = [/*$$restProps*/ ctx[4]];
	let ul_data = {};

	for (let i = 0; i < ul_levels.length; i += 1) {
		ul_data = assign(ul_data, ul_levels[i]);
	}

	return {
		c() {
			ul = element("ul");
			if (if_block) if_block.c();
			t = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			ul = claim_element(nodes, "UL", {});
			var ul_nodes = children(ul);
			if (if_block) if_block.l(ul_nodes);
			t = claim_space(ul_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_attributes(ul, ul_data);
			toggle_class(ul, "bx--skeleton", true);
			toggle_class(ul, "bx--accordion", true);
			toggle_class(ul, "bx--accordion--start", /*align*/ ctx[1] === "start");
			toggle_class(ul, "bx--accordion--end", /*align*/ ctx[1] === "end");
			toggle_class(ul, "bx--accordion--sm", /*size*/ ctx[2] === "sm");
			toggle_class(ul, "bx--accordion--xl", /*size*/ ctx[2] === "xl");
		},
		m(target, anchor) {
			insert_hydration(target, ul, anchor);
			if (if_block) if_block.m(ul, null);
			append_hydration(ul, t);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;

			if (!mounted) {
				dispose = [
					listen(ul, "click", /*click_handler*/ ctx[5]),
					listen(ul, "mouseover", /*mouseover_handler*/ ctx[6]),
					listen(ul, "mouseenter", /*mouseenter_handler*/ ctx[7]),
					listen(ul, "mouseleave", /*mouseleave_handler*/ ctx[8])
				];

				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (/*open*/ ctx[3]) {
				if (if_block) {
					if (dirty & /*open*/ 8) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block$5();
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(ul, t);
				}
			} else if (if_block) {
				group_outros();

				transition_out(if_block, 1, 1, () => {
					if_block = null;
				});

				check_outros();
			}

			if (dirty & /*open, count*/ 9) {
				each_value = Array.from(
					{
						length: /*open*/ ctx[3]
						? /*count*/ ctx[0] - 1
						: /*count*/ ctx[0]
					},
					func
				);

				group_outros();
				each_blocks = update_keyed_each(each_blocks, dirty, get_key, 1, ctx, each_value, each_1_lookup, ul, outro_and_destroy_block, create_each_block$1, null, get_each_context$1);
				check_outros();
			}

			set_attributes(ul, ul_data = get_spread_update(ul_levels, [dirty & /*$$restProps*/ 16 && /*$$restProps*/ ctx[4]]));
			toggle_class(ul, "bx--skeleton", true);
			toggle_class(ul, "bx--accordion", true);
			toggle_class(ul, "bx--accordion--start", /*align*/ ctx[1] === "start");
			toggle_class(ul, "bx--accordion--end", /*align*/ ctx[1] === "end");
			toggle_class(ul, "bx--accordion--sm", /*size*/ ctx[2] === "sm");
			toggle_class(ul, "bx--accordion--xl", /*size*/ ctx[2] === "xl");
		},
		i(local) {
			if (current) return;
			transition_in(if_block);

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			transition_out(if_block);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(ul);
			if (if_block) if_block.d();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].d();
			}

			mounted = false;
			run_all(dispose);
		}
	};
}

const func = (_, i) => i;

function instance$7($$self, $$props, $$invalidate) {
	const omit_props_names = ["count","align","size","open"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { count = 4 } = $$props;
	let { align = "end" } = $$props;
	let { size = undefined } = $$props;
	let { open = true } = $$props;

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler(event) {
		bubble.call(this, $$self, event);
	}

	$$self.$$set = $$new_props => {
		$$props = assign(assign({}, $$props), exclude_internal_props($$new_props));
		$$invalidate(4, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('count' in $$new_props) $$invalidate(0, count = $$new_props.count);
		if ('align' in $$new_props) $$invalidate(1, align = $$new_props.align);
		if ('size' in $$new_props) $$invalidate(2, size = $$new_props.size);
		if ('open' in $$new_props) $$invalidate(3, open = $$new_props.open);
	};

	return [
		count,
		align,
		size,
		open,
		$$restProps,
		click_handler,
		mouseover_handler,
		mouseenter_handler,
		mouseleave_handler
	];
}

let Component$7 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$7, create_fragment$7, safe_not_equal, { count: 0, align: 1, size: 2, open: 3 });
	}
};

/* generated by Svelte v3.59.1 */

function create_else_block$2(ctx) {
	let ul;
	let current;
	let mounted;
	let dispose;
	const default_slot_template = /*#slots*/ ctx[6].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[5], null);
	let ul_levels = [/*$$restProps*/ ctx[3]];
	let ul_data = {};

	for (let i = 0; i < ul_levels.length; i += 1) {
		ul_data = assign(ul_data, ul_levels[i]);
	}

	return {
		c() {
			ul = element("ul");
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			ul = claim_element(nodes, "UL", {});
			var ul_nodes = children(ul);
			if (default_slot) default_slot.l(ul_nodes);
			ul_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_attributes(ul, ul_data);
			toggle_class(ul, "bx--accordion", true);
			toggle_class(ul, "bx--accordion--start", /*align*/ ctx[0] === "start");
			toggle_class(ul, "bx--accordion--end", /*align*/ ctx[0] === "end");
			toggle_class(ul, "bx--accordion--sm", /*size*/ ctx[1] === "sm");
			toggle_class(ul, "bx--accordion--xl", /*size*/ ctx[1] === "xl");
		},
		m(target, anchor) {
			insert_hydration(target, ul, anchor);

			if (default_slot) {
				default_slot.m(ul, null);
			}

			current = true;

			if (!mounted) {
				dispose = [
					listen(ul, "click", /*click_handler_1*/ ctx[7]),
					listen(ul, "mouseover", /*mouseover_handler_1*/ ctx[8]),
					listen(ul, "mouseenter", /*mouseenter_handler_1*/ ctx[9]),
					listen(ul, "mouseleave", /*mouseleave_handler_1*/ ctx[10])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 32)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[5],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[5])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[5], dirty, null),
						null
					);
				}
			}

			set_attributes(ul, ul_data = get_spread_update(ul_levels, [dirty & /*$$restProps*/ 8 && /*$$restProps*/ ctx[3]]));
			toggle_class(ul, "bx--accordion", true);
			toggle_class(ul, "bx--accordion--start", /*align*/ ctx[0] === "start");
			toggle_class(ul, "bx--accordion--end", /*align*/ ctx[0] === "end");
			toggle_class(ul, "bx--accordion--sm", /*size*/ ctx[1] === "sm");
			toggle_class(ul, "bx--accordion--xl", /*size*/ ctx[1] === "xl");
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
			if (detaching) detach(ul);
			if (default_slot) default_slot.d(detaching);
			mounted = false;
			run_all(dispose);
		}
	};
}

// (34:0) {#if skeleton}
function create_if_block$4(ctx) {
	let accordionskeleton;
	let current;
	const accordionskeleton_spread_levels = [/*$$restProps*/ ctx[3], { align: /*align*/ ctx[0] }, { size: /*size*/ ctx[1] }];
	let accordionskeleton_props = {};

	for (let i = 0; i < accordionskeleton_spread_levels.length; i += 1) {
		accordionskeleton_props = assign(accordionskeleton_props, accordionskeleton_spread_levels[i]);
	}

	accordionskeleton = new Component$7({ props: accordionskeleton_props });
	accordionskeleton.$on("click", /*click_handler*/ ctx[11]);
	accordionskeleton.$on("mouseover", /*mouseover_handler*/ ctx[12]);
	accordionskeleton.$on("mouseenter", /*mouseenter_handler*/ ctx[13]);
	accordionskeleton.$on("mouseleave", /*mouseleave_handler*/ ctx[14]);

	return {
		c() {
			create_component(accordionskeleton.$$.fragment);
		},
		l(nodes) {
			claim_component(accordionskeleton.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(accordionskeleton, target, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const accordionskeleton_changes = (dirty & /*$$restProps, align, size*/ 11)
			? get_spread_update(accordionskeleton_spread_levels, [
					dirty & /*$$restProps*/ 8 && get_spread_object(/*$$restProps*/ ctx[3]),
					dirty & /*align*/ 1 && { align: /*align*/ ctx[0] },
					dirty & /*size*/ 2 && { size: /*size*/ ctx[1] }
				])
			: {};

			accordionskeleton.$set(accordionskeleton_changes);
		},
		i(local) {
			if (current) return;
			transition_in(accordionskeleton.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(accordionskeleton.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(accordionskeleton, detaching);
		}
	};
}

function create_fragment$6(ctx) {
	let current_block_type_index;
	let if_block;
	let if_block_anchor;
	let current;
	const if_block_creators = [create_if_block$4, create_else_block$2];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*skeleton*/ ctx[2]) return 0;
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

function instance$6($$self, $$props, $$invalidate) {
	const omit_props_names = ["align","size","disabled","skeleton"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	let { align = "end" } = $$props;
	let { size = undefined } = $$props;
	let { disabled = false } = $$props;
	let { skeleton = false } = $$props;
	const disableItems = writable(disabled);
	setContext("Accordion", { disableItems });

	function click_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler(event) {
		bubble.call(this, $$self, event);
	}

	$$self.$$set = $$new_props => {
		$$props = assign(assign({}, $$props), exclude_internal_props($$new_props));
		$$invalidate(3, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('align' in $$new_props) $$invalidate(0, align = $$new_props.align);
		if ('size' in $$new_props) $$invalidate(1, size = $$new_props.size);
		if ('disabled' in $$new_props) $$invalidate(4, disabled = $$new_props.disabled);
		if ('skeleton' in $$new_props) $$invalidate(2, skeleton = $$new_props.skeleton);
		if ('$$scope' in $$new_props) $$invalidate(5, $$scope = $$new_props.$$scope);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*disabled*/ 16) {
			disableItems.set(disabled);
		}
	};

	return [
		align,
		size,
		skeleton,
		$$restProps,
		disabled,
		$$scope,
		slots,
		click_handler_1,
		mouseover_handler_1,
		mouseenter_handler_1,
		mouseleave_handler_1,
		click_handler,
		mouseover_handler,
		mouseenter_handler,
		mouseleave_handler
	];
}

let Component$6 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$6, safe_not_equal, {
			align: 0,
			size: 1,
			disabled: 4,
			skeleton: 2
		});
	}
};

/* generated by Svelte v3.59.1 */
const get_title_slot_changes = dirty => ({});
const get_title_slot_context = ctx => ({});

// (73:25) {title}
function fallback_block$1(ctx) {
	let t;

	return {
		c() {
			t = text(/*title*/ ctx[2]);
		},
		l(nodes) {
			t = claim_text(nodes, /*title*/ ctx[2]);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*title*/ 4) set_data(t, /*title*/ ctx[2]);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

function create_fragment$5(ctx) {
	let li;
	let button;
	let chevronright;
	let t0;
	let div0;
	let t1;
	let div1;
	let current;
	let mounted;
	let dispose;

	chevronright = new Component$9({
			props: {
				class: "bx--accordion__arrow",
				"aria-label": /*iconDescription*/ ctx[3]
			}
		});

	const title_slot_template = /*#slots*/ ctx[7].title;
	const title_slot = create_slot(title_slot_template, ctx, /*$$scope*/ ctx[6], get_title_slot_context);
	const title_slot_or_fallback = title_slot || fallback_block$1(ctx);
	const default_slot_template = /*#slots*/ ctx[7].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[6], null);
	let li_levels = [/*$$restProps*/ ctx[5]];
	let li_data = {};

	for (let i = 0; i < li_levels.length; i += 1) {
		li_data = assign(li_data, li_levels[i]);
	}

	return {
		c() {
			li = element("li");
			button = element("button");
			create_component(chevronright.$$.fragment);
			t0 = space();
			div0 = element("div");
			if (title_slot_or_fallback) title_slot_or_fallback.c();
			t1 = space();
			div1 = element("div");
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", {});
			var li_nodes = children(li);

			button = claim_element(li_nodes, "BUTTON", {
				type: true,
				title: true,
				"aria-expanded": true
			});

			var button_nodes = children(button);
			claim_component(chevronright.$$.fragment, button_nodes);
			t0 = claim_space(button_nodes);
			div0 = claim_element(button_nodes, "DIV", {});
			var div0_nodes = children(div0);
			if (title_slot_or_fallback) title_slot_or_fallback.l(div0_nodes);
			div0_nodes.forEach(detach);
			button_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			div1 = claim_element(li_nodes, "DIV", {});
			var div1_nodes = children(div1);
			if (default_slot) default_slot.l(div1_nodes);
			div1_nodes.forEach(detach);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			toggle_class(div0, "bx--accordion__title", true);
			attr(button, "type", "button");
			attr(button, "title", /*iconDescription*/ ctx[3]);
			attr(button, "aria-expanded", /*open*/ ctx[0]);
			button.disabled = /*disabled*/ ctx[1];
			toggle_class(button, "bx--accordion__heading", true);
			toggle_class(div1, "bx--accordion__content", true);
			set_attributes(li, li_data);
			toggle_class(li, "bx--accordion__item", true);
			toggle_class(li, "bx--accordion__item--active", /*open*/ ctx[0]);
			toggle_class(li, "bx--accordion__item--disabled", /*disabled*/ ctx[1]);
			toggle_class(li, "bx--accordion__item--expanding", /*animation*/ ctx[4] === "expanding");
			toggle_class(li, "bx--accordion__item--collapsing", /*animation*/ ctx[4] === "collapsing");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, button);
			mount_component(chevronright, button, null);
			append_hydration(button, t0);
			append_hydration(button, div0);

			if (title_slot_or_fallback) {
				title_slot_or_fallback.m(div0, null);
			}

			append_hydration(li, t1);
			append_hydration(li, div1);

			if (default_slot) {
				default_slot.m(div1, null);
			}

			current = true;

			if (!mounted) {
				dispose = [
					listen(button, "click", /*click_handler*/ ctx[9]),
					listen(button, "click", /*click_handler_1*/ ctx[14]),
					listen(button, "mouseover", /*mouseover_handler*/ ctx[10]),
					listen(button, "mouseenter", /*mouseenter_handler*/ ctx[11]),
					listen(button, "mouseleave", /*mouseleave_handler*/ ctx[12]),
					listen(button, "keydown", /*keydown_handler*/ ctx[13]),
					listen(button, "keydown", /*keydown_handler_1*/ ctx[15]),
					listen(li, "animationend", /*animationend_handler*/ ctx[8]),
					listen(li, "animationend", /*animationend_handler_1*/ ctx[16])
				];

				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			const chevronright_changes = {};
			if (dirty & /*iconDescription*/ 8) chevronright_changes["aria-label"] = /*iconDescription*/ ctx[3];
			chevronright.$set(chevronright_changes);

			if (title_slot) {
				if (title_slot.p && (!current || dirty & /*$$scope*/ 64)) {
					update_slot_base(
						title_slot,
						title_slot_template,
						ctx,
						/*$$scope*/ ctx[6],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[6])
						: get_slot_changes(title_slot_template, /*$$scope*/ ctx[6], dirty, get_title_slot_changes),
						get_title_slot_context
					);
				}
			} else {
				if (title_slot_or_fallback && title_slot_or_fallback.p && (!current || dirty & /*title*/ 4)) {
					title_slot_or_fallback.p(ctx, !current ? -1 : dirty);
				}
			}

			if (!current || dirty & /*iconDescription*/ 8) {
				attr(button, "title", /*iconDescription*/ ctx[3]);
			}

			if (!current || dirty & /*open*/ 1) {
				attr(button, "aria-expanded", /*open*/ ctx[0]);
			}

			if (!current || dirty & /*disabled*/ 2) {
				button.disabled = /*disabled*/ ctx[1];
			}

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

			set_attributes(li, li_data = get_spread_update(li_levels, [dirty & /*$$restProps*/ 32 && /*$$restProps*/ ctx[5]]));
			toggle_class(li, "bx--accordion__item", true);
			toggle_class(li, "bx--accordion__item--active", /*open*/ ctx[0]);
			toggle_class(li, "bx--accordion__item--disabled", /*disabled*/ ctx[1]);
			toggle_class(li, "bx--accordion__item--expanding", /*animation*/ ctx[4] === "expanding");
			toggle_class(li, "bx--accordion__item--collapsing", /*animation*/ ctx[4] === "collapsing");
		},
		i(local) {
			if (current) return;
			transition_in(chevronright.$$.fragment, local);
			transition_in(title_slot_or_fallback, local);
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(chevronright.$$.fragment, local);
			transition_out(title_slot_or_fallback, local);
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(chevronright);
			if (title_slot_or_fallback) title_slot_or_fallback.d(detaching);
			if (default_slot) default_slot.d(detaching);
			mounted = false;
			run_all(dispose);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	const omit_props_names = ["title","open","disabled","iconDescription"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	let { title = "title" } = $$props;
	let { open = false } = $$props;
	let { disabled = false } = $$props;
	let { iconDescription = "Expand/Collapse" } = $$props;
	let initialDisabled = disabled;
	const ctx = getContext("Accordion");

	const unsubscribe = ctx.disableItems.subscribe(value => {
		if (!value && initialDisabled) return;
		$$invalidate(1, disabled = value);
	});

	let animation = undefined;

	onMount(() => {
		return () => {
			unsubscribe();
		};
	});

	function animationend_handler(event) {
		bubble.call(this, $$self, event);
	}

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler(event) {
		bubble.call(this, $$self, event);
	}

	function keydown_handler(event) {
		bubble.call(this, $$self, event);
	}

	const click_handler_1 = () => {
		$$invalidate(0, open = !open);
		$$invalidate(4, animation = open ? "expanding" : "collapsing");
	};

	const keydown_handler_1 = ({ key }) => {
		if (open && key === "Escape") {
			$$invalidate(0, open = false);
		}
	};

	const animationend_handler_1 = () => {
		$$invalidate(4, animation = undefined);
	};

	$$self.$$set = $$new_props => {
		$$props = assign(assign({}, $$props), exclude_internal_props($$new_props));
		$$invalidate(5, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('title' in $$new_props) $$invalidate(2, title = $$new_props.title);
		if ('open' in $$new_props) $$invalidate(0, open = $$new_props.open);
		if ('disabled' in $$new_props) $$invalidate(1, disabled = $$new_props.disabled);
		if ('iconDescription' in $$new_props) $$invalidate(3, iconDescription = $$new_props.iconDescription);
		if ('$$scope' in $$new_props) $$invalidate(6, $$scope = $$new_props.$$scope);
	};

	return [
		open,
		disabled,
		title,
		iconDescription,
		animation,
		$$restProps,
		$$scope,
		slots,
		animationend_handler,
		click_handler,
		mouseover_handler,
		mouseenter_handler,
		mouseleave_handler,
		keydown_handler,
		click_handler_1,
		keydown_handler_1,
		animationend_handler_1
	];
}

let Component$5 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			title: 2,
			open: 0,
			disabled: 1,
			iconDescription: 3
		});
	}
};

/* generated by Svelte v3.59.1 */

function create_else_block$1(ctx) {
	let div;
	let mounted;
	let dispose;
	let div_levels = [/*$$restProps*/ ctx[2]];
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
			div = claim_element(nodes, "DIV", {});
			children(div).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(div, div_data);
			toggle_class(div, "bx--skeleton", true);
			toggle_class(div, "bx--btn", true);
			toggle_class(div, "bx--btn--field", /*size*/ ctx[1] === "field");
			toggle_class(div, "bx--btn--sm", /*size*/ ctx[1] === "small");
			toggle_class(div, "bx--btn--lg", /*size*/ ctx[1] === "lg");
			toggle_class(div, "bx--btn--xl", /*size*/ ctx[1] === "xl");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);

			if (!mounted) {
				dispose = [
					listen(div, "click", /*click_handler_1*/ ctx[9]),
					listen(div, "focus", /*focus_handler_1*/ ctx[10]),
					listen(div, "blur", /*blur_handler_1*/ ctx[11]),
					listen(div, "mouseover", /*mouseover_handler_1*/ ctx[12]),
					listen(div, "mouseenter", /*mouseenter_handler_1*/ ctx[13]),
					listen(div, "mouseleave", /*mouseleave_handler_1*/ ctx[14])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			set_attributes(div, div_data = get_spread_update(div_levels, [dirty & /*$$restProps*/ 4 && /*$$restProps*/ ctx[2]]));
			toggle_class(div, "bx--skeleton", true);
			toggle_class(div, "bx--btn", true);
			toggle_class(div, "bx--btn--field", /*size*/ ctx[1] === "field");
			toggle_class(div, "bx--btn--sm", /*size*/ ctx[1] === "small");
			toggle_class(div, "bx--btn--lg", /*size*/ ctx[1] === "lg");
			toggle_class(div, "bx--btn--xl", /*size*/ ctx[1] === "xl");
		},
		d(detaching) {
			if (detaching) detach(div);
			mounted = false;
			run_all(dispose);
		}
	};
}

// (16:0) {#if href}
function create_if_block$3(ctx) {
	let a;
	let t_value = "" + "";
	let t;
	let a_rel_value;
	let mounted;
	let dispose;

	let a_levels = [
		{ href: /*href*/ ctx[0] },
		{
			rel: a_rel_value = /*$$restProps*/ ctx[2].target === "_blank"
			? "noopener noreferrer"
			: undefined
		},
		{ role: "button" },
		/*$$restProps*/ ctx[2]
	];

	let a_data = {};

	for (let i = 0; i < a_levels.length; i += 1) {
		a_data = assign(a_data, a_levels[i]);
	}

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, rel: true, role: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_attributes(a, a_data);
			toggle_class(a, "bx--skeleton", true);
			toggle_class(a, "bx--btn", true);
			toggle_class(a, "bx--btn--field", /*size*/ ctx[1] === "field");
			toggle_class(a, "bx--btn--sm", /*size*/ ctx[1] === "small");
			toggle_class(a, "bx--btn--lg", /*size*/ ctx[1] === "lg");
			toggle_class(a, "bx--btn--xl", /*size*/ ctx[1] === "xl");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);

			if (!mounted) {
				dispose = [
					listen(a, "click", /*click_handler*/ ctx[3]),
					listen(a, "focus", /*focus_handler*/ ctx[4]),
					listen(a, "blur", /*blur_handler*/ ctx[5]),
					listen(a, "mouseover", /*mouseover_handler*/ ctx[6]),
					listen(a, "mouseenter", /*mouseenter_handler*/ ctx[7]),
					listen(a, "mouseleave", /*mouseleave_handler*/ ctx[8])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			set_attributes(a, a_data = get_spread_update(a_levels, [
				dirty & /*href*/ 1 && { href: /*href*/ ctx[0] },
				dirty & /*$$restProps*/ 4 && a_rel_value !== (a_rel_value = /*$$restProps*/ ctx[2].target === "_blank"
				? "noopener noreferrer"
				: undefined) && { rel: a_rel_value },
				{ role: "button" },
				dirty & /*$$restProps*/ 4 && /*$$restProps*/ ctx[2]
			]));

			toggle_class(a, "bx--skeleton", true);
			toggle_class(a, "bx--btn", true);
			toggle_class(a, "bx--btn--field", /*size*/ ctx[1] === "field");
			toggle_class(a, "bx--btn--sm", /*size*/ ctx[1] === "small");
			toggle_class(a, "bx--btn--lg", /*size*/ ctx[1] === "lg");
			toggle_class(a, "bx--btn--xl", /*size*/ ctx[1] === "xl");
		},
		d(detaching) {
			if (detaching) detach(a);
			mounted = false;
			run_all(dispose);
		}
	};
}

function create_fragment$4(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*href*/ ctx[0]) return create_if_block$3;
		return create_else_block$1;
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
		p(ctx, [dirty]) {
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
		i: noop,
		o: noop,
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	const omit_props_names = ["href","size"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { href = undefined } = $$props;
	let { size = "default" } = $$props;

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	function focus_handler(event) {
		bubble.call(this, $$self, event);
	}

	function blur_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler(event) {
		bubble.call(this, $$self, event);
	}

	function click_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function focus_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function blur_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	$$self.$$set = $$new_props => {
		$$props = assign(assign({}, $$props), exclude_internal_props($$new_props));
		$$invalidate(2, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('href' in $$new_props) $$invalidate(0, href = $$new_props.href);
		if ('size' in $$new_props) $$invalidate(1, size = $$new_props.size);
	};

	return [
		href,
		size,
		$$restProps,
		click_handler,
		focus_handler,
		blur_handler,
		mouseover_handler,
		mouseenter_handler,
		mouseleave_handler,
		click_handler_1,
		focus_handler_1,
		blur_handler_1,
		mouseover_handler_1,
		mouseenter_handler_1,
		mouseleave_handler_1
	];
}

let Component$4 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$4, create_fragment$4, safe_not_equal, { href: 0, size: 1 });
	}
};

/* generated by Svelte v3.59.1 */
const get_icon_slot_spread_changes_1 = dirty => dirty[0] & /*iconProps*/ 1024;
const get_icon_slot_changes_1 = dirty => ({ style: dirty[0] & /*hasIconOnly*/ 256 });

const get_icon_slot_context_1 = ctx => ({
	style: /*hasIconOnly*/ ctx[8] ? "margin-left: 0" : undefined,
	.../*iconProps*/ ctx[10]
});

const get_icon_slot_spread_changes = dirty => dirty[0] & /*iconProps*/ 1024;
const get_icon_slot_changes = dirty => ({ style: dirty[0] & /*hasIconOnly*/ 256 });

const get_icon_slot_context = ctx => ({
	style: /*hasIconOnly*/ ctx[8] ? "margin-left: 0" : undefined,
	.../*iconProps*/ ctx[10]
});

const get_default_slot_changes = dirty => ({ props: dirty[0] & /*buttonProps*/ 512 });
const get_default_slot_context = ctx => ({ props: /*buttonProps*/ ctx[9] });

// (183:0) {:else}
function create_else_block(ctx) {
	let button;
	let t0;
	let t1;
	let current_block_type_index;
	let if_block1;
	let current;
	let mounted;
	let dispose;
	let if_block0 = /*hasIconOnly*/ ctx[8] && create_if_block_8(ctx);
	const default_slot_template = /*#slots*/ ctx[21].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[20], null);
	const if_block_creators = [create_if_block_6$1, create_if_block_7];
	const if_blocks = [];

	function select_block_type_2(ctx, dirty) {
		if (/*$$slots*/ ctx[12].icon) return 0;
		if (/*icon*/ ctx[2]) return 1;
		return -1;
	}

	if (~(current_block_type_index = select_block_type_2(ctx))) {
		if_block1 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
	}

	let button_levels = [/*buttonProps*/ ctx[9]];
	let button_data = {};

	for (let i = 0; i < button_levels.length; i += 1) {
		button_data = assign(button_data, button_levels[i]);
	}

	return {
		c() {
			button = element("button");
			if (if_block0) if_block0.c();
			t0 = space();
			if (default_slot) default_slot.c();
			t1 = space();
			if (if_block1) if_block1.c();
			this.h();
		},
		l(nodes) {
			button = claim_element(nodes, "BUTTON", {});
			var button_nodes = children(button);
			if (if_block0) if_block0.l(button_nodes);
			t0 = claim_space(button_nodes);
			if (default_slot) default_slot.l(button_nodes);
			t1 = claim_space(button_nodes);
			if (if_block1) if_block1.l(button_nodes);
			button_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_attributes(button, button_data);
		},
		m(target, anchor) {
			insert_hydration(target, button, anchor);
			if (if_block0) if_block0.m(button, null);
			append_hydration(button, t0);

			if (default_slot) {
				default_slot.m(button, null);
			}

			append_hydration(button, t1);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].m(button, null);
			}

			if (button.autofocus) button.focus();
			/*button_binding*/ ctx[41](button);
			current = true;

			if (!mounted) {
				dispose = [
					listen(button, "click", /*click_handler_2*/ ctx[28]),
					listen(button, "focus", /*focus_handler_2*/ ctx[29]),
					listen(button, "blur", /*blur_handler_2*/ ctx[30]),
					listen(button, "mouseover", /*mouseover_handler_2*/ ctx[31]),
					listen(button, "mouseenter", /*mouseenter_handler_2*/ ctx[32]),
					listen(button, "mouseleave", /*mouseleave_handler_2*/ ctx[33])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (/*hasIconOnly*/ ctx[8]) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_8(ctx);
					if_block0.c();
					if_block0.m(button, t0);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (default_slot) {
				if (default_slot.p && (!current || dirty[0] & /*$$scope*/ 1048576)) {
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

			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type_2(ctx);

			if (current_block_type_index === previous_block_index) {
				if (~current_block_type_index) {
					if_blocks[current_block_type_index].p(ctx, dirty);
				}
			} else {
				if (if_block1) {
					group_outros();

					transition_out(if_blocks[previous_block_index], 1, 1, () => {
						if_blocks[previous_block_index] = null;
					});

					check_outros();
				}

				if (~current_block_type_index) {
					if_block1 = if_blocks[current_block_type_index];

					if (!if_block1) {
						if_block1 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
						if_block1.c();
					} else {
						if_block1.p(ctx, dirty);
					}

					transition_in(if_block1, 1);
					if_block1.m(button, null);
				} else {
					if_block1 = null;
				}
			}

			set_attributes(button, button_data = get_spread_update(button_levels, [dirty[0] & /*buttonProps*/ 512 && /*buttonProps*/ ctx[9]]));
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			transition_in(if_block1);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			transition_out(if_block1);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(button);
			if (if_block0) if_block0.d();
			if (default_slot) default_slot.d(detaching);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].d();
			}

			/*button_binding*/ ctx[41](null);
			mounted = false;
			run_all(dispose);
		}
	};
}

// (152:28) 
function create_if_block_2$1(ctx) {
	let a;
	let t0;
	let t1;
	let current_block_type_index;
	let if_block1;
	let current;
	let mounted;
	let dispose;
	let if_block0 = /*hasIconOnly*/ ctx[8] && create_if_block_5$1(ctx);
	const default_slot_template = /*#slots*/ ctx[21].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[20], null);
	const if_block_creators = [create_if_block_3$1, create_if_block_4$1];
	const if_blocks = [];

	function select_block_type_1(ctx, dirty) {
		if (/*$$slots*/ ctx[12].icon) return 0;
		if (/*icon*/ ctx[2]) return 1;
		return -1;
	}

	if (~(current_block_type_index = select_block_type_1(ctx))) {
		if_block1 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
	}

	let a_levels = [/*buttonProps*/ ctx[9]];
	let a_data = {};

	for (let i = 0; i < a_levels.length; i += 1) {
		a_data = assign(a_data, a_levels[i]);
	}

	return {
		c() {
			a = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			if (default_slot) default_slot.c();
			t1 = space();
			if (if_block1) if_block1.c();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", {});
			var a_nodes = children(a);
			if (if_block0) if_block0.l(a_nodes);
			t0 = claim_space(a_nodes);
			if (default_slot) default_slot.l(a_nodes);
			t1 = claim_space(a_nodes);
			if (if_block1) if_block1.l(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_attributes(a, a_data);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			if (if_block0) if_block0.m(a, null);
			append_hydration(a, t0);

			if (default_slot) {
				default_slot.m(a, null);
			}

			append_hydration(a, t1);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].m(a, null);
			}

			/*a_binding*/ ctx[40](a);
			current = true;

			if (!mounted) {
				dispose = [
					listen(a, "click", /*click_handler_1*/ ctx[22]),
					listen(a, "focus", /*focus_handler_1*/ ctx[23]),
					listen(a, "blur", /*blur_handler_1*/ ctx[24]),
					listen(a, "mouseover", /*mouseover_handler_1*/ ctx[25]),
					listen(a, "mouseenter", /*mouseenter_handler_1*/ ctx[26]),
					listen(a, "mouseleave", /*mouseleave_handler_1*/ ctx[27])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (/*hasIconOnly*/ ctx[8]) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_5$1(ctx);
					if_block0.c();
					if_block0.m(a, t0);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (default_slot) {
				if (default_slot.p && (!current || dirty[0] & /*$$scope*/ 1048576)) {
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

			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type_1(ctx);

			if (current_block_type_index === previous_block_index) {
				if (~current_block_type_index) {
					if_blocks[current_block_type_index].p(ctx, dirty);
				}
			} else {
				if (if_block1) {
					group_outros();

					transition_out(if_blocks[previous_block_index], 1, 1, () => {
						if_blocks[previous_block_index] = null;
					});

					check_outros();
				}

				if (~current_block_type_index) {
					if_block1 = if_blocks[current_block_type_index];

					if (!if_block1) {
						if_block1 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
						if_block1.c();
					} else {
						if_block1.p(ctx, dirty);
					}

					transition_in(if_block1, 1);
					if_block1.m(a, null);
				} else {
					if_block1 = null;
				}
			}

			set_attributes(a, a_data = get_spread_update(a_levels, [dirty[0] & /*buttonProps*/ 512 && /*buttonProps*/ ctx[9]]));
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			transition_in(if_block1);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			transition_out(if_block1);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			if (if_block0) if_block0.d();
			if (default_slot) default_slot.d(detaching);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].d();
			}

			/*a_binding*/ ctx[40](null);
			mounted = false;
			run_all(dispose);
		}
	};
}

// (150:13) 
function create_if_block_1$1(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[21].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[20], get_default_slot_context);

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
				if (default_slot.p && (!current || dirty[0] & /*$$scope, buttonProps*/ 1049088)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[20],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[20])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[20], dirty, get_default_slot_changes),
						get_default_slot_context
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

// (137:0) {#if skeleton}
function create_if_block$2(ctx) {
	let buttonskeleton;
	let current;

	const buttonskeleton_spread_levels = [
		{ href: /*href*/ ctx[7] },
		{ size: /*size*/ ctx[1] },
		/*$$restProps*/ ctx[11],
		{
			style: /*hasIconOnly*/ ctx[8] && "width: 3rem;"
		}
	];

	let buttonskeleton_props = {};

	for (let i = 0; i < buttonskeleton_spread_levels.length; i += 1) {
		buttonskeleton_props = assign(buttonskeleton_props, buttonskeleton_spread_levels[i]);
	}

	buttonskeleton = new Component$4({ props: buttonskeleton_props });
	buttonskeleton.$on("click", /*click_handler*/ ctx[34]);
	buttonskeleton.$on("focus", /*focus_handler*/ ctx[35]);
	buttonskeleton.$on("blur", /*blur_handler*/ ctx[36]);
	buttonskeleton.$on("mouseover", /*mouseover_handler*/ ctx[37]);
	buttonskeleton.$on("mouseenter", /*mouseenter_handler*/ ctx[38]);
	buttonskeleton.$on("mouseleave", /*mouseleave_handler*/ ctx[39]);

	return {
		c() {
			create_component(buttonskeleton.$$.fragment);
		},
		l(nodes) {
			claim_component(buttonskeleton.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(buttonskeleton, target, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const buttonskeleton_changes = (dirty[0] & /*href, size, $$restProps, hasIconOnly*/ 2434)
			? get_spread_update(buttonskeleton_spread_levels, [
					dirty[0] & /*href*/ 128 && { href: /*href*/ ctx[7] },
					dirty[0] & /*size*/ 2 && { size: /*size*/ ctx[1] },
					dirty[0] & /*$$restProps*/ 2048 && get_spread_object(/*$$restProps*/ ctx[11]),
					dirty[0] & /*hasIconOnly*/ 256 && {
						style: /*hasIconOnly*/ ctx[8] && "width: 3rem;"
					}
				])
			: {};

			buttonskeleton.$set(buttonskeleton_changes);
		},
		i(local) {
			if (current) return;
			transition_in(buttonskeleton.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(buttonskeleton.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(buttonskeleton, detaching);
		}
	};
}

// (194:4) {#if hasIconOnly}
function create_if_block_8(ctx) {
	let span;
	let t;

	return {
		c() {
			span = element("span");
			t = text(/*iconDescription*/ ctx[3]);
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			var span_nodes = children(span);
			t = claim_text(span_nodes, /*iconDescription*/ ctx[3]);
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			toggle_class(span, "bx--assistive-text", true);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*iconDescription*/ 8) set_data(t, /*iconDescription*/ ctx[3]);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (204:19) 
function create_if_block_7(ctx) {
	let switch_instance;
	let switch_instance_anchor;
	let current;

	const switch_instance_spread_levels = [
		{
			style: /*hasIconOnly*/ ctx[8] ? "margin-left: 0" : undefined
		},
		/*iconProps*/ ctx[10]
	];

	var switch_value = /*icon*/ ctx[2];

	function switch_props(ctx) {
		let switch_instance_props = {};

		for (let i = 0; i < switch_instance_spread_levels.length; i += 1) {
			switch_instance_props = assign(switch_instance_props, switch_instance_spread_levels[i]);
		}

		return { props: switch_instance_props };
	}

	if (switch_value) {
		switch_instance = construct_svelte_component(switch_value, switch_props());
	}

	return {
		c() {
			if (switch_instance) create_component(switch_instance.$$.fragment);
			switch_instance_anchor = empty();
		},
		l(nodes) {
			if (switch_instance) claim_component(switch_instance.$$.fragment, nodes);
			switch_instance_anchor = empty();
		},
		m(target, anchor) {
			if (switch_instance) mount_component(switch_instance, target, anchor);
			insert_hydration(target, switch_instance_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const switch_instance_changes = (dirty[0] & /*hasIconOnly, iconProps*/ 1280)
			? get_spread_update(switch_instance_spread_levels, [
					dirty[0] & /*hasIconOnly*/ 256 && {
						style: /*hasIconOnly*/ ctx[8] ? "margin-left: 0" : undefined
					},
					dirty[0] & /*iconProps*/ 1024 && get_spread_object(/*iconProps*/ ctx[10])
				])
			: {};

			if (dirty[0] & /*icon*/ 4 && switch_value !== (switch_value = /*icon*/ ctx[2])) {
				if (switch_instance) {
					group_outros();
					const old_component = switch_instance;

					transition_out(old_component.$$.fragment, 1, 0, () => {
						destroy_component(old_component, 1);
					});

					check_outros();
				}

				if (switch_value) {
					switch_instance = construct_svelte_component(switch_value, switch_props());
					create_component(switch_instance.$$.fragment);
					transition_in(switch_instance.$$.fragment, 1);
					mount_component(switch_instance, switch_instance_anchor.parentNode, switch_instance_anchor);
				} else {
					switch_instance = null;
				}
			} else if (switch_value) {
				switch_instance.$set(switch_instance_changes);
			}
		},
		i(local) {
			if (current) return;
			if (switch_instance) transition_in(switch_instance.$$.fragment, local);
			current = true;
		},
		o(local) {
			if (switch_instance) transition_out(switch_instance.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(switch_instance_anchor);
			if (switch_instance) destroy_component(switch_instance, detaching);
		}
	};
}

// (198:4) {#if $$slots.icon}
function create_if_block_6$1(ctx) {
	let current;
	const icon_slot_template = /*#slots*/ ctx[21].icon;
	const icon_slot = create_slot(icon_slot_template, ctx, /*$$scope*/ ctx[20], get_icon_slot_context_1);

	return {
		c() {
			if (icon_slot) icon_slot.c();
		},
		l(nodes) {
			if (icon_slot) icon_slot.l(nodes);
		},
		m(target, anchor) {
			if (icon_slot) {
				icon_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (icon_slot) {
				if (icon_slot.p && (!current || dirty[0] & /*$$scope, hasIconOnly, iconProps*/ 1049856)) {
					update_slot_base(
						icon_slot,
						icon_slot_template,
						ctx,
						/*$$scope*/ ctx[20],
						get_icon_slot_spread_changes_1(dirty) || !current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[20])
						: get_slot_changes(icon_slot_template, /*$$scope*/ ctx[20], dirty, get_icon_slot_changes_1),
						get_icon_slot_context_1
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon_slot, local);
			current = true;
		},
		o(local) {
			transition_out(icon_slot, local);
			current = false;
		},
		d(detaching) {
			if (icon_slot) icon_slot.d(detaching);
		}
	};
}

// (165:4) {#if hasIconOnly}
function create_if_block_5$1(ctx) {
	let span;
	let t;

	return {
		c() {
			span = element("span");
			t = text(/*iconDescription*/ ctx[3]);
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			var span_nodes = children(span);
			t = claim_text(span_nodes, /*iconDescription*/ ctx[3]);
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			toggle_class(span, "bx--assistive-text", true);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*iconDescription*/ 8) set_data(t, /*iconDescription*/ ctx[3]);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (175:19) 
function create_if_block_4$1(ctx) {
	let switch_instance;
	let switch_instance_anchor;
	let current;

	const switch_instance_spread_levels = [
		{
			style: /*hasIconOnly*/ ctx[8] ? "margin-left: 0" : undefined
		},
		/*iconProps*/ ctx[10]
	];

	var switch_value = /*icon*/ ctx[2];

	function switch_props(ctx) {
		let switch_instance_props = {};

		for (let i = 0; i < switch_instance_spread_levels.length; i += 1) {
			switch_instance_props = assign(switch_instance_props, switch_instance_spread_levels[i]);
		}

		return { props: switch_instance_props };
	}

	if (switch_value) {
		switch_instance = construct_svelte_component(switch_value, switch_props());
	}

	return {
		c() {
			if (switch_instance) create_component(switch_instance.$$.fragment);
			switch_instance_anchor = empty();
		},
		l(nodes) {
			if (switch_instance) claim_component(switch_instance.$$.fragment, nodes);
			switch_instance_anchor = empty();
		},
		m(target, anchor) {
			if (switch_instance) mount_component(switch_instance, target, anchor);
			insert_hydration(target, switch_instance_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const switch_instance_changes = (dirty[0] & /*hasIconOnly, iconProps*/ 1280)
			? get_spread_update(switch_instance_spread_levels, [
					dirty[0] & /*hasIconOnly*/ 256 && {
						style: /*hasIconOnly*/ ctx[8] ? "margin-left: 0" : undefined
					},
					dirty[0] & /*iconProps*/ 1024 && get_spread_object(/*iconProps*/ ctx[10])
				])
			: {};

			if (dirty[0] & /*icon*/ 4 && switch_value !== (switch_value = /*icon*/ ctx[2])) {
				if (switch_instance) {
					group_outros();
					const old_component = switch_instance;

					transition_out(old_component.$$.fragment, 1, 0, () => {
						destroy_component(old_component, 1);
					});

					check_outros();
				}

				if (switch_value) {
					switch_instance = construct_svelte_component(switch_value, switch_props());
					create_component(switch_instance.$$.fragment);
					transition_in(switch_instance.$$.fragment, 1);
					mount_component(switch_instance, switch_instance_anchor.parentNode, switch_instance_anchor);
				} else {
					switch_instance = null;
				}
			} else if (switch_value) {
				switch_instance.$set(switch_instance_changes);
			}
		},
		i(local) {
			if (current) return;
			if (switch_instance) transition_in(switch_instance.$$.fragment, local);
			current = true;
		},
		o(local) {
			if (switch_instance) transition_out(switch_instance.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(switch_instance_anchor);
			if (switch_instance) destroy_component(switch_instance, detaching);
		}
	};
}

// (169:4) {#if $$slots.icon}
function create_if_block_3$1(ctx) {
	let current;
	const icon_slot_template = /*#slots*/ ctx[21].icon;
	const icon_slot = create_slot(icon_slot_template, ctx, /*$$scope*/ ctx[20], get_icon_slot_context);

	return {
		c() {
			if (icon_slot) icon_slot.c();
		},
		l(nodes) {
			if (icon_slot) icon_slot.l(nodes);
		},
		m(target, anchor) {
			if (icon_slot) {
				icon_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (icon_slot) {
				if (icon_slot.p && (!current || dirty[0] & /*$$scope, hasIconOnly, iconProps*/ 1049856)) {
					update_slot_base(
						icon_slot,
						icon_slot_template,
						ctx,
						/*$$scope*/ ctx[20],
						get_icon_slot_spread_changes(dirty) || !current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[20])
						: get_slot_changes(icon_slot_template, /*$$scope*/ ctx[20], dirty, get_icon_slot_changes),
						get_icon_slot_context
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon_slot, local);
			current = true;
		},
		o(local) {
			transition_out(icon_slot, local);
			current = false;
		},
		d(detaching) {
			if (icon_slot) icon_slot.d(detaching);
		}
	};
}

function create_fragment$3(ctx) {
	let current_block_type_index;
	let if_block;
	let if_block_anchor;
	let current;
	const if_block_creators = [create_if_block$2, create_if_block_1$1, create_if_block_2$1, create_else_block];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*skeleton*/ ctx[5]) return 0;
		if (/*as*/ ctx[4]) return 1;
		if (/*href*/ ctx[7] && !/*disabled*/ ctx[6]) return 2;
		return 3;
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
		p(ctx, dirty) {
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

function instance$3($$self, $$props, $$invalidate) {
	let hasIconOnly;
	let iconProps;
	let buttonProps;

	const omit_props_names = [
		"kind","size","expressive","isSelected","icon","iconDescription","tooltipAlignment","tooltipPosition","as","skeleton","disabled","href","tabindex","type","ref"
	];

	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	const $$slots = compute_slots(slots);
	let { kind = "primary" } = $$props;
	let { size = "default" } = $$props;
	let { expressive = false } = $$props;
	let { isSelected = false } = $$props;
	let { icon = undefined } = $$props;
	let { iconDescription = undefined } = $$props;
	let { tooltipAlignment = "center" } = $$props;
	let { tooltipPosition = "bottom" } = $$props;
	let { as = false } = $$props;
	let { skeleton = false } = $$props;
	let { disabled = false } = $$props;
	let { href = undefined } = $$props;
	let { tabindex = "0" } = $$props;
	let { type = "button" } = $$props;
	let { ref = null } = $$props;
	const ctx = getContext("ComposedModal");

	function click_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function focus_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function blur_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler_1(event) {
		bubble.call(this, $$self, event);
	}

	function click_handler_2(event) {
		bubble.call(this, $$self, event);
	}

	function focus_handler_2(event) {
		bubble.call(this, $$self, event);
	}

	function blur_handler_2(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler_2(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler_2(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler_2(event) {
		bubble.call(this, $$self, event);
	}

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	function focus_handler(event) {
		bubble.call(this, $$self, event);
	}

	function blur_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler(event) {
		bubble.call(this, $$self, event);
	}

	function a_binding($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			ref = $$value;
			$$invalidate(0, ref);
		});
	}

	function button_binding($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			ref = $$value;
			$$invalidate(0, ref);
		});
	}

	$$self.$$set = $$new_props => {
		$$props = assign(assign({}, $$props), exclude_internal_props($$new_props));
		$$invalidate(11, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('kind' in $$new_props) $$invalidate(13, kind = $$new_props.kind);
		if ('size' in $$new_props) $$invalidate(1, size = $$new_props.size);
		if ('expressive' in $$new_props) $$invalidate(14, expressive = $$new_props.expressive);
		if ('isSelected' in $$new_props) $$invalidate(15, isSelected = $$new_props.isSelected);
		if ('icon' in $$new_props) $$invalidate(2, icon = $$new_props.icon);
		if ('iconDescription' in $$new_props) $$invalidate(3, iconDescription = $$new_props.iconDescription);
		if ('tooltipAlignment' in $$new_props) $$invalidate(16, tooltipAlignment = $$new_props.tooltipAlignment);
		if ('tooltipPosition' in $$new_props) $$invalidate(17, tooltipPosition = $$new_props.tooltipPosition);
		if ('as' in $$new_props) $$invalidate(4, as = $$new_props.as);
		if ('skeleton' in $$new_props) $$invalidate(5, skeleton = $$new_props.skeleton);
		if ('disabled' in $$new_props) $$invalidate(6, disabled = $$new_props.disabled);
		if ('href' in $$new_props) $$invalidate(7, href = $$new_props.href);
		if ('tabindex' in $$new_props) $$invalidate(18, tabindex = $$new_props.tabindex);
		if ('type' in $$new_props) $$invalidate(19, type = $$new_props.type);
		if ('ref' in $$new_props) $$invalidate(0, ref = $$new_props.ref);
		if ('$$scope' in $$new_props) $$invalidate(20, $$scope = $$new_props.$$scope);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty[0] & /*ref*/ 1) {
			if (ctx && ref) {
				ctx.declareRef(ref);
			}
		}

		if ($$self.$$.dirty[0] & /*icon*/ 4) {
			$$invalidate(8, hasIconOnly = (icon || $$slots.icon) && !$$slots.default);
		}

		if ($$self.$$.dirty[0] & /*iconDescription*/ 8) {
			$$invalidate(10, iconProps = {
				"aria-hidden": "true",
				class: "bx--btn__icon",
				"aria-label": iconDescription
			});
		}

		$$invalidate(9, buttonProps = {
			type: href && !disabled ? undefined : type,
			tabindex,
			disabled: disabled === true ? true : undefined,
			href,
			"aria-pressed": hasIconOnly && kind === "ghost" && !href
			? isSelected
			: undefined,
			...$$restProps,
			class: [
				"bx--btn",
				expressive && "bx--btn--expressive",
				(size === "small" && !expressive || size === "sm" && !expressive || size === "small" && !expressive) && "bx--btn--sm",
				size === "field" && !expressive || size === "md" && !expressive && "bx--btn--md",
				size === "field" && "bx--btn--field",
				size === "small" && "bx--btn--sm",
				size === "lg" && "bx--btn--lg",
				size === "xl" && "bx--btn--xl",
				kind && `bx--btn--${kind}`,
				disabled && "bx--btn--disabled",
				hasIconOnly && "bx--btn--icon-only",
				hasIconOnly && "bx--tooltip__trigger",
				hasIconOnly && "bx--tooltip--a11y",
				hasIconOnly && tooltipPosition && `bx--btn--icon-only--${tooltipPosition}`,
				hasIconOnly && tooltipAlignment && `bx--tooltip--align-${tooltipAlignment}`,
				hasIconOnly && isSelected && kind === "ghost" && "bx--btn--selected",
				$$restProps.class
			].filter(Boolean).join(" ")
		});
	};

	return [
		ref,
		size,
		icon,
		iconDescription,
		as,
		skeleton,
		disabled,
		href,
		hasIconOnly,
		buttonProps,
		iconProps,
		$$restProps,
		$$slots,
		kind,
		expressive,
		isSelected,
		tooltipAlignment,
		tooltipPosition,
		tabindex,
		type,
		$$scope,
		slots,
		click_handler_1,
		focus_handler_1,
		blur_handler_1,
		mouseover_handler_1,
		mouseenter_handler_1,
		mouseleave_handler_1,
		click_handler_2,
		focus_handler_2,
		blur_handler_2,
		mouseover_handler_2,
		mouseenter_handler_2,
		mouseleave_handler_2,
		click_handler,
		focus_handler,
		blur_handler,
		mouseover_handler,
		mouseenter_handler,
		mouseleave_handler,
		a_binding,
		button_binding
	];
}

let Component$3 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(
			this,
			options,
			instance$3,
			create_fragment$3,
			safe_not_equal,
			{
				kind: 13,
				size: 1,
				expressive: 14,
				isSelected: 15,
				icon: 2,
				iconDescription: 3,
				tooltipAlignment: 16,
				tooltipPosition: 17,
				as: 4,
				skeleton: 5,
				disabled: 6,
				href: 7,
				tabindex: 18,
				type: 19,
				ref: 0
			},
			null,
			[-1, -1]
		);
	}
};

/* generated by Svelte v3.59.1 */

function create_if_block$1(ctx) {
	let title_1;
	let t;

	return {
		c() {
			title_1 = svg_element("title");
			t = text(/*title*/ ctx[1]);
		},
		l(nodes) {
			title_1 = claim_svg_element(nodes, "title", {});
			var title_1_nodes = children(title_1);
			t = claim_text(title_1_nodes, /*title*/ ctx[1]);
			title_1_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, title_1, anchor);
			append_hydration(title_1, t);
		},
		p(ctx, dirty) {
			if (dirty & /*title*/ 2) set_data(t, /*title*/ ctx[1]);
		},
		d(detaching) {
			if (detaching) detach(title_1);
		}
	};
}

function create_fragment$2(ctx) {
	let svg;
	let path;
	let if_block = /*title*/ ctx[1] && create_if_block$1(ctx);

	let svg_levels = [
		{ xmlns: "http://www.w3.org/2000/svg" },
		{ viewBox: "0 0 32 32" },
		{ fill: "currentColor" },
		{ preserveAspectRatio: "xMidYMid meet" },
		{ width: /*size*/ ctx[0] },
		{ height: /*size*/ ctx[0] },
		/*attributes*/ ctx[2],
		/*$$restProps*/ ctx[3]
	];

	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			if (if_block) if_block.c();
			path = svg_element("path");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {
				xmlns: true,
				viewBox: true,
				fill: true,
				preserveAspectRatio: true,
				width: true,
				height: true
			});

			var svg_nodes = children(svg);
			if (if_block) if_block.l(svg_nodes);
			path = claim_svg_element(svg_nodes, "path", { d: true });
			children(path).forEach(detach);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(path, "d", "M24 9.4L22.6 8 16 14.6 9.4 8 8 9.4 14.6 16 8 22.6 9.4 24 16 17.4 22.6 24 24 22.6 17.4 16 24 9.4z");
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			if (if_block) if_block.m(svg, null);
			append_hydration(svg, path);
		},
		p(ctx, [dirty]) {
			if (/*title*/ ctx[1]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$1(ctx);
					if_block.c();
					if_block.m(svg, path);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [
				{ xmlns: "http://www.w3.org/2000/svg" },
				{ viewBox: "0 0 32 32" },
				{ fill: "currentColor" },
				{ preserveAspectRatio: "xMidYMid meet" },
				dirty & /*size*/ 1 && { width: /*size*/ ctx[0] },
				dirty & /*size*/ 1 && { height: /*size*/ ctx[0] },
				dirty & /*attributes*/ 4 && /*attributes*/ ctx[2],
				dirty & /*$$restProps*/ 8 && /*$$restProps*/ ctx[3]
			]));
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(svg);
			if (if_block) if_block.d();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let labelled;
	let attributes;
	const omit_props_names = ["size","title"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { size = 16 } = $$props;
	let { title = undefined } = $$props;

	$$self.$$set = $$new_props => {
		$$invalidate(5, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(3, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('size' in $$new_props) $$invalidate(0, size = $$new_props.size);
		if ('title' in $$new_props) $$invalidate(1, title = $$new_props.title);
	};

	$$self.$$.update = () => {
		$$invalidate(4, labelled = $$props["aria-label"] || $$props["aria-labelledby"] || title);

		$$invalidate(2, attributes = {
			"aria-hidden": labelled ? undefined : true,
			role: labelled ? "img" : undefined,
			focusable: Number($$props["tabindex"]) === 0 ? true : undefined
		});
	};

	$$props = exclude_internal_props($$props);
	return [size, title, attributes, $$restProps, labelled];
}

let Component$2 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$2, create_fragment$2, safe_not_equal, { size: 0, title: 1 });
	}
};

/** A set of stores indicating whether a modal is open. */
const stores = new Set();

/** Store for the number of open modals. */
const modalsOpen = writable(0);

const updateModalsOpen = () =>
  modalsOpen.set([...stores].filter((open) => get_store_value(open)).length);

/**
 * Adds a modal's store to the open modal tracking.
 * Has to be called during component initialization.
 * Modal is automatically removed on destroy.
 * @param {import('svelte/store').Readable<boolean>} openStore
 *   Store that indicates whether the modal is opened.
 */
const trackModal = (openStore) =>
  onMount(() => {
    stores.add(openStore);
    const unsubscribe = openStore.subscribe(updateModalsOpen);

    return () => {
      unsubscribe();
      stores.delete(openStore);

      updateModalsOpen();
    };
  });

modalsOpen.subscribe((openCount) => {
  if (typeof document !== "undefined")
    document.body.classList.toggle("bx--body--with-modal-open", openCount > 0);
});

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[55] = list[i];
	return child_ctx;
}

const get_heading_slot_changes = dirty => ({});
const get_heading_slot_context = ctx => ({});
const get_label_slot_changes = dirty => ({});
const get_label_slot_context = ctx => ({});

// (211:6) {#if passiveModal}
function create_if_block_6(ctx) {
	let button;
	let close;
	let current;
	let mounted;
	let dispose;

	close = new Component$2({
			props: {
				size: 20,
				class: "bx--modal-close__icon",
				"aria-hidden": "true"
			}
		});

	return {
		c() {
			button = element("button");
			create_component(close.$$.fragment);
			this.h();
		},
		l(nodes) {
			button = claim_element(nodes, "BUTTON", { type: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(close.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "type", "button");
			attr(button, "aria-label", /*iconDescription*/ ctx[8]);
			toggle_class(button, "bx--modal-close", true);
		},
		m(target, anchor) {
			insert_hydration(target, button, anchor);
			mount_component(close, button, null);
			/*button_binding*/ ctx[37](button);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[38]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (!current || dirty[0] & /*iconDescription*/ 256) {
				attr(button, "aria-label", /*iconDescription*/ ctx[8]);
			}
		},
		i(local) {
			if (current) return;
			transition_in(close.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(close.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(button);
			destroy_component(close);
			/*button_binding*/ ctx[37](null);
			mounted = false;
			dispose();
		}
	};
}

// (224:6) {#if modalLabel}
function create_if_block_5(ctx) {
	let h2;
	let current;
	const label_slot_template = /*#slots*/ ctx[31].label;
	const label_slot = create_slot(label_slot_template, ctx, /*$$scope*/ ctx[50], get_label_slot_context);
	const label_slot_or_fallback = label_slot || fallback_block_1(ctx);

	return {
		c() {
			h2 = element("h2");
			if (label_slot_or_fallback) label_slot_or_fallback.c();
			this.h();
		},
		l(nodes) {
			h2 = claim_element(nodes, "H2", { id: true });
			var h2_nodes = children(h2);
			if (label_slot_or_fallback) label_slot_or_fallback.l(h2_nodes);
			h2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "id", /*modalLabelId*/ ctx[25]);
			toggle_class(h2, "bx--modal-header__label", true);
		},
		m(target, anchor) {
			insert_hydration(target, h2, anchor);

			if (label_slot_or_fallback) {
				label_slot_or_fallback.m(h2, null);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (label_slot) {
				if (label_slot.p && (!current || dirty[1] & /*$$scope*/ 524288)) {
					update_slot_base(
						label_slot,
						label_slot_template,
						ctx,
						/*$$scope*/ ctx[50],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[50])
						: get_slot_changes(label_slot_template, /*$$scope*/ ctx[50], dirty, get_label_slot_changes),
						get_label_slot_context
					);
				}
			} else {
				if (label_slot_or_fallback && label_slot_or_fallback.p && (!current || dirty[0] & /*modalLabel*/ 128)) {
					label_slot_or_fallback.p(ctx, !current ? [-1, -1] : dirty);
				}
			}

			if (!current || dirty[0] & /*modalLabelId*/ 33554432) {
				attr(h2, "id", /*modalLabelId*/ ctx[25]);
			}
		},
		i(local) {
			if (current) return;
			transition_in(label_slot_or_fallback, local);
			current = true;
		},
		o(local) {
			transition_out(label_slot_or_fallback, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(h2);
			if (label_slot_or_fallback) label_slot_or_fallback.d(detaching);
		}
	};
}

// (226:29) {modalLabel}
function fallback_block_1(ctx) {
	let t;

	return {
		c() {
			t = text(/*modalLabel*/ ctx[7]);
		},
		l(nodes) {
			t = claim_text(nodes, /*modalLabel*/ ctx[7]);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*modalLabel*/ 128) set_data(t, /*modalLabel*/ ctx[7]);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (230:29) {modalHeading}
function fallback_block(ctx) {
	let t;

	return {
		c() {
			t = text(/*modalHeading*/ ctx[6]);
		},
		l(nodes) {
			t = claim_text(nodes, /*modalHeading*/ ctx[6]);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*modalHeading*/ 64) set_data(t, /*modalHeading*/ ctx[6]);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (232:6) {#if !passiveModal}
function create_if_block_4(ctx) {
	let button;
	let close;
	let current;
	let mounted;
	let dispose;

	close = new Component$2({
			props: {
				size: 20,
				class: "bx--modal-close__icon",
				"aria-hidden": "true"
			}
		});

	return {
		c() {
			button = element("button");
			create_component(close.$$.fragment);
			this.h();
		},
		l(nodes) {
			button = claim_element(nodes, "BUTTON", { type: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(close.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "type", "button");
			attr(button, "aria-label", /*iconDescription*/ ctx[8]);
			toggle_class(button, "bx--modal-close", true);
		},
		m(target, anchor) {
			insert_hydration(target, button, anchor);
			mount_component(close, button, null);
			/*button_binding_1*/ ctx[39](button);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_2*/ ctx[40]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (!current || dirty[0] & /*iconDescription*/ 256) {
				attr(button, "aria-label", /*iconDescription*/ ctx[8]);
			}
		},
		i(local) {
			if (current) return;
			transition_in(close.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(close.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(button);
			destroy_component(close);
			/*button_binding_1*/ ctx[39](null);
			mounted = false;
			dispose();
		}
	};
}

// (259:4) {#if hasScrollingContent}
function create_if_block_3(ctx) {
	let div;

	return {
		c() {
			div = element("div");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", {});
			children(div).forEach(detach);
			this.h();
		},
		h() {
			toggle_class(div, "bx--modal-content--overflow-indicator", true);
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (262:4) {#if !passiveModal}
function create_if_block(ctx) {
	let div;
	let current_block_type_index;
	let if_block;
	let t;
	let button;
	let current;
	const if_block_creators = [create_if_block_1, create_if_block_2];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*secondaryButtons*/ ctx[16].length > 0) return 0;
		if (/*secondaryButtonText*/ ctx[15]) return 1;
		return -1;
	}

	if (~(current_block_type_index = select_block_type(ctx))) {
		if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
	}

	button = new Component$3({
			props: {
				kind: /*danger*/ ctx[3] ? "danger" : "primary",
				disabled: /*primaryButtonDisabled*/ ctx[12],
				icon: /*primaryButtonIcon*/ ctx[13],
				$$slots: { default: [create_default_slot$1] },
				$$scope: { ctx }
			}
		});

	button.$on("click", /*click_handler_5*/ ctx[43]);

	return {
		c() {
			div = element("div");
			if (if_block) if_block.c();
			t = space();
			create_component(button.$$.fragment);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", {});
			var div_nodes = children(div);
			if (if_block) if_block.l(div_nodes);
			t = claim_space(div_nodes);
			claim_component(button.$$.fragment, div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			toggle_class(div, "bx--modal-footer", true);
			toggle_class(div, "bx--modal-footer--three-button", /*secondaryButtons*/ ctx[16].length === 2);
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].m(div, null);
			}

			append_hydration(div, t);
			mount_component(button, div, null);
			current = true;
		},
		p(ctx, dirty) {
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if (~current_block_type_index) {
					if_blocks[current_block_type_index].p(ctx, dirty);
				}
			} else {
				if (if_block) {
					group_outros();

					transition_out(if_blocks[previous_block_index], 1, 1, () => {
						if_blocks[previous_block_index] = null;
					});

					check_outros();
				}

				if (~current_block_type_index) {
					if_block = if_blocks[current_block_type_index];

					if (!if_block) {
						if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
						if_block.c();
					} else {
						if_block.p(ctx, dirty);
					}

					transition_in(if_block, 1);
					if_block.m(div, t);
				} else {
					if_block = null;
				}
			}

			const button_changes = {};
			if (dirty[0] & /*danger*/ 8) button_changes.kind = /*danger*/ ctx[3] ? "danger" : "primary";
			if (dirty[0] & /*primaryButtonDisabled*/ 4096) button_changes.disabled = /*primaryButtonDisabled*/ ctx[12];
			if (dirty[0] & /*primaryButtonIcon*/ 8192) button_changes.icon = /*primaryButtonIcon*/ ctx[13];

			if (dirty[0] & /*primaryButtonText*/ 2048 | dirty[1] & /*$$scope*/ 524288) {
				button_changes.$$scope = { dirty, ctx };
			}

			button.$set(button_changes);

			if (!current || dirty[0] & /*secondaryButtons*/ 65536) {
				toggle_class(div, "bx--modal-footer--three-button", /*secondaryButtons*/ ctx[16].length === 2);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			transition_in(button.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			transition_out(button.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);

			if (~current_block_type_index) {
				if_blocks[current_block_type_index].d();
			}

			destroy_component(button);
		}
	};
}

// (278:38) 
function create_if_block_2(ctx) {
	let button;
	let current;

	button = new Component$3({
			props: {
				kind: "secondary",
				$$slots: { default: [create_default_slot_2$1] },
				$$scope: { ctx }
			}
		});

	button.$on("click", /*click_handler_4*/ ctx[42]);

	return {
		c() {
			create_component(button.$$.fragment);
		},
		l(nodes) {
			claim_component(button.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(button, target, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const button_changes = {};

			if (dirty[0] & /*secondaryButtonText*/ 32768 | dirty[1] & /*$$scope*/ 524288) {
				button_changes.$$scope = { dirty, ctx };
			}

			button.$set(button_changes);
		},
		i(local) {
			if (current) return;
			transition_in(button.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(button.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(button, detaching);
		}
	};
}

// (267:8) {#if secondaryButtons.length > 0}
function create_if_block_1(ctx) {
	let each_1_anchor;
	let current;
	let each_value = /*secondaryButtons*/ ctx[16];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			each_1_anchor = empty();
		},
		l(nodes) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nodes);
			}

			each_1_anchor = empty();
		},
		m(target, anchor) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(target, anchor);
				}
			}

			insert_hydration(target, each_1_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			if (dirty[0] & /*dispatch, secondaryButtons*/ 67174400) {
				each_value = /*secondaryButtons*/ ctx[16];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(each_1_anchor.parentNode, each_1_anchor);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			destroy_each(each_blocks, detaching);
			if (detaching) detach(each_1_anchor);
		}
	};
}

// (279:10) <Button             kind="secondary"             on:click={() => {               dispatch("click:button--secondary", {                 text: secondaryButtonText,               });             }}           >
function create_default_slot_2$1(ctx) {
	let t;

	return {
		c() {
			t = text(/*secondaryButtonText*/ ctx[15]);
		},
		l(nodes) {
			t = claim_text(nodes, /*secondaryButtonText*/ ctx[15]);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*secondaryButtonText*/ 32768) set_data(t, /*secondaryButtonText*/ ctx[15]);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (269:12) <Button               kind="secondary"               on:click={() => {                 dispatch("click:button--secondary", { text: button.text });               }}             >
function create_default_slot_1$1(ctx) {
	let t0_value = /*button*/ ctx[55].text + "";
	let t0;
	let t1;

	return {
		c() {
			t0 = text(t0_value);
			t1 = space();
		},
		l(nodes) {
			t0 = claim_text(nodes, t0_value);
			t1 = claim_space(nodes);
		},
		m(target, anchor) {
			insert_hydration(target, t0, anchor);
			insert_hydration(target, t1, anchor);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*secondaryButtons*/ 65536 && t0_value !== (t0_value = /*button*/ ctx[55].text + "")) set_data(t0, t0_value);
		},
		d(detaching) {
			if (detaching) detach(t0);
			if (detaching) detach(t1);
		}
	};
}

// (268:10) {#each secondaryButtons as button}
function create_each_block(ctx) {
	let button;
	let current;

	function click_handler_3() {
		return /*click_handler_3*/ ctx[41](/*button*/ ctx[55]);
	}

	button = new Component$3({
			props: {
				kind: "secondary",
				$$slots: { default: [create_default_slot_1$1] },
				$$scope: { ctx }
			}
		});

	button.$on("click", click_handler_3);

	return {
		c() {
			create_component(button.$$.fragment);
		},
		l(nodes) {
			claim_component(button.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(button, target, anchor);
			current = true;
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			const button_changes = {};

			if (dirty[0] & /*secondaryButtons*/ 65536 | dirty[1] & /*$$scope*/ 524288) {
				button_changes.$$scope = { dirty, ctx };
			}

			button.$set(button_changes);
		},
		i(local) {
			if (current) return;
			transition_in(button.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(button.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(button, detaching);
		}
	};
}

// (290:8) <Button           kind={danger ? "danger" : "primary"}           disabled={primaryButtonDisabled}           icon={primaryButtonIcon}           on:click={() => {             dispatch("submit");             dispatch("click:button--primary");           }}         >
function create_default_slot$1(ctx) {
	let t;

	return {
		c() {
			t = text(/*primaryButtonText*/ ctx[11]);
		},
		l(nodes) {
			t = claim_text(nodes, /*primaryButtonText*/ ctx[11]);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*primaryButtonText*/ 2048) set_data(t, /*primaryButtonText*/ ctx[11]);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

function create_fragment$1(ctx) {
	let div3;
	let div2;
	let div0;
	let t0;
	let t1;
	let h3;
	let t2;
	let t3;
	let div1;
	let div1_tabindex_value;
	let div1_role_value;
	let div1_aria_label_value;
	let div1_aria_labelledby_value;
	let t4;
	let t5;
	let div2_role_value;
	let div2_aria_describedby_value;
	let current;
	let mounted;
	let dispose;
	let if_block0 = /*passiveModal*/ ctx[5] && create_if_block_6(ctx);
	let if_block1 = /*modalLabel*/ ctx[7] && create_if_block_5(ctx);
	const heading_slot_template = /*#slots*/ ctx[31].heading;
	const heading_slot = create_slot(heading_slot_template, ctx, /*$$scope*/ ctx[50], get_heading_slot_context);
	const heading_slot_or_fallback = heading_slot || fallback_block(ctx);
	let if_block2 = !/*passiveModal*/ ctx[5] && create_if_block_4(ctx);
	const default_slot_template = /*#slots*/ ctx[31].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[50], null);
	let if_block3 = /*hasScrollingContent*/ ctx[10] && create_if_block_3();
	let if_block4 = !/*passiveModal*/ ctx[5] && create_if_block(ctx);
	let div3_levels = [{ role: "presentation" }, { id: /*id*/ ctx[18] }, /*$$restProps*/ ctx[28]];
	let div_data_3 = {};

	for (let i = 0; i < div3_levels.length; i += 1) {
		div_data_3 = assign(div_data_3, div3_levels[i]);
	}

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			div0 = element("div");
			if (if_block0) if_block0.c();
			t0 = space();
			if (if_block1) if_block1.c();
			t1 = space();
			h3 = element("h3");
			if (heading_slot_or_fallback) heading_slot_or_fallback.c();
			t2 = space();
			if (if_block2) if_block2.c();
			t3 = space();
			div1 = element("div");
			if (default_slot) default_slot.c();
			t4 = space();
			if (if_block3) if_block3.c();
			t5 = space();
			if (if_block4) if_block4.c();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { role: true, id: true });
			var div3_nodes = children(div3);

			div2 = claim_element(div3_nodes, "DIV", {
				tabindex: true,
				role: true,
				"aria-describedby": true,
				"aria-modal": true,
				"aria-label": true
			});

			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", {});
			var div0_nodes = children(div0);
			if (if_block0) if_block0.l(div0_nodes);
			t0 = claim_space(div0_nodes);
			if (if_block1) if_block1.l(div0_nodes);
			t1 = claim_space(div0_nodes);
			h3 = claim_element(div0_nodes, "H3", { id: true });
			var h3_nodes = children(h3);
			if (heading_slot_or_fallback) heading_slot_or_fallback.l(h3_nodes);
			h3_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			if (if_block2) if_block2.l(div0_nodes);
			div0_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);

			div1 = claim_element(div2_nodes, "DIV", {
				id: true,
				tabindex: true,
				role: true,
				"aria-label": true,
				"aria-labelledby": true
			});

			var div1_nodes = children(div1);
			if (default_slot) default_slot.l(div1_nodes);
			div1_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			if (if_block3) if_block3.l(div2_nodes);
			t5 = claim_space(div2_nodes);
			if (if_block4) if_block4.l(div2_nodes);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "id", /*modalHeadingId*/ ctx[24]);
			toggle_class(h3, "bx--modal-header__heading", true);
			toggle_class(div0, "bx--modal-header", true);
			attr(div1, "id", /*modalBodyId*/ ctx[23]);
			attr(div1, "tabindex", div1_tabindex_value = /*hasScrollingContent*/ ctx[10] ? "0" : undefined);
			attr(div1, "role", div1_role_value = /*hasScrollingContent*/ ctx[10] ? "region" : undefined);

			attr(div1, "aria-label", div1_aria_label_value = /*hasScrollingContent*/ ctx[10]
			? /*ariaLabel*/ ctx[22]
			: undefined);

			attr(div1, "aria-labelledby", div1_aria_labelledby_value = /*modalLabel*/ ctx[7]
			? /*modalLabelId*/ ctx[25]
			: /*modalHeadingId*/ ctx[24]);

			toggle_class(div1, "bx--modal-content", true);
			toggle_class(div1, "bx--modal-content--with-form", /*hasForm*/ ctx[9]);
			toggle_class(div1, "bx--modal-scroll-content", /*hasScrollingContent*/ ctx[10]);
			attr(div2, "tabindex", "-1");

			attr(div2, "role", div2_role_value = /*alert*/ ctx[4]
			? /*passiveModal*/ ctx[5] ? "alert" : "alertdialog"
			: "dialog");

			attr(div2, "aria-describedby", div2_aria_describedby_value = /*alert*/ ctx[4] && !/*passiveModal*/ ctx[5]
			? /*modalBodyId*/ ctx[23]
			: undefined);

			attr(div2, "aria-modal", "true");
			attr(div2, "aria-label", /*ariaLabel*/ ctx[22]);
			toggle_class(div2, "bx--modal-container", true);
			toggle_class(div2, "bx--modal-container--xs", /*size*/ ctx[2] === "xs");
			toggle_class(div2, "bx--modal-container--sm", /*size*/ ctx[2] === "sm");
			toggle_class(div2, "bx--modal-container--lg", /*size*/ ctx[2] === "lg");
			set_attributes(div3, div_data_3);
			toggle_class(div3, "bx--modal", true);
			toggle_class(div3, "bx--modal-tall", !/*passiveModal*/ ctx[5]);
			toggle_class(div3, "is-visible", /*open*/ ctx[0]);
			toggle_class(div3, "bx--modal--danger", /*danger*/ ctx[3]);
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, div0);
			if (if_block0) if_block0.m(div0, null);
			append_hydration(div0, t0);
			if (if_block1) if_block1.m(div0, null);
			append_hydration(div0, t1);
			append_hydration(div0, h3);

			if (heading_slot_or_fallback) {
				heading_slot_or_fallback.m(h3, null);
			}

			append_hydration(div0, t2);
			if (if_block2) if_block2.m(div0, null);
			append_hydration(div2, t3);
			append_hydration(div2, div1);

			if (default_slot) {
				default_slot.m(div1, null);
			}

			append_hydration(div2, t4);
			if (if_block3) if_block3.m(div2, null);
			append_hydration(div2, t5);
			if (if_block4) if_block4.m(div2, null);
			/*div2_binding*/ ctx[44](div2);
			/*div3_binding*/ ctx[46](div3);
			current = true;

			if (!mounted) {
				dispose = [
					listen(div2, "click", /*click_handler_6*/ ctx[45]),
					listen(div3, "keydown", /*keydown_handler*/ ctx[32]),
					listen(div3, "keydown", /*keydown_handler_1*/ ctx[47]),
					listen(div3, "click", /*click_handler*/ ctx[33]),
					listen(div3, "click", /*click_handler_7*/ ctx[48]),
					listen(div3, "mouseover", /*mouseover_handler*/ ctx[34]),
					listen(div3, "mouseenter", /*mouseenter_handler*/ ctx[35]),
					listen(div3, "mouseleave", /*mouseleave_handler*/ ctx[36]),
					listen(div3, "transitionend", /*transitionend_handler*/ ctx[49])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (/*passiveModal*/ ctx[5]) {
				if (if_block0) {
					if_block0.p(ctx, dirty);

					if (dirty[0] & /*passiveModal*/ 32) {
						transition_in(if_block0, 1);
					}
				} else {
					if_block0 = create_if_block_6(ctx);
					if_block0.c();
					transition_in(if_block0, 1);
					if_block0.m(div0, t0);
				}
			} else if (if_block0) {
				group_outros();

				transition_out(if_block0, 1, 1, () => {
					if_block0 = null;
				});

				check_outros();
			}

			if (/*modalLabel*/ ctx[7]) {
				if (if_block1) {
					if_block1.p(ctx, dirty);

					if (dirty[0] & /*modalLabel*/ 128) {
						transition_in(if_block1, 1);
					}
				} else {
					if_block1 = create_if_block_5(ctx);
					if_block1.c();
					transition_in(if_block1, 1);
					if_block1.m(div0, t1);
				}
			} else if (if_block1) {
				group_outros();

				transition_out(if_block1, 1, 1, () => {
					if_block1 = null;
				});

				check_outros();
			}

			if (heading_slot) {
				if (heading_slot.p && (!current || dirty[1] & /*$$scope*/ 524288)) {
					update_slot_base(
						heading_slot,
						heading_slot_template,
						ctx,
						/*$$scope*/ ctx[50],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[50])
						: get_slot_changes(heading_slot_template, /*$$scope*/ ctx[50], dirty, get_heading_slot_changes),
						get_heading_slot_context
					);
				}
			} else {
				if (heading_slot_or_fallback && heading_slot_or_fallback.p && (!current || dirty[0] & /*modalHeading*/ 64)) {
					heading_slot_or_fallback.p(ctx, !current ? [-1, -1] : dirty);
				}
			}

			if (!current || dirty[0] & /*modalHeadingId*/ 16777216) {
				attr(h3, "id", /*modalHeadingId*/ ctx[24]);
			}

			if (!/*passiveModal*/ ctx[5]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty[0] & /*passiveModal*/ 32) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block_4(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div0, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}

			if (default_slot) {
				if (default_slot.p && (!current || dirty[1] & /*$$scope*/ 524288)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[50],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[50])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[50], dirty, null),
						null
					);
				}
			}

			if (!current || dirty[0] & /*modalBodyId*/ 8388608) {
				attr(div1, "id", /*modalBodyId*/ ctx[23]);
			}

			if (!current || dirty[0] & /*hasScrollingContent*/ 1024 && div1_tabindex_value !== (div1_tabindex_value = /*hasScrollingContent*/ ctx[10] ? "0" : undefined)) {
				attr(div1, "tabindex", div1_tabindex_value);
			}

			if (!current || dirty[0] & /*hasScrollingContent*/ 1024 && div1_role_value !== (div1_role_value = /*hasScrollingContent*/ ctx[10] ? "region" : undefined)) {
				attr(div1, "role", div1_role_value);
			}

			if (!current || dirty[0] & /*hasScrollingContent, ariaLabel*/ 4195328 && div1_aria_label_value !== (div1_aria_label_value = /*hasScrollingContent*/ ctx[10]
			? /*ariaLabel*/ ctx[22]
			: undefined)) {
				attr(div1, "aria-label", div1_aria_label_value);
			}

			if (!current || dirty[0] & /*modalLabel, modalLabelId, modalHeadingId*/ 50331776 && div1_aria_labelledby_value !== (div1_aria_labelledby_value = /*modalLabel*/ ctx[7]
			? /*modalLabelId*/ ctx[25]
			: /*modalHeadingId*/ ctx[24])) {
				attr(div1, "aria-labelledby", div1_aria_labelledby_value);
			}

			if (!current || dirty[0] & /*hasForm*/ 512) {
				toggle_class(div1, "bx--modal-content--with-form", /*hasForm*/ ctx[9]);
			}

			if (!current || dirty[0] & /*hasScrollingContent*/ 1024) {
				toggle_class(div1, "bx--modal-scroll-content", /*hasScrollingContent*/ ctx[10]);
			}

			if (/*hasScrollingContent*/ ctx[10]) {
				if (if_block3) ; else {
					if_block3 = create_if_block_3();
					if_block3.c();
					if_block3.m(div2, t5);
				}
			} else if (if_block3) {
				if_block3.d(1);
				if_block3 = null;
			}

			if (!/*passiveModal*/ ctx[5]) {
				if (if_block4) {
					if_block4.p(ctx, dirty);

					if (dirty[0] & /*passiveModal*/ 32) {
						transition_in(if_block4, 1);
					}
				} else {
					if_block4 = create_if_block(ctx);
					if_block4.c();
					transition_in(if_block4, 1);
					if_block4.m(div2, null);
				}
			} else if (if_block4) {
				group_outros();

				transition_out(if_block4, 1, 1, () => {
					if_block4 = null;
				});

				check_outros();
			}

			if (!current || dirty[0] & /*alert, passiveModal*/ 48 && div2_role_value !== (div2_role_value = /*alert*/ ctx[4]
			? /*passiveModal*/ ctx[5] ? "alert" : "alertdialog"
			: "dialog")) {
				attr(div2, "role", div2_role_value);
			}

			if (!current || dirty[0] & /*alert, passiveModal, modalBodyId*/ 8388656 && div2_aria_describedby_value !== (div2_aria_describedby_value = /*alert*/ ctx[4] && !/*passiveModal*/ ctx[5]
			? /*modalBodyId*/ ctx[23]
			: undefined)) {
				attr(div2, "aria-describedby", div2_aria_describedby_value);
			}

			if (!current || dirty[0] & /*ariaLabel*/ 4194304) {
				attr(div2, "aria-label", /*ariaLabel*/ ctx[22]);
			}

			if (!current || dirty[0] & /*size*/ 4) {
				toggle_class(div2, "bx--modal-container--xs", /*size*/ ctx[2] === "xs");
			}

			if (!current || dirty[0] & /*size*/ 4) {
				toggle_class(div2, "bx--modal-container--sm", /*size*/ ctx[2] === "sm");
			}

			if (!current || dirty[0] & /*size*/ 4) {
				toggle_class(div2, "bx--modal-container--lg", /*size*/ ctx[2] === "lg");
			}

			set_attributes(div3, div_data_3 = get_spread_update(div3_levels, [
				{ role: "presentation" },
				(!current || dirty[0] & /*id*/ 262144) && { id: /*id*/ ctx[18] },
				dirty[0] & /*$$restProps*/ 268435456 && /*$$restProps*/ ctx[28]
			]));

			toggle_class(div3, "bx--modal", true);
			toggle_class(div3, "bx--modal-tall", !/*passiveModal*/ ctx[5]);
			toggle_class(div3, "is-visible", /*open*/ ctx[0]);
			toggle_class(div3, "bx--modal--danger", /*danger*/ ctx[3]);
		},
		i(local) {
			if (current) return;
			transition_in(if_block0);
			transition_in(if_block1);
			transition_in(heading_slot_or_fallback, local);
			transition_in(if_block2);
			transition_in(default_slot, local);
			transition_in(if_block4);
			current = true;
		},
		o(local) {
			transition_out(if_block0);
			transition_out(if_block1);
			transition_out(heading_slot_or_fallback, local);
			transition_out(if_block2);
			transition_out(default_slot, local);
			transition_out(if_block4);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			if (if_block0) if_block0.d();
			if (if_block1) if_block1.d();
			if (heading_slot_or_fallback) heading_slot_or_fallback.d(detaching);
			if (if_block2) if_block2.d();
			if (default_slot) default_slot.d(detaching);
			if (if_block3) if_block3.d();
			if (if_block4) if_block4.d();
			/*div2_binding*/ ctx[44](null);
			/*div3_binding*/ ctx[46](null);
			mounted = false;
			run_all(dispose);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let modalLabelId;
	let modalHeadingId;
	let modalBodyId;
	let ariaLabel;

	const omit_props_names = [
		"size","open","danger","alert","passiveModal","modalHeading","modalLabel","modalAriaLabel","iconDescription","hasForm","hasScrollingContent","primaryButtonText","primaryButtonDisabled","primaryButtonIcon","shouldSubmitOnEnter","secondaryButtonText","secondaryButtons","selectorPrimaryFocus","preventCloseOnClickOutside","id","ref"
	];

	let $$restProps = compute_rest_props($$props, omit_props_names);
	let $openStore;
	let { $$slots: slots = {}, $$scope } = $$props;
	let { size = undefined } = $$props;
	let { open = false } = $$props;
	let { danger = false } = $$props;
	let { alert = false } = $$props;
	let { passiveModal = false } = $$props;
	let { modalHeading = undefined } = $$props;
	let { modalLabel = undefined } = $$props;
	let { modalAriaLabel = undefined } = $$props;
	let { iconDescription = "Close the modal" } = $$props;
	let { hasForm = false } = $$props;
	let { hasScrollingContent = false } = $$props;
	let { primaryButtonText = "" } = $$props;
	let { primaryButtonDisabled = false } = $$props;
	let { primaryButtonIcon = undefined } = $$props;
	let { shouldSubmitOnEnter = true } = $$props;
	let { secondaryButtonText = "" } = $$props;
	let { secondaryButtons = [] } = $$props;
	let { selectorPrimaryFocus = "[data-modal-primary-focus]" } = $$props;
	let { preventCloseOnClickOutside = false } = $$props;
	let { id = "ccs-" + Math.random().toString(36) } = $$props;
	let { ref = null } = $$props;
	const dispatch = createEventDispatcher();
	let buttonRef = null;
	let innerModal = null;
	let opened = false;
	let didClickInnerModal = false;

	function focus(element) {
		const node = (element || innerModal).querySelector(selectorPrimaryFocus) || buttonRef;
		node.focus();
	}

	const openStore = writable(open);
	component_subscribe($$self, openStore, value => $$invalidate(52, $openStore = value));
	trackModal(openStore);

	afterUpdate(() => {
		if (opened) {
			if (!open) {
				opened = false;
				dispatch("close");
			}
		} else if (open) {
			opened = true;
			focus();
			dispatch("open");
		}
	});

	function keydown_handler(event) {
		bubble.call(this, $$self, event);
	}

	function click_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseover_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseenter_handler(event) {
		bubble.call(this, $$self, event);
	}

	function mouseleave_handler(event) {
		bubble.call(this, $$self, event);
	}

	function button_binding($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			buttonRef = $$value;
			$$invalidate(19, buttonRef);
		});
	}

	const click_handler_1 = () => {
		$$invalidate(0, open = false);
	};

	function button_binding_1($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			buttonRef = $$value;
			$$invalidate(19, buttonRef);
		});
	}

	const click_handler_2 = () => {
		$$invalidate(0, open = false);
	};

	const click_handler_3 = button => {
		dispatch("click:button--secondary", { text: button.text });
	};

	const click_handler_4 = () => {
		dispatch("click:button--secondary", { text: secondaryButtonText });
	};

	const click_handler_5 = () => {
		dispatch("submit");
		dispatch("click:button--primary");
	};

	function div2_binding($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			innerModal = $$value;
			$$invalidate(20, innerModal);
		});
	}

	const click_handler_6 = () => {
		$$invalidate(21, didClickInnerModal = true);
	};

	function div3_binding($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			ref = $$value;
			$$invalidate(1, ref);
		});
	}

	const keydown_handler_1 = e => {
		if (open) {
			if (e.key === "Escape") {
				$$invalidate(0, open = false);
			} else if (e.key === "Tab") {
				// trap focus
				// taken from github.com/carbon-design-system/carbon/packages/react/src/internal/keyboard/navigation.js
				const selectorTabbable = `
  a[href], area[href], input:not([disabled]):not([tabindex='-1']),
  button:not([disabled]):not([tabindex='-1']),select:not([disabled]):not([tabindex='-1']),
  textarea:not([disabled]):not([tabindex='-1']),
  iframe, object, embed, *[tabindex]:not([tabindex='-1']):not([disabled]), *[contenteditable=true]
`;

				const tabbable = Array.from(ref.querySelectorAll(selectorTabbable));
				let index = tabbable.indexOf(document.activeElement);
				if (index === -1 && e.shiftKey) index = 0;
				index += tabbable.length + (e.shiftKey ? -1 : 1);
				index %= tabbable.length;
				tabbable[index].focus();
				e.preventDefault();
			} else if (shouldSubmitOnEnter && e.key === "Enter" && !primaryButtonDisabled) {
				dispatch("submit");
				dispatch("click:button--primary");
			}
		}
	};

	const click_handler_7 = () => {
		if (!didClickInnerModal && !preventCloseOnClickOutside) $$invalidate(0, open = false);
		$$invalidate(21, didClickInnerModal = false);
	};

	const transitionend_handler = e => {
		if (e.propertyName === "transform") {
			dispatch("transitionend", { open });
		}
	};

	$$self.$$set = $$new_props => {
		$$invalidate(54, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(28, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('size' in $$new_props) $$invalidate(2, size = $$new_props.size);
		if ('open' in $$new_props) $$invalidate(0, open = $$new_props.open);
		if ('danger' in $$new_props) $$invalidate(3, danger = $$new_props.danger);
		if ('alert' in $$new_props) $$invalidate(4, alert = $$new_props.alert);
		if ('passiveModal' in $$new_props) $$invalidate(5, passiveModal = $$new_props.passiveModal);
		if ('modalHeading' in $$new_props) $$invalidate(6, modalHeading = $$new_props.modalHeading);
		if ('modalLabel' in $$new_props) $$invalidate(7, modalLabel = $$new_props.modalLabel);
		if ('modalAriaLabel' in $$new_props) $$invalidate(29, modalAriaLabel = $$new_props.modalAriaLabel);
		if ('iconDescription' in $$new_props) $$invalidate(8, iconDescription = $$new_props.iconDescription);
		if ('hasForm' in $$new_props) $$invalidate(9, hasForm = $$new_props.hasForm);
		if ('hasScrollingContent' in $$new_props) $$invalidate(10, hasScrollingContent = $$new_props.hasScrollingContent);
		if ('primaryButtonText' in $$new_props) $$invalidate(11, primaryButtonText = $$new_props.primaryButtonText);
		if ('primaryButtonDisabled' in $$new_props) $$invalidate(12, primaryButtonDisabled = $$new_props.primaryButtonDisabled);
		if ('primaryButtonIcon' in $$new_props) $$invalidate(13, primaryButtonIcon = $$new_props.primaryButtonIcon);
		if ('shouldSubmitOnEnter' in $$new_props) $$invalidate(14, shouldSubmitOnEnter = $$new_props.shouldSubmitOnEnter);
		if ('secondaryButtonText' in $$new_props) $$invalidate(15, secondaryButtonText = $$new_props.secondaryButtonText);
		if ('secondaryButtons' in $$new_props) $$invalidate(16, secondaryButtons = $$new_props.secondaryButtons);
		if ('selectorPrimaryFocus' in $$new_props) $$invalidate(30, selectorPrimaryFocus = $$new_props.selectorPrimaryFocus);
		if ('preventCloseOnClickOutside' in $$new_props) $$invalidate(17, preventCloseOnClickOutside = $$new_props.preventCloseOnClickOutside);
		if ('id' in $$new_props) $$invalidate(18, id = $$new_props.id);
		if ('ref' in $$new_props) $$invalidate(1, ref = $$new_props.ref);
		if ('$$scope' in $$new_props) $$invalidate(50, $$scope = $$new_props.$$scope);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty[0] & /*open*/ 1) {
			set_store_value(openStore, $openStore = open, $openStore);
		}

		if ($$self.$$.dirty[0] & /*id*/ 262144) {
			$$invalidate(25, modalLabelId = `bx--modal-header__label--modal-${id}`);
		}

		if ($$self.$$.dirty[0] & /*id*/ 262144) {
			$$invalidate(24, modalHeadingId = `bx--modal-header__heading--modal-${id}`);
		}

		if ($$self.$$.dirty[0] & /*id*/ 262144) {
			$$invalidate(23, modalBodyId = `bx--modal-body--${id}`);
		}

		$$invalidate(22, ariaLabel = modalLabel || $$props["aria-label"] || modalAriaLabel || modalHeading);
	};

	$$props = exclude_internal_props($$props);

	return [
		open,
		ref,
		size,
		danger,
		alert,
		passiveModal,
		modalHeading,
		modalLabel,
		iconDescription,
		hasForm,
		hasScrollingContent,
		primaryButtonText,
		primaryButtonDisabled,
		primaryButtonIcon,
		shouldSubmitOnEnter,
		secondaryButtonText,
		secondaryButtons,
		preventCloseOnClickOutside,
		id,
		buttonRef,
		innerModal,
		didClickInnerModal,
		ariaLabel,
		modalBodyId,
		modalHeadingId,
		modalLabelId,
		dispatch,
		openStore,
		$$restProps,
		modalAriaLabel,
		selectorPrimaryFocus,
		slots,
		keydown_handler,
		click_handler,
		mouseover_handler,
		mouseenter_handler,
		mouseleave_handler,
		button_binding,
		click_handler_1,
		button_binding_1,
		click_handler_2,
		click_handler_3,
		click_handler_4,
		click_handler_5,
		div2_binding,
		click_handler_6,
		div3_binding,
		keydown_handler_1,
		click_handler_7,
		transitionend_handler,
		$$scope
	];
}

let Component$1 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(
			this,
			options,
			instance$1,
			create_fragment$1,
			safe_not_equal,
			{
				size: 2,
				open: 0,
				danger: 3,
				alert: 4,
				passiveModal: 5,
				modalHeading: 6,
				modalLabel: 7,
				modalAriaLabel: 29,
				iconDescription: 8,
				hasForm: 9,
				hasScrollingContent: 10,
				primaryButtonText: 11,
				primaryButtonDisabled: 12,
				primaryButtonIcon: 13,
				shouldSubmitOnEnter: 14,
				secondaryButtonText: 15,
				secondaryButtons: 16,
				selectorPrimaryFocus: 30,
				preventCloseOnClickOutside: 17,
				id: 18,
				ref: 1
			},
			null,
			[-1, -1]
		);
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot_5(ctx) {
	let t;

	return {
		c() {
			t = text("Create database");
		},
		l(nodes) {
			t = claim_text(nodes, "Create database");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (15:0) <Modal   bind:open   modalHeading="Create database"   primaryButtonText="Confirm"   secondaryButtonText="Cancel"   on:click:button--secondary={() => (open = false)}   on:open   on:close   on:submit >
function create_default_slot_4(ctx) {
	let p;
	let t;

	return {
		c() {
			p = element("p");
			t = text("Create a new Cloudant database in the US South region.");
		},
		l(nodes) {
			p = claim_element(nodes, "P", {});
			var p_nodes = children(p);
			t = claim_text(p_nodes, "Create a new Cloudant database in the US South region.");
			p_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);
			append_hydration(p, t);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(p);
		}
	};
}

// (30:2) <AccordionItem title="Natural Language Classifier">
function create_default_slot_3(ctx) {
	let p;
	let t;

	return {
		c() {
			p = element("p");
			t = text("Natural Language Classifier uses advanced natural language processing and\n      machine learning techniques to create custom classification models. Users\n      train their data and the service predicts the appropriate category for the\n      inputted text.");
		},
		l(nodes) {
			p = claim_element(nodes, "P", {});
			var p_nodes = children(p);
			t = claim_text(p_nodes, "Natural Language Classifier uses advanced natural language processing and\n      machine learning techniques to create custom classification models. Users\n      train their data and the service predicts the appropriate category for the\n      inputted text.");
			p_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);
			append_hydration(p, t);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(p);
		}
	};
}

// (38:2) <AccordionItem title="Natural Language Understanding">
function create_default_slot_2(ctx) {
	let p;
	let t;

	return {
		c() {
			p = element("p");
			t = text("Analyze text to extract meta-data from content such as concepts, entities,\n      emotion, relations, sentiment and more.");
		},
		l(nodes) {
			p = claim_element(nodes, "P", {});
			var p_nodes = children(p);
			t = claim_text(p_nodes, "Analyze text to extract meta-data from content such as concepts, entities,\n      emotion, relations, sentiment and more.");
			p_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);
			append_hydration(p, t);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(p);
		}
	};
}

// (44:2) <AccordionItem title="Language Translator">
function create_default_slot_1(ctx) {
	let p;
	let t;

	return {
		c() {
			p = element("p");
			t = text("Translate text, documents, and websites from one language to another.\n      Create industry or region-specific translations via the service's\n      customization capability.");
		},
		l(nodes) {
			p = claim_element(nodes, "P", {});
			var p_nodes = children(p);
			t = claim_text(p_nodes, "Translate text, documents, and websites from one language to another.\n      Create industry or region-specific translations via the service's\n      customization capability.");
			p_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);
			append_hydration(p, t);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(p);
		}
	};
}

// (29:2) <Accordion>
function create_default_slot(ctx) {
	let accordionitem0;
	let t0;
	let accordionitem1;
	let t1;
	let accordionitem2;
	let current;

	accordionitem0 = new Component$5({
			props: {
				title: "Natural Language Classifier",
				$$slots: { default: [create_default_slot_3] },
				$$scope: { ctx }
			}
		});

	accordionitem1 = new Component$5({
			props: {
				title: "Natural Language Understanding",
				$$slots: { default: [create_default_slot_2] },
				$$scope: { ctx }
			}
		});

	accordionitem2 = new Component$5({
			props: {
				title: "Language Translator",
				$$slots: { default: [create_default_slot_1] },
				$$scope: { ctx }
			}
		});

	return {
		c() {
			create_component(accordionitem0.$$.fragment);
			t0 = space();
			create_component(accordionitem1.$$.fragment);
			t1 = space();
			create_component(accordionitem2.$$.fragment);
		},
		l(nodes) {
			claim_component(accordionitem0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(accordionitem1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(accordionitem2.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(accordionitem0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(accordionitem1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(accordionitem2, target, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const accordionitem0_changes = {};

			if (dirty & /*$$scope*/ 256) {
				accordionitem0_changes.$$scope = { dirty, ctx };
			}

			accordionitem0.$set(accordionitem0_changes);
			const accordionitem1_changes = {};

			if (dirty & /*$$scope*/ 256) {
				accordionitem1_changes.$$scope = { dirty, ctx };
			}

			accordionitem1.$set(accordionitem1_changes);
			const accordionitem2_changes = {};

			if (dirty & /*$$scope*/ 256) {
				accordionitem2_changes.$$scope = { dirty, ctx };
			}

			accordionitem2.$set(accordionitem2_changes);
		},
		i(local) {
			if (current) return;
			transition_in(accordionitem0.$$.fragment, local);
			transition_in(accordionitem1.$$.fragment, local);
			transition_in(accordionitem2.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(accordionitem0.$$.fragment, local);
			transition_out(accordionitem1.$$.fragment, local);
			transition_out(accordionitem2.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(accordionitem0, detaching);
			if (detaching) detach(t0);
			destroy_component(accordionitem1, detaching);
			if (detaching) detach(t1);
			destroy_component(accordionitem2, detaching);
		}
	};
}

function create_fragment(ctx) {
	let section;
	let button;
	let t0;
	let modal;
	let updating_open;
	let t1;
	let div;
	let accordion;
	let t2;
	let link;
	let current;

	button = new Component$3({
			props: {
				$$slots: { default: [create_default_slot_5] },
				$$scope: { ctx }
			}
		});

	button.$on("click", /*click_handler*/ ctx[2]);

	function modal_open_binding(value) {
		/*modal_open_binding*/ ctx[3](value);
	}

	let modal_props = {
		modalHeading: "Create database",
		primaryButtonText: "Confirm",
		secondaryButtonText: "Cancel",
		$$slots: { default: [create_default_slot_4] },
		$$scope: { ctx }
	};

	if (/*open*/ ctx[0] !== void 0) {
		modal_props.open = /*open*/ ctx[0];
	}

	modal = new Component$1({ props: modal_props });
	binding_callbacks.push(() => bind(modal, 'open', modal_open_binding));
	modal.$on("click:button--secondary", /*click_button_secondary_handler*/ ctx[4]);
	modal.$on("open", /*open_handler*/ ctx[5]);
	modal.$on("close", /*close_handler*/ ctx[6]);
	modal.$on("submit", /*submit_handler*/ ctx[7]);

	accordion = new Component$6({
			props: {
				$$slots: { default: [create_default_slot] },
				$$scope: { ctx }
			}
		});

	return {
		c() {
			section = element("section");
			create_component(button.$$.fragment);
			t0 = space();
			create_component(modal.$$.fragment);
			t1 = space();
			div = element("div");
			create_component(accordion.$$.fragment);
			t2 = space();
			link = element("link");
			this.h();
		},
		l(nodes) {
			section = claim_element(nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			claim_component(button.$$.fragment, section_nodes);
			t0 = claim_space(section_nodes);
			claim_component(modal.$$.fragment, section_nodes);
			section_nodes.forEach(detach);
			t1 = claim_space(nodes);
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			claim_component(accordion.$$.fragment, div_nodes);
			div_nodes.forEach(detach);
			t2 = claim_space(nodes);
			link = claim_element(nodes, "LINK", { rel: true, href: true });
			this.h();
		},
		h() {
			attr(section, "class", "section-container");
			attr(div, "class", "section-container");
			attr(link, "rel", "stylesheet");
			attr(link, "href", "https://unpkg.com/carbon-components-svelte/css/white.css");
		},
		m(target, anchor) {
			insert_hydration(target, section, anchor);
			mount_component(button, section, null);
			append_hydration(section, t0);
			mount_component(modal, section, null);
			insert_hydration(target, t1, anchor);
			insert_hydration(target, div, anchor);
			mount_component(accordion, div, null);
			insert_hydration(target, t2, anchor);
			insert_hydration(target, link, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const button_changes = {};

			if (dirty & /*$$scope*/ 256) {
				button_changes.$$scope = { dirty, ctx };
			}

			button.$set(button_changes);
			const modal_changes = {};

			if (dirty & /*$$scope*/ 256) {
				modal_changes.$$scope = { dirty, ctx };
			}

			if (!updating_open && dirty & /*open*/ 1) {
				updating_open = true;
				modal_changes.open = /*open*/ ctx[0];
				add_flush_callback(() => updating_open = false);
			}

			modal.$set(modal_changes);
			const accordion_changes = {};

			if (dirty & /*$$scope*/ 256) {
				accordion_changes.$$scope = { dirty, ctx };
			}

			accordion.$set(accordion_changes);
		},
		i(local) {
			if (current) return;
			transition_in(button.$$.fragment, local);
			transition_in(modal.$$.fragment, local);
			transition_in(accordion.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(button.$$.fragment, local);
			transition_out(modal.$$.fragment, local);
			transition_out(accordion.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(section);
			destroy_component(button);
			destroy_component(modal);
			if (detaching) detach(t1);
			if (detaching) detach(div);
			destroy_component(accordion);
			if (detaching) detach(t2);
			if (detaching) detach(link);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let open = false;
	const click_handler = () => $$invalidate(0, open = true);

	function modal_open_binding(value) {
		open = value;
		$$invalidate(0, open);
	}

	const click_button_secondary_handler = () => $$invalidate(0, open = false);

	function open_handler(event) {
		bubble.call(this, $$self, event);
	}

	function close_handler(event) {
		bubble.call(this, $$self, event);
	}

	function submit_handler(event) {
		bubble.call(this, $$self, event);
	}

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(1, props = $$props.props);
	};

	return [
		open,
		props,
		click_handler,
		modal_open_binding,
		click_button_secondary_handler,
		open_handler,
		close_handler,
		submit_handler
	];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { props: 1 });
	}
}

export { Component as default };
