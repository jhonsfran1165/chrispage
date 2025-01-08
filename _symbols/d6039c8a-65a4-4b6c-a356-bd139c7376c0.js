// New Block - Updated January 8, 2025
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
function hash(str) {
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
    const name = `__svelte_${hash(rule)}_${uid}`;
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

function create_else_block$1(ctx) {
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
function create_if_block$1(ctx) {
	let previous_tag = /*tag*/ ctx[1];
	let svelte_element_anchor;
	let tag_will_be_removed = false;
	let current;
	let svelte_element = /*tag*/ ctx[1] && create_dynamic_element(ctx);

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
					svelte_element = create_dynamic_element(ctx);
					previous_tag = /*tag*/ ctx[1];
					svelte_element.c();
					transition_in(svelte_element);
					svelte_element.m(svelte_element_anchor.parentNode, svelte_element_anchor);
				} else if (safe_not_equal(previous_tag, /*tag*/ ctx[1])) {
					svelte_element.d(1);
					svelte_element = create_dynamic_element(ctx);
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
function create_dynamic_element(ctx) {
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

function create_fragment$2(ctx) {
	let current_block_type_index;
	let if_block;
	let if_block_anchor;
	let current;
	const if_block_creators = [create_if_block$1, create_else_block$1];
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

function instance$2($$self, $$props, $$invalidate) {
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

let Component$2 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
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

/* generated by Svelte v3.59.1 */

function create_else_block(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[10].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[11], null);

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
				if (default_slot.p && (!current || dirty & /*$$scope*/ 2048)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[11],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[11])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[11], dirty, null),
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

// (32:2) {#if img}
function create_if_block(ctx) {
	let img_1;
	let img_1_src_value;
	let t;
	let div;
	let current;
	const default_slot_template = /*#slots*/ ctx[10].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[11], null);

	return {
		c() {
			img_1 = element("img");
			t = space();
			div = element("div");
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			img_1 = claim_element(nodes, "IMG", { class: true, src: true, alt: true });
			t = claim_space(nodes);
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			if (default_slot) default_slot.l(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img_1, "class", /*imgClass*/ ctx[4]);
			if (!src_url_equal(img_1.src, img_1_src_value = /*img*/ ctx[1])) attr(img_1, "src", img_1_src_value);
			attr(img_1, "alt", "");
			attr(div, "class", /*innerPdding*/ ctx[2]);
		},
		m(target, anchor) {
			insert_hydration(target, img_1, anchor);
			insert_hydration(target, t, anchor);
			insert_hydration(target, div, anchor);

			if (default_slot) {
				default_slot.m(div, null);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (!current || dirty & /*imgClass*/ 16) {
				attr(img_1, "class", /*imgClass*/ ctx[4]);
			}

			if (!current || dirty & /*img*/ 2 && !src_url_equal(img_1.src, img_1_src_value = /*img*/ ctx[1])) {
				attr(img_1, "src", img_1_src_value);
			}

			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 2048)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[11],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[11])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[11], dirty, null),
						null
					);
				}
			}

			if (!current || dirty & /*innerPdding*/ 4) {
				attr(div, "class", /*innerPdding*/ ctx[2]);
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
			if (detaching) detach(img_1);
			if (detaching) detach(t);
			if (detaching) detach(div);
			if (default_slot) default_slot.d(detaching);
		}
	};
}

// (31:0) <Frame tag={href ? 'a' : 'div'} rounded shadow border {href} {...$$restProps} class={cardClass}>
function create_default_slot$1(ctx) {
	let current_block_type_index;
	let if_block;
	let if_block_anchor;
	let current;
	const if_block_creators = [create_if_block, create_else_block];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*img*/ ctx[1]) return 0;
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

function create_fragment$1(ctx) {
	let frame;
	let current;

	const frame_spread_levels = [
		{ tag: /*href*/ ctx[0] ? 'a' : 'div' },
		{ rounded: true },
		{ shadow: true },
		{ border: true },
		{ href: /*href*/ ctx[0] },
		/*$$restProps*/ ctx[5],
		{ class: /*cardClass*/ ctx[3] }
	];

	let frame_props = {
		$$slots: { default: [create_default_slot$1] },
		$$scope: { ctx }
	};

	for (let i = 0; i < frame_spread_levels.length; i += 1) {
		frame_props = assign(frame_props, frame_spread_levels[i]);
	}

	frame = new Component$2({ props: frame_props });

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
			const frame_changes = (dirty & /*href, $$restProps, cardClass*/ 41)
			? get_spread_update(frame_spread_levels, [
					dirty & /*href*/ 1 && { tag: /*href*/ ctx[0] ? 'a' : 'div' },
					frame_spread_levels[1],
					frame_spread_levels[2],
					frame_spread_levels[3],
					dirty & /*href*/ 1 && { href: /*href*/ ctx[0] },
					dirty & /*$$restProps*/ 32 && get_spread_object(/*$$restProps*/ ctx[5]),
					dirty & /*cardClass*/ 8 && { class: /*cardClass*/ ctx[3] }
				])
			: {};

			if (dirty & /*$$scope, innerPdding, imgClass, img*/ 2070) {
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

function instance$1($$self, $$props, $$invalidate) {
	const omit_props_names = ["href","horizontal","reverse","img","padding","size"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	let { href = undefined } = $$props;
	let { horizontal = false } = $$props;
	let { reverse = false } = $$props;
	let { img = undefined } = $$props;
	let { padding = 'lg' } = $$props;
	let { size = 'sm' } = $$props;

	const paddings = {
		none: 'p-0',
		sm: 'p-4 sm:p-6 md:p-8',
		md: 'p-4 sm:p-5',
		lg: 'p-4 sm:p-6',
		xl: 'p-4 sm:p-8'
	};

	const sizes = {
		xs: 'max-w-xs',
		sm: 'max-w-sm',
		md: 'max-w-lg',
		lg: 'max-w-2xl',
		xl: 'max-w-screen-xl'
	};

	let innerPdding;
	let cardClass;
	let imgClass;

	$$self.$$set = $$new_props => {
		$$invalidate(14, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(5, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('href' in $$new_props) $$invalidate(0, href = $$new_props.href);
		if ('horizontal' in $$new_props) $$invalidate(6, horizontal = $$new_props.horizontal);
		if ('reverse' in $$new_props) $$invalidate(7, reverse = $$new_props.reverse);
		if ('img' in $$new_props) $$invalidate(1, img = $$new_props.img);
		if ('padding' in $$new_props) $$invalidate(8, padding = $$new_props.padding);
		if ('size' in $$new_props) $$invalidate(9, size = $$new_props.size);
		if ('$$scope' in $$new_props) $$invalidate(11, $$scope = $$new_props.$$scope);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*padding*/ 256) {
			$$invalidate(2, innerPdding = paddings[padding]);
		}

		$$invalidate(3, cardClass = classNames(
			'flex',
			sizes[size],
			reverse ? 'flex-col-reverse' : 'flex-col',
			horizontal && (reverse
			? 'md:flex-row-reverse md:max-w-xl'
			: 'md:flex-row md:max-w-xl'),
			href && 'hover:bg-gray-100 dark:hover:bg-gray-700',
			!img && innerPdding,
			$$props.class
		));

		if ($$self.$$.dirty & /*reverse, horizontal*/ 192) {
			$$invalidate(4, imgClass = classNames(reverse ? 'rounded-b-lg' : 'rounded-t-lg', horizontal && 'object-cover w-full h-96 md:h-auto md:w-48 md:rounded-none', horizontal && (reverse ? 'md:rounded-r-lg' : 'md:rounded-l-lg')));
		}
	};

	$$props = exclude_internal_props($$props);

	return [
		href,
		img,
		innerPdding,
		cardClass,
		imgClass,
		$$restProps,
		horizontal,
		reverse,
		padding,
		size,
		slots,
		$$scope
	];
}

let Component$1 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$1, create_fragment$1, safe_not_equal, {
			href: 0,
			horizontal: 6,
			reverse: 7,
			img: 1,
			padding: 8,
			size: 9
		});
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot(ctx) {
	let h5;
	let t0;
	let t1;
	let p;
	let t2;

	return {
		c() {
			h5 = element("h5");
			t0 = text("Noteworthy technology acquisitions 2021");
			t1 = space();
			p = element("p");
			t2 = text("Here are the biggest enterprise technology acquisitions of 2021 so far, in reverse chronological order.");
			this.h();
		},
		l(nodes) {
			h5 = claim_element(nodes, "H5", { class: true });
			var h5_nodes = children(h5);
			t0 = claim_text(h5_nodes, "Noteworthy technology acquisitions 2021");
			h5_nodes.forEach(detach);
			t1 = claim_space(nodes);
			p = claim_element(nodes, "P", { class: true });
			var p_nodes = children(p);
			t2 = claim_text(p_nodes, "Here are the biggest enterprise technology acquisitions of 2021 so far, in reverse chronological order.");
			p_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h5, "class", "mb-2 text-2xl font-bold tracking-tight text-gray-900 dark:text-white");
			attr(p, "class", "font-normal text-gray-700 dark:text-gray-400 leading-tight");
		},
		m(target, anchor) {
			insert_hydration(target, h5, anchor);
			append_hydration(h5, t0);
			insert_hydration(target, t1, anchor);
			insert_hydration(target, p, anchor);
			append_hydration(p, t2);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(h5);
			if (detaching) detach(t1);
			if (detaching) detach(p);
		}
	};
}

function create_fragment(ctx) {
	let card;
	let current;

	card = new Component$1({
			props: {
				href: "/cards",
				$$slots: { default: [create_default_slot] },
				$$scope: { ctx }
			}
		});

	return {
		c() {
			create_component(card.$$.fragment);
		},
		l(nodes) {
			claim_component(card.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(card, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const card_changes = {};

			if (dirty & /*$$scope*/ 2) {
				card_changes.$$scope = { dirty, ctx };
			}

			card.$set(card_changes);
		},
		i(local) {
			if (current) return;
			transition_in(card.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(card.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(card, detaching);
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
