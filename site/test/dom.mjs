// A DOM small enough to fit in one file and large enough to run
// static/playground.js against the real generated markup. It exists because
// there is no browser here and no DOM library installed, and "the playground
// works" is worth more as a test than as a claim.
//
// Supported: parsing the generator's HTML, getElementById, querySelector and
// querySelectorAll over compound selectors (tag, .class, [attr], [attr="v"]),
// textContent, innerHTML (re-parsed), value, appendChild, createElement,
// addEventListener/dispatchEvent, and the layout properties playground.js
// reads when it scrolls a highlight into view.

const VOID = new Set(['area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input',
  'link', 'meta', 'param', 'source', 'track', 'wbr']);
const RAW = new Set(['script', 'style', 'textarea']);

const ENTITIES = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", nbsp: ' ' };

function decode(s) {
  return s.replace(/&(#x?[0-9a-fA-F]+|[a-zA-Z]+);/g, (all, body) => {
    if (body[0] === '#') {
      const n = body[1] === 'x' || body[1] === 'X'
        ? parseInt(body.slice(2), 16) : parseInt(body.slice(1), 10);
      return Number.isFinite(n) ? String.fromCodePoint(n) : all;
    }
    return body in ENTITIES ? ENTITIES[body] : all;
  });
}

class TextNode {
  constructor(text) { this.nodeType = 3; this.data = text; this.parent = null; }
  get textContent() { return this.data; }
}

export class Element {
  constructor(tag) {
    this.nodeType = 1;
    this.tagName = tag.toUpperCase();
    this.tag = tag.toLowerCase();
    this.attrs = new Map();
    this.children = [];
    this.parent = null;
    this.listeners = new Map();
    this._value = undefined;
    // playground.js consults these when deciding whether to scroll; zero is a
    // consistent answer and keeps the code path exercised.
    this.offsetTop = 0;
    this.scrollTop = 0;
    this.clientHeight = 100;
  }

  getAttribute(n) { return this.attrs.has(n) ? this.attrs.get(n) : null; }
  setAttribute(n, v) { this.attrs.set(n, String(v)); }
  hasAttribute(n) { return this.attrs.has(n); }
  removeAttribute(n) { this.attrs.delete(n); }

  get id() { return this.getAttribute('id') || ''; }
  get className() { return this.getAttribute('class') || ''; }
  set className(v) { this.setAttribute('class', v); }
  get classes() { return this.className.split(/\s+/).filter(Boolean); }
  get hidden() { return this.hasAttribute('hidden'); }
  set hidden(v) { if (v) this.setAttribute('hidden', ''); else this.removeAttribute('hidden'); }

  appendChild(child) { child.parent = this; this.children.push(child); return child; }

  get textContent() {
    return this.children.map((c) => c.textContent).join('');
  }
  set textContent(v) {
    this.children = [];
    this.appendChild(new TextNode(String(v)));
  }

  get innerHTML() { return serialize(this.children); }
  set innerHTML(v) {
    this.children = parseFragment(String(v), this);
  }

  // Form controls: textarea takes its initial value from its text content.
  get value() {
    if (this._value !== undefined) return this._value;
    if (this.tag === 'textarea') return this.textContent;
    return this.getAttribute('value') || '';
  }
  set value(v) { this._value = String(v); }

  addEventListener(type, fn) {
    if (!this.listeners.has(type)) this.listeners.set(type, []);
    this.listeners.get(type).push(fn);
  }
  dispatchEvent(ev) {
    for (const fn of this.listeners.get(ev.type) || []) fn.call(this, ev);
    return true;
  }
  click() { this.dispatchEvent(new Ev('click')); }
  scrollIntoView() {}

  *walk() {
    for (const c of this.children) {
      if (c.nodeType === 1) { yield c; yield* c.walk(); }
    }
  }

  querySelector(sel) { for (const el of this.querySelectorAll(sel)) return el; return null; }
  querySelectorAll(sel) {
    const parts = sel.split(',').map((s) => s.trim()).filter(Boolean).map(parseCompound);
    const out = [];
    for (const el of this.walk()) {
      if (parts.some((p) => matches(el, p))) out.push(el);
    }
    return out;
  }
}

export class Ev {
  constructor(type) { this.type = type; }
}

// --- selectors ----------------------------------------------------------

function parseCompound(sel) {
  // Only compound selectors are needed: tag, .class, [attr], [attr="value"],
  // and [attr^="value"], concatenated. No combinators.
  const spec = { tag: null, classes: [], attrs: [] };
  const re = /^(?:([a-zA-Z][\w-]*)|\.([\w-]+)|\[([\w-]+)(?:([~^]?=)"([^"]*)")?\])/;
  let rest = sel;
  while (rest.length) {
    const m = re.exec(rest);
    if (!m) throw new Error('unsupported selector: ' + sel);
    if (m[1]) spec.tag = m[1].toLowerCase();
    else if (m[2]) spec.classes.push(m[2]);
    else spec.attrs.push({ name: m[3], op: m[4], value: m[5] });
    rest = rest.slice(m[0].length);
  }
  return spec;
}

function matches(el, spec) {
  if (spec.tag && el.tag !== spec.tag) return false;
  for (const c of spec.classes) if (!el.classes.includes(c)) return false;
  for (const a of spec.attrs) {
    if (!el.hasAttribute(a.name)) return false;
    if (!a.op) continue;
    const v = el.getAttribute(a.name);
    if (a.op === '=' && v !== a.value) return false;
    if (a.op === '^=' && !v.startsWith(a.value)) return false;
    if (a.op === '~=' && !v.split(/\s+/).includes(a.value)) return false;
  }
  return true;
}

// --- parsing ------------------------------------------------------------

function parseFragment(html, parentForRoots) {
  const root = new Element('#fragment');
  const stack = [root];
  let i = 0;
  const push = (node) => { stack[stack.length - 1].appendChild(node); };

  while (i < html.length) {
    const lt = html.indexOf('<', i);
    if (lt < 0) { if (i < html.length) push(new TextNode(decode(html.slice(i)))); break; }
    if (lt > i) push(new TextNode(decode(html.slice(i, lt))));

    if (html.startsWith('<!--', lt)) {
      const end = html.indexOf('-->', lt);
      i = end < 0 ? html.length : end + 3;
      continue;
    }
    if (html.startsWith('<!', lt)) {
      const end = html.indexOf('>', lt);
      i = end < 0 ? html.length : end + 1;
      continue;
    }
    if (html.startsWith('</', lt)) {
      const end = html.indexOf('>', lt);
      const name = html.slice(lt + 2, end).trim().toLowerCase();
      for (let k = stack.length - 1; k > 0; k--) {
        if (stack[k].tag === name) { stack.length = k; break; }
      }
      i = end + 1;
      continue;
    }

    const end = findTagEnd(html, lt);
    const inner = html.slice(lt + 1, end).replace(/\/$/, '');
    const sp = inner.search(/[\s]/);
    const name = (sp < 0 ? inner : inner.slice(0, sp)).toLowerCase();
    const el = new Element(name);
    if (sp >= 0) {
      const attrRe = /([\w:-]+)(?:\s*=\s*"([^"]*)")?/g;
      let m;
      while ((m = attrRe.exec(inner.slice(sp))) !== null) {
        el.setAttribute(m[1], m[2] === undefined ? '' : decode(m[2]));
      }
    }
    push(el);
    i = end + 1;

    if (VOID.has(name) || html[end - 1] === '/') continue;
    if (RAW.has(name)) {
      const close = html.toLowerCase().indexOf('</' + name, i);
      const text = close < 0 ? html.slice(i) : html.slice(i, close);
      // script and style hold raw text; textarea's content is entity-encoded
      el.appendChild(new TextNode(name === 'textarea' ? decode(text) : text));
      i = close < 0 ? html.length : html.indexOf('>', close) + 1;
      continue;
    }
    stack.push(el);
  }
  const kids = root.children;
  for (const k of kids) k.parent = parentForRoots;
  return kids;
}

function findTagEnd(html, from) {
  let inQuote = false;
  for (let i = from + 1; i < html.length; i++) {
    const c = html[i];
    if (c === '"') inQuote = !inQuote;
    else if (c === '>' && !inQuote) return i;
  }
  return html.length;
}

function escapeText(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function serialize(nodes) {
  return nodes.map((n) => {
    if (n.nodeType === 3) return escapeText(n.data);
    const attrs = [...n.attrs].map(([k, v]) => ` ${k}="${v}"`).join('');
    if (VOID.has(n.tag)) return `<${n.tag}${attrs}>`;
    return `<${n.tag}${attrs}>${serialize(n.children)}</${n.tag}>`;
  }).join('');
}

// --- document -----------------------------------------------------------

export function parseDocument(html) {
  const doc = new Element('#document');
  doc.children = parseFragment(html, doc);

  doc.createElement = (tag) => new Element(tag);
  doc.getElementById = (id) => {
    for (const el of doc.walk()) if (el.id === id) return el;
    return null;
  };
  doc.readyState = 'loading';
  doc.documentElement = doc.querySelector('html') || new Element('html');
  doc.body = doc.querySelector('body') || new Element('body');
  return doc;
}
