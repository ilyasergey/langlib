// Runs static/playground.js against the real generated markup, in the tiny DOM
// from test/dom.mjs, and drives the playgrounds the way a reader would: pick an
// example, press Run, read the output pane, step, reset.
//
//   cd site && lake exe langlib-site && node test/playground-test.mjs

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import vm from 'node:vm';
import { parseDocument, Ev } from './dom.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const site = join(here, '..');
const out = join(site, 'out');

let failures = 0, checks = 0;
function check(label, ok, detail) {
  checks++;
  if (!ok) { failures++; console.error(`FAIL ${label}${detail ? '\n  ' + detail : ''}`); }
  else console.log(`ok   ${label}`);
}

function loadPage(file) {
  const html = readFileSync(join(out, file), 'utf8');
  const document = parseDocument(html);

  const sandbox = {
    document,
    console,
    setInterval, clearInterval, setTimeout, clearTimeout,
    TextEncoder, TextDecoder,
    Event: Ev,
    Array, Object, JSON, Math, Number, String, Boolean, BigInt, Map, Set,
    Uint8Array, Int32Array, Infinity, NaN
  };
  vm.createContext(sandbox);
  sandbox.window = sandbox;
  sandbox.globalThis = sandbox;

  const listeners = [];
  document.addEventListener = (type, fn) => { if (type === 'DOMContentLoaded') listeners.push(fn); };

  for (const src of ['bf.js', 'ws.js', 'df.js', 'playground.js']) {
    vm.runInContext(readFileSync(join(site, 'static', src), 'utf8'), sandbox, { filename: src });
  }
  // fire DOMContentLoaded, which is what mounts the playgrounds
  listeners.forEach((fn) => fn());
  return { document, sandbox };
}

function pg(document, kind) {
  return document.querySelector(`.pg[data-kind="${kind}"]`);
}
const role = (root, name) => root.querySelector(`[data-role="${name}"]`);

function press(root, name) { role(root, name).click(); }

function pick(root, index) {
  const sel = role(root, 'example');
  sel.value = String(index);
  sel.dispatchEvent(new Ev('change'));
}

function setSpeed(root, v) {
  const s = role(root, 'speed');
  s.value = String(v);
  s.dispatchEvent(new Ev('input'));
}

// ---------------------------------------------------------------- brainfuck

{
  const { document } = loadPage(join('playground', 'index.html'));
  const root = pg(document, 'brainfuck');
  check('the brainfuck playground mounts', !!root);

  const picker = role(root, 'example');
  check('the example menu is populated from the embedded programs',
    picker.children.length === 9, `${picker.children.length} options`);
  check('the first example is selected on load',
    role(root, 'program').value.includes('Hello World'));
  check('the example note is shown',
    role(root, 'example-note').textContent.length > 20);

  setSpeed(root, 6);            // all at once
  press(root, 'run');
  check('Run on hello.b prints Hello World!',
    role(root, 'output').textContent === 'Hello World!\n',
    JSON.stringify(role(root, 'output').textContent));
  check('the status line says halted',
    role(root, 'status').textContent.startsWith('halted'),
    role(root, 'status').textContent);
  check('the step counter is shown',
    /\d/.test(role(root, 'steps').textContent), role(root, 'steps').textContent);
  check('the tape is rendered',
    role(root, 'tape').children.length > 0);
  check('the tape marks the cell under the pointer',
    role(root, 'tape').querySelector('.cell.here') !== null);
  check('the pointer readout names a cell',
    /pointer at cell \d+/.test(role(root, 'pointer').textContent),
    role(root, 'pointer').textContent);

  // rev.b, which needs its preset input and the store-0 EOF convention
  pick(root, 2);
  check('picking rev.b loads its input', role(root, 'input').value === 'stressed');
  check('picking rev.b switches the EOF convention', role(root, 'eof').value === 'zero');
  press(root, 'run');
  check('Run on rev.b reverses the word',
    role(root, 'output').textContent === 'desserts',
    JSON.stringify(role(root, 'output').textContent));

  // the EOF selector really is wired to the interpreter: `+++,.` reads at end
  // of input and prints whatever the convention put in the cell.
  const readAtEof = (mode) => {
    role(root, 'program').value = '+++,.';
    role(root, 'program').dispatchEvent(new Ev('input'));
    role(root, 'input').value = '';
    role(root, 'input').dispatchEvent(new Ev('input'));
    role(root, 'eof').value = mode;
    role(root, 'eof').dispatchEvent(new Ev('change'));
    press(root, 'run');
    return role(root, 'output').textContent.charCodeAt(0);
  };
  check('EOF "leave the cell" keeps the 3 that was there', readAtEof('unchanged') === 3);
  check('EOF "store 0" stores 0', readAtEof('zero') === 0);
  check('EOF "store 255" stores 255', readAtEof('minus1') === 255);

  // stepping
  pick(root, 0);
  press(root, 'reset');
  check('Reset clears the output', role(root, 'output').textContent === '');
  for (let i = 0; i < 10; i++) press(root, 'step');
  check('ten Steps advance the machine ten steps',
    role(root, 'steps').textContent.startsWith('10 '),
    role(root, 'steps').textContent);
  check('the instruction pane highlights the current command',
    role(root, 'code').querySelector('mark') !== null);
  check('stepping has not finished the program',
    role(root, 'status').textContent.startsWith('running'),
    role(root, 'status').textContent);

  // a parse error reaches the reader
  role(root, 'program').value = '+++[';
  role(root, 'program').dispatchEvent(new Ev('input'));
  press(root, 'run');
  check('an unmatched bracket is reported as a parse error',
    role(root, 'status').textContent.startsWith('parse error'),
    role(root, 'status').textContent);

  // a runtime error too
  role(root, 'program').value = '<';
  role(root, 'program').dispatchEvent(new Ev('input'));
  press(root, 'run');
  check('moving left of cell 0 is reported as a runtime error',
    role(root, 'status').textContent.includes('left of cell 0'),
    role(root, 'status').textContent);
}

// --------------------------------------------------------------- whitespace

{
  const { document } = loadPage(join('playground', 'index.html'));
  const root = pg(document, 'whitespace');
  check('the whitespace playground mounts', !!root);

  check('the glyph pane makes the program visible',
    role(root, 'glyphs').textContent.includes('·') &&
    role(root, 'glyphs').textContent.includes('→'),
    JSON.stringify(role(root, 'glyphs').textContent.slice(0, 40)));
  check('the instruction listing is shown before running',
    role(root, 'listing').textContent.includes('push'));

  setSpeed(root, 6);
  press(root, 'run');
  check('Run on hello.ws prints Hello, World!',
    role(root, 'output').textContent === 'Hello, World!\n',
    JSON.stringify(role(root, 'output').textContent));

  // fact.ws exercises the call stack and the heap
  const picker = role(root, 'example');
  const names = picker.children.map((o) => o.textContent);
  const factIndex = names.findIndex((n) => n.startsWith('fact.ws'));
  pick(root, factIndex);
  check('picking fact.ws loads its input', role(root, 'input').value === '5\n');
  press(root, 'run');
  check('Run on fact.ws prints 120',
    role(root, 'output').textContent === '120\n',
    JSON.stringify(role(root, 'output').textContent));
  check('the heap pane shows what the program stored',
    role(root, 'heap').textContent.includes('['),
    JSON.stringify(role(root, 'heap').textContent));

  // stepping shows the stack mid-run
  pick(root, factIndex);
  press(root, 'reset');
  let sawStack = false;
  for (let i = 0; i < 12; i++) {
    press(root, 'step');
    if (role(root, 'stack').textContent.includes('top')) sawStack = true;
  }
  check('stepping fact.ws shows values on the stack', sawStack,
    JSON.stringify(role(root, 'stack').textContent));

  // cat.ws is documented to fail at end of input, and should say so
  const catIndex = names.findIndex((n) => n.startsWith('cat.ws'));
  pick(root, catIndex);
  press(root, 'run');
  check('cat.ws copies its input', role(root, 'output').textContent === 'meow\n');
  check('cat.ws then reports the documented read error',
    role(root, 'status').textContent.includes('end of input'),
    role(root, 'status').textContent);
}

// ----------------------------------------------------------------- deadfish

{
  const { document } = loadPage(join('playground', 'index.html'));
  const root = pg(document, 'deadfish');
  check('the deadfish playground mounts', !!root);

  setSpeed(root, 6);
  press(root, 'run');
  const codes = role(root, 'output').textContent.split('\n').filter((s) => s.length);
  check('Run on hello.df prints the codes of a greeting',
    codes.map((n) => String.fromCharCode(Number(n))).join('') === 'Hello, world!',
    role(root, 'output').textContent.slice(0, 40));
  check('the accumulator is shown', /\d/.test(role(root, 'acc').textContent));

  role(root, 'program').value = 'iissso';
  role(root, 'program').dispatchEvent(new Ev('input'));
  press(root, 'run');
  check('iissso prints 0, because 16 squared is 256',
    role(root, 'output').textContent === '0\n',
    JSON.stringify(role(root, 'output').textContent));

  role(root, 'program').value = 'iissisdo';
  role(root, 'program').dispatchEvent(new Ev('input'));
  press(root, 'run');
  check('iissisdo prints 288, because 17 squared sails past the check',
    role(root, 'output').textContent === '288\n',
    JSON.stringify(role(root, 'output').textContent));
}

// ----------------------------------------- the copy embedded on other pages

for (const [page, kind] of [['index.html', 'brainfuck'],
                            [join('brainfuck', 'index.html'), 'brainfuck'],
                            [join('whitespace', 'index.html'), 'whitespace'],
                            [join('deadfish', 'index.html'), 'deadfish']]) {
  const { document } = loadPage(page);
  const root = pg(document, kind);
  check(`/${page} mounts its ${kind} playground`, !!root);
  if (!root) continue;
  setSpeed(root, 6);
  press(root, 'run');
  check(`/${page} runs its first example`,
    role(root, 'output').textContent.length > 0 &&
    role(root, 'status').textContent.startsWith('halted'),
    role(root, 'status').textContent);
}

console.log(`\n${checks - failures}/${checks} checks passed`);
process.exit(failures === 0 ? 0 : 1);
