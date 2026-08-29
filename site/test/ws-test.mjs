// Checks site/static/ws.js against the example programs in
// Langlib/Examples/Whitespace/ and the decisions in docs/whitespace/spec.md.
//
//   cd site && node test/ws-test.mjs

import { readFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const require = createRequire(import.meta.url);
const here = dirname(fileURLToPath(import.meta.url));
const repo = join(here, '..', '..');
const WS = require(join(here, '..', 'static', 'ws.js'));

const example = (name) =>
  readFileSync(join(repo, 'Langlib', 'Examples', 'Whitespace', name), 'latin1');

let failures = 0, checks = 0;
function check(label, actual, expected) {
  checks++;
  if (actual !== expected) {
    failures++;
    console.error(`FAIL ${label}\n  expected: ${JSON.stringify(expected)}\n  actual:   ${JSON.stringify(actual)}`);
  } else console.log(`ok   ${label}`);
}

// Assemble a program from a readable notation: S = space, T = tab, L = LF.
const asm = (s) => s.replace(/[^STL]/g, '')
  .replace(/S/g, ' ').replace(/T/g, '\t').replace(/L/g, '\n');

// --- example programs ---------------------------------------------------

check('hello.ws prints Hello, World!',
  WS.run(example('hello.ws')).output, 'Hello, World!\n');

check('count.ws prints 1 to 10',
  WS.run(example('count.ws')).output, '1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n');

check('add.ws adds two numbers',
  WS.run(example('add.ws'), '17\n25\n').output, '42\n');

check('fact.ws computes 5!',
  WS.run(example('fact.ws'), '5\n').output, '120\n');

check('greet.ws greets a name',
  WS.run(example('greet.ws'), 'Ada\n').output, 'Hello, Ada!\n');

{
  const r = WS.run(example('cat.ws'), 'meow\n');
  check('cat.ws copies its input', r.output, 'meow\n');
  // Whitespace cannot test for EOF, so cat ends with a runtime error by design.
  check('cat.ws ends with a read error at EOF', r.status, 'error');
}

check('truth.ws on 0 prints 0',
  WS.run(example('truth.ws'), '0\n').output, '0');

{
  const r = WS.run(example('truth.ws'), '1\n', { fuel: 20000 });
  check('truth.ws on 1 diverges', r.status, 'outoffuel');
  check('truth.ws on 1 prints only ones and newlines',
    r.output.replace(/[1\n]/g, '').length, 0);
}

// --- semantic decisions -------------------------------------------------

// Decision 2: floor division, mod takes the sign of the divisor.
const arith = (a, b, op) => WS.run(asm(
  'SS' + a + 'L' + 'SS' + b + 'L' + op + 'TLST' + 'LLL'
)).output;
// numbers: sign token then binary digits, MSB first, so -7 = T TTT and
// 2 = S TS (sign, then 10 in binary).
check('-7 div 2 = -4 (decision 2)', arith('TTTT', 'STS', 'TSTS'), '-4');
check('-7 mod 2 = 1 (decision 2)', arith('TTTT', 'STS', 'TSTT'), '1');
check('7 mod -2 = -1 (decision 2)', arith('STTT', 'TTS', 'TSTT'), '-1');

check('subtraction is second minus top (decision 3)',
  arith('STSSS', 'STT', 'TSST'), '5');   // 8 - 3

{
  const r = WS.run(asm('SS' + 'ST' + 'L' + 'SS' + 'SL' + 'TSTS' + 'LLL'));
  check('division by zero is a runtime error (decision 2)', r.status, 'error');
}

// Decision 4: the first definition of a duplicated label wins.
{
  // mark A; push 1; outnum; jmp B;   mark A (again); push 2; outnum;  mark B; end
  const p = asm('LSS' + 'SL' +           // mark ""
                'SS' + 'ST' + 'L' + 'TLST' +   // push 1, outnum
                'LSL' + 'TL' +           // jmp label "T"
                'LSS' + 'SL' +           // mark "" again (ignored)
                'LSS' + 'TL' + 'LLL');   // mark "T", end
  check('the first definition of a label wins (decision 4)', WS.run(p).output, '1');
}

check('the empty label is a legal, distinct label (decision 4)',
  WS.run(asm('LSL' + 'L' + 'SS' + 'STSTS' + 'L' + 'TLSS' + 'LSSL' + 'LLL')).status,
  'halted');

{
  // An undefined label reached at jump time is a runtime error, not a parse
  // error, and one that is never reached is fine.
  check('an undefined label errors at jump time (decision 4)',
    WS.run(asm('LSL' + 'SSL' + 'LLL')).status, 'error');
  // push 0; jz to a defined label, so the undefined branch is never taken.
  check('an unreached undefined label is harmless (decision 4)',
    WS.run(asm('SS' + 'SL' + 'LTS' + 'SL' + 'LSL' + 'TTL' + 'LSS' + 'SL' + 'LLL')).status,
    'halted');
}

// Decision 5: copy out of range errors, slide clamps.
check('copy with an out of range index errors (decision 5)',
  WS.run(asm('SS' + 'ST' + 'L' + 'STS' + 'STSL' + 'LLL')).status, 'error');
{
  // push 1; push 2; push 3; slide 99 -> keeps only the 3
  const p = asm('SS' + 'STL' + 'SS' + 'SSTSL' + 'SS' + 'SSTTL' +
                'STL' + 'STTSSSTTL' + 'TLST' + 'LLL');
  check('slide clamps to the stack depth (decision 5)', WS.run(p).output, '3');
}

// Decision 6: the heap is total and defaults to 0; negative addresses error.
check('retrieving an unwritten address gives 0 (decision 6)',
  WS.run(asm('SS' + 'STSSSSSSL' + 'TTT' + 'TLST' + 'LLL')).output, '0');
check('a negative heap address is a runtime error (decision 6)',
  WS.run(asm('SS' + 'TTL' + 'TTT' + 'LLL')).status, 'error');

// Decision 7 and 8.
check('popping an empty stack is a runtime error (decision 7)',
  WS.run(asm('SLL' + 'LLL')).status, 'error');
check('return with an empty call stack errors (decision 7)',
  WS.run(asm('LTL' + 'LLL')).status, 'error');
check('running off the end is a runtime error (decision 8)',
  WS.run(asm('SS' + 'STL')).status, 'error');
check('the empty program is a runtime error (decision 8)',
  WS.run('').status, 'error');

// Decision 9: number literals need a sign token; both signs of zero work.
check('a number with no sign token is a parse error (decision 9)',
  WS.run(asm('SS' + 'L' + 'LLL')).status, 'parseerror');
check('[Space][LF] denotes 0 (decision 9)',
  WS.run(asm('SS' + 'SL' + 'TLST' + 'LLL')).output, '0');
check('[Tab][LF] also denotes 0 (decision 9)',
  WS.run(asm('SS' + 'TL' + 'TLST' + 'LLL')).output, '0');
check('an unterminated number is a parse error (decision 9)',
  WS.run(asm('SS' + 'ST')).status, 'parseerror');

// Decision 10: outchar wants a byte.
check('outchar outside 0..255 is a runtime error (decision 10)',
  WS.run(asm('SS' + 'STSSSSSSSSSL' + 'TLSS' + 'LLL')).status, 'error');

// Decision 12: reading at end of input is a runtime error.
check('readchar at end of input errors (decision 12)',
  WS.run(asm('SS' + 'SL' + 'TLTS' + 'LLL'), '').status, 'error');

// Decision 14: CR is a comment character, so CRLF files parse identically.
check('CR is a comment character (decision 14)',
  WS.run(example('hello.ws').replace(/\n/g, '\r\n')).output, 'Hello, World!\n');
check('visible text is a comment',
  WS.run('this is a comment ' + example('hello.ws')).output.slice(-7), 'World!\n');

// The glyph rendering used by the playground.
check('glyphs render the invisible source',
  WS.glyphs(' \t\n'), '·→¶\n');

console.log(`\n${checks - failures}/${checks} checks passed`);
process.exit(failures === 0 ? 0 : 1);
