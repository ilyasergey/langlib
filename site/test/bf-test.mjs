// Checks site/static/bf.js against the real example programs in
// Langlib/Examples/Brainfuck/ and against the semantic decisions in
// docs/brainfuck/spec.md.
//
//   cd site && node test/bf-test.mjs
//
// Exits 0 on success, 1 on the first failure.

import { readFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const require = createRequire(import.meta.url);
const here = dirname(fileURLToPath(import.meta.url));
const repo = join(here, '..', '..');
const BF = require(join(here, '..', 'static', 'bf.js'));

const example = (name) =>
  readFileSync(join(repo, 'Langlib', 'Examples', 'Brainfuck', name), 'utf8');

let failures = 0;
let checks = 0;

function check(label, actual, expected) {
  checks++;
  const ok = actual === expected;
  if (!ok) {
    failures++;
    console.error(`FAIL ${label}`);
    console.error(`  expected: ${JSON.stringify(expected)}`);
    console.error(`  actual:   ${JSON.stringify(actual)}`);
  } else {
    console.log(`ok   ${label}`);
  }
}

function runFile(name, input, opts) {
  return BF.run(example(name), input || '', opts || {});
}

// --- the example programs, as documented in README.md and the spec -------

check('hello.b prints Hello World!',
  runFile('hello.b').output, 'Hello World!\n');

check('add.b adds two ASCII digits (3 + 4)',
  runFile('add.b', '34').output, '7');

check('add.b adds two ASCII digits (2 + 5)',
  runFile('add.b', '25').output, '7');

check('rev.b reverses under --eof zero',
  runFile('rev.b', 'stressed', { eof: 'zero' }).output, 'desserts');

check('countdown.b counts down from 9',
  runFile('countdown.b').output, '9876543210\n');

check('alphabet.b prints the uppercase alphabet',
  runFile('alphabet.b').output, 'ABCDEFGHIJKLMNOPQRSTUVWXYZ\n');

check('cat.b copies input under --eof zero',
  runFile('cat.b', 'meow meow\n', { eof: 'zero' }).output, 'meow meow\n');

check('xkcd-random.b prints 4',
  runFile('xkcd-random.b').output, '4');

check('truth.b on 0 prints 0 and halts',
  runFile('truth.b', '0').output, '0');

{
  // A truth-machine on 1 prints 1 forever, so it must exhaust its fuel.
  const r = runFile('truth.b', '1', { fuel: 200000 });
  check('truth.b on 1 runs out of fuel', r.status, 'outoffuel');
  check('truth.b on 1 prints only ones',
    r.output.replace(/1/g, '').length, 0);
  checks++;
  if (r.output.length < 10) { failures++; console.error('FAIL truth.b on 1 printed too little'); }
  else console.log('ok   truth.b on 1 keeps printing');
}

{
  // Erik Bosman's 505-byte quine prints itself.
  const src = example('quine.b');
  const r = BF.run(src, '', { fuel: 50000000 });
  check('quine.b reproduces itself', r.output, src);
}

// --- the semantic decisions, one test each ------------------------------

check('cells wrap at 255 (decision 1: 0 - 1 = 255)',
  BF.run('-.').bytes[0], 255);

check('cells wrap at 0 (decision 1: 255 + 1 = 0)',
  BF.run('-+.').bytes[0], 0);

{
  // Decision 2: the tape is unbounded to the right; walk well past any
  // fixed allocation and come back.
  const far = '>'.repeat(5000) + '+' + '<'.repeat(5000) + '.';
  const r = BF.run(far);
  check('tape grows on demand (decision 2)', r.status, 'halted');
  check('tape starts zeroed after growth (decision 2)', r.bytes[0], 0);
  const back = '>'.repeat(5000) + '+++++++++++++++++++++++++++++++++++++++++++++++++' +
    '.'; // 49 = ASCII '1'
  check('a far cell holds what was written (decision 2)',
    BF.run(back).output, '1');
}

{
  // Decision 3: moving left of cell 0 is a runtime error.
  const r = BF.run('<');
  check('moving left of cell 0 errors (decision 3)', r.status, 'error');
  checks++;
  if (!/left of cell 0/.test(r.error || '')) {
    failures++; console.error('FAIL error message names the cause');
  } else console.log('ok   error message names the cause');
}

// Decision 4: the three EOF conventions.
check('EOF leaves the cell unchanged by default (decision 4)',
  BF.run('+++,.', '').bytes[0], 3);
check('--eof zero stores 0 (decision 4)',
  BF.run('+++,.', '', { eof: 'zero' }).bytes[0], 0);
check('--eof minus1 stores 255 (decision 4)',
  BF.run('+++,.', '', { eof: 'minus1' }).bytes[0], 255);
check('input is consumed before EOF applies (decision 4)',
  BF.run(',.,.', 'hi', { eof: 'zero' }).output, 'hi');

// Decision 5: no newline translation; byte 10 goes straight through.
check('newlines pass through untouched (decision 5)',
  BF.run(',.', '\n').bytes[0], 10);

// Non-command characters are comments; only unmatched brackets are errors.
check('non-commands are comments',
  BF.run('++ this is a comment! +.').bytes[0], 3);
check('unmatched [ is a parse error', BF.run('[').status, 'parseerror');
check('unmatched ] is a parse error', BF.run(']').status, 'parseerror');
check('the empty program halts', BF.run('').status, 'halted');

// Fuel is charged per command and per loop-condition check, so a loop of
// n iterations over a k-command body costs n*(k+2) + 1 steps.
{
  // "+++[-]" : 3 increments, then [ check, then 3 * (- , ] check), then the
  // final [ ... ] pair check. Count it exactly.
  const m = new BF.Machine('+++[-]', '');
  m.run();
  //  + + +      = 3
  //  [ (enter)  = 1
  //  - ]  x 3   = 6   (the third ] check sees zero and falls through)
  check('fuel is charged per command and loop check', m.steps, 10);
}

console.log(`\n${checks - failures}/${checks} checks passed`);
process.exit(failures === 0 ? 0 : 1);
