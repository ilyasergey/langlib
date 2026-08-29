// Checks site/static/df.js against docs/deadfish/spec.md and the examples in
// Langlib/Examples/Deadfish/.
//
//   cd site && node test/df-test.mjs

import { readFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const require = createRequire(import.meta.url);
const here = dirname(fileURLToPath(import.meta.url));
const repo = join(here, '..', '..');
const DF = require(join(here, '..', 'static', 'df.js'));

const example = (name) =>
  readFileSync(join(repo, 'Langlib', 'Examples', 'Deadfish', name), 'utf8');

let failures = 0, checks = 0;
function check(label, actual, expected) {
  checks++;
  if (actual !== expected) {
    failures++;
    console.error(`FAIL ${label}\n  expected: ${JSON.stringify(expected)}\n  actual:   ${JSON.stringify(actual)}`);
  } else console.log(`ok   ${label}`);
}

// The wiki's mandatory interpreter tests, quoted in the spec page.
check('iissso prints 0 (16 squared resets)', DF.run('iissso').output, '0\n');
check('diissisdo prints 288', DF.run('diissisdo').output, '288\n');
check('iissisdo prints 288', DF.run('iissisdo').output, '288\n');
check('289 minus 33 lands exactly on 256 and resets',
  DF.run('iissis' + 'd'.repeat(33) + 'o').output, '0\n');

// Semantic decisions.
check('the accumulator starts at 0 (spec: the machine)', DF.run('o').output, '0\n');
check('squaring can jump over 256 (decision 2)', DF.run('iiiiiiiiiiiiiiiiiso').output, '289\n');
check('the reset is exact, not a clamp (decision 2)', DF.run('iiiiiiiiiiiiiiiiisdo').output, '288\n');
check('d at 0 gives -1 which resets (decision 2)', DF.run('do').output, '0\n');
check('o prints decimal and a newline (decision 3)', DF.run('iiio').output, '3\n');
check('any other character prints a bare newline (decision 4)',
  DF.run('i?o').output, '\n1\n');
check('h is not a halt command (decision 4)', DF.run('ihio').output, '\n2\n');
check('commands are case sensitive (decision 4)', DF.run('Io').output, '\n0\n');
check('the accumulator is unbounded (decision 1)',
  DF.run('iii' + 's'.repeat(6) + 'o').output, (3n ** 64n).toString() + '\n');

// Fuel: one unit per command, so an n-character program halts in n steps.
{
  const m = new DF.Machine('iiisdo');
  m.run();
  check('one fuel unit per command', m.steps, 6);
  check('a straight-line program always halts', m.status, 'halted');
}
check('a short fuel budget is observable', DF.run('iiii', { fuel: 2 }).status, 'outoffuel');

// The example programs.
check('xkcd-random.df prints 4', DF.run(example('xkcd-random.df')).output, '4\n\n');  // the file's own trailing newline prints one too
check('powers.df squares its way into the reset',
  DF.run(example('powers.df')).output, '2\n4\n16\n0\n0\n\n');
{
  // hello.df prints the ASCII codes of "Hello, world!", one per line, with
  // the file's own newlines each contributing a bare newline.
  const out = DF.run(example('hello.df')).output;
  const codes = out.split('\n').filter((s) => s.length > 0);
  check('hello.df prints the codes of Hello, world!',
    codes.map((n) => String.fromCharCode(Number(n))).join(''), 'Hello, world!');
}

console.log(`\n${checks - failures}/${checks} checks passed`);
process.exit(failures === 0 ? 0 : 1);
