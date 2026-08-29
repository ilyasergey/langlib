// Checks the generated site in site/out/: internal links resolve, no Markdown
// leaks through unrendered, every page has its metadata, the playground markup
// has every element playground.js looks for, and the embedded example programs
// are byte-for-byte the files in Langlib/Examples/.
//
//   cd site && lake exe langlib-site && node test/site-test.mjs

import { readFileSync, readdirSync, existsSync, statSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join, relative } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const site = join(here, '..');
const repo = join(site, '..');
const out = join(site, 'out');

let failures = 0, checks = 0;
function check(label, ok, detail) {
  checks++;
  if (!ok) { failures++; console.error(`FAIL ${label}${detail ? '\n  ' + detail : ''}`); }
  else console.log(`ok   ${label}`);
}

if (!existsSync(out)) {
  console.error('site/out/ does not exist; run `lake exe langlib-site` first');
  process.exit(1);
}

function walk(dir) {
  return readdirSync(dir).flatMap((name) => {
    const p = join(dir, name);
    return statSync(p).isDirectory() ? walk(p) : [p];
  });
}

const files = walk(out);
const htmlFiles = files.filter((f) => f.endsWith('.html'));
const rel = (f) => '/' + relative(out, f).split('\\').join('/');

check('the generator produced pages', htmlFiles.length >= 18,
  `found ${htmlFiles.length}`);

// --- CNAME and the other deploy furniture -------------------------------

check('CNAME lands in the output with exactly the domain',
  existsSync(join(out, 'CNAME')) &&
  readFileSync(join(out, 'CNAME'), 'utf8').trim() === 'langlib.wtf',
  existsSync(join(out, 'CNAME')) ? JSON.stringify(readFileSync(join(out, 'CNAME'), 'utf8')) : 'missing');

['style.css', 'site.js', 'bf.js', 'ws.js', 'df.js', 'playground.js', 'favicon.svg',
 'robots.txt', 'sitemap.xml', '404.html'].forEach((f) => {
  check(`${f} is in the output`, existsSync(join(out, f)));
});

// --- per-page checks ----------------------------------------------------

const pages = new Map();          // "/brainfuck/" -> { html, ids }
for (const f of htmlFiles) {
  const html = readFileSync(f, 'utf8');
  const url = rel(f).replace(/index\.html$/, '');
  const ids = new Set();
  for (const m of html.matchAll(/\sid="([^"]+)"/g)) ids.add(m[1]);
  pages.set(url, { html, ids, file: f });
}

for (const [url, page] of pages) {
  const label = url;
  check(`${label} has a title`, /<title>[^<]+<\/title>/.test(page.html));
  check(`${label} has a description`,
    /<meta name="description" content="[^"]+">/.test(page.html));
  check(`${label} links the stylesheet`,
    page.html.includes('<link rel="stylesheet" href="/style.css">'));
  check(`${label} has one h1`, (page.html.match(/<h1[ >]/g) || []).length === 1);
}

// --- nothing leaked through the Markdown renderer -----------------------

// Only look inside <main>, since the shell legitimately contains other text.
function mainOf(html) {
  const m = html.match(/<main[^>]*>([\s\S]*)<\/main>/);
  return m ? m[1] : '';
}
// ...and outside <pre> blocks and <script> data, where raw characters are the point.
function proseOf(html) {
  return mainOf(html)
    .replace(/<pre[\s\S]*?<\/pre>/g, '')
    .replace(/<script[\s\S]*?<\/script>/g, '')
    .replace(/<code>[\s\S]*?<\/code>/g, '');
}

const leaks = [
  ['unrendered bold', /\*\*/],
  ['unrendered inline code', /`[^`\n]+`/],
  ['unrendered link', /\]\(/],
  ['unrendered heading', /(^|\n)#{1,6} /],
  ['unrendered table row', /(^|\n)\s*\|[^\n]*\|/],
  ['unrendered list bullet', /(^|\n)\s*[*+] /],
];
for (const [url, page] of pages) {
  const prose = proseOf(page.html);
  for (const [what, re] of leaks) {
    const m = prose.match(re);
    check(`${url} has no ${what}`, !m, m ? JSON.stringify(m[0].slice(0, 70)) : '');
  }
}

// --- internal links resolve --------------------------------------------

let linkChecks = 0, linkFailures = [];
for (const [url, page] of pages) {
  for (const m of page.html.matchAll(/href="([^"]+)"/g)) {
    const href = m[1];
    if (!href.startsWith('/')) continue;      // external, or a bare fragment
    linkChecks++;
    const [path, frag] = href.split('#');
    const targetUrl = path.endsWith('/') || path === '' ? (path || '/') : path;
    const target = pages.get(targetUrl) ||
      (existsSync(join(out, targetUrl.replace(/^\//, ''))) ? { ids: new Set() } : null);
    if (!target) { linkFailures.push(`${url} -> ${href} (no such page)`); continue; }
    if (frag && target.ids && !target.ids.has(decodeURIComponent(frag))) {
      linkFailures.push(`${url} -> ${href} (no such anchor)`);
    }
  }
}
check(`all ${linkChecks} internal links resolve`, linkFailures.length === 0,
  linkFailures.slice(0, 10).join('\n  '));

// --- playground markup matches what playground.js queries ---------------

const ROLES = {
  brainfuck: ['program', 'input', 'output', 'tape', 'code', 'steps', 'pointer',
              'eof', 'example', 'example-note', 'run', 'step', 'reset', 'speed',
              'speed-label', 'status'],
  whitespace: ['program', 'input', 'output', 'glyphs', 'listing', 'stack', 'heap',
               'steps', 'example', 'example-note', 'run', 'step', 'reset', 'speed',
               'speed-label', 'status'],
  deadfish: ['program', 'output', 'acc', 'code', 'steps', 'example', 'run', 'step',
             'reset', 'speed', 'speed-label', 'status']
};

const pgPage = pages.get('/playground/');
check('the playground page exists', !!pgPage);
if (pgPage) {
  for (const kind of Object.keys(ROLES)) {
    const block = pgPage.html.split(`data-kind="${kind}"`)[1];
    check(`the ${kind} playground is on the playground page`, !!block);
    if (!block) continue;
    const section = block.split('</div>\n<div class="pg ')[0];
    for (const r of ROLES[kind]) {
      check(`  ${kind} playground has data-role="${r}"`,
        section.includes(`data-role="${r}"`));
    }
  }
  for (const kind of ['brainfuck', 'whitespace', 'deadfish']) {
    const js = { brainfuck: 'bf.js', whitespace: 'ws.js', deadfish: 'df.js' }[kind];
    check(`the playground page loads ${js}`, pgPage.html.includes(`src="/${js}"`));
  }
  check('the playground page loads playground.js',
    pgPage.html.includes('src="/playground.js"'));
}

check('the home page embeds the brainfuck playground',
  pages.get('/').html.includes('data-kind="brainfuck"'));
check('the brainfuck page embeds the brainfuck playground',
  pages.get('/brainfuck/').html.includes('data-kind="brainfuck"'));
check('the whitespace page embeds the whitespace playground',
  pages.get('/whitespace/').html.includes('data-kind="whitespace"'));
check('the deadfish page embeds the deadfish playground',
  pages.get('/deadfish/').html.includes('data-kind="deadfish"'));

// --- embedded examples are the real files -------------------------------

function embedded(page, id) {
  const m = page.html.match(
    new RegExp('<script type="application/json" id="' + id + '">([\\s\\S]*?)</script>'));
  return m ? JSON.parse(m[1]) : null;
}

const DIRS = { 'bf-examples': 'Brainfuck', 'ws-examples': 'Whitespace', 'df-examples': 'Deadfish' };
for (const [id, dir] of Object.entries(DIRS)) {
  const data = embedded(pgPage, id);
  check(`${id} parses as JSON`, Array.isArray(data) && data.length > 0);
  if (!data) continue;
  let allMatch = true, why = '';
  for (const ex of data) {
    // the label carries the file name before the em dash
    const name = ex.name.split(' ')[0];
    const path = join(repo, 'Langlib', 'Examples', dir, name);
    if (!existsSync(path)) { allMatch = false; why = `${path} missing`; break; }
    const onDisk = readFileSync(path, 'latin1');
    const embeddedSrc = Buffer.from(ex.source, 'utf8').toString('latin1');
    if (onDisk !== embeddedSrc) { allMatch = false; why = `${name} differs from the repository copy`; break; }
  }
  check(`${id} matches Langlib/Examples/${dir}/ byte for byte`, allMatch, why);
}

// --- the embedded programs still do what the pages claim ----------------

const require_ = (await import('node:module')).createRequire(import.meta.url);
const BF = require_(join(site, 'static', 'bf.js'));
const WS = require_(join(site, 'static', 'ws.js'));
const DF = require_(join(site, 'static', 'df.js'));

{
  const data = embedded(pgPage, 'bf-examples');
  const byName = Object.fromEntries(data.map((e) => [e.name.split(' ')[0], e]));
  const run = (n) => BF.run(byName[n].source, byName[n].input, { eof: byName[n].eof, fuel: 5e7 });
  check('the embedded hello.b prints Hello World!', run('hello.b').output === 'Hello World!\n');
  check('the embedded rev.b reverses with its preset input and EOF setting',
    run('rev.b').output === 'desserts');
  check('the embedded add.b adds with its preset input', run('add.b').output === '7');
  check('the embedded quine.b prints itself',
    run('quine.b').output === byName['quine.b'].source);
}
{
  const data = embedded(pgPage, 'ws-examples');
  const byName = Object.fromEntries(data.map((e) => [e.name.split(' ')[0], e]));
  const run = (n) => WS.run(byName[n].source, byName[n].input, { fuel: 1e6 });
  check('the embedded hello.ws prints Hello, World!', run('hello.ws').output === 'Hello, World!\n');
  check('the embedded add.ws adds its preset input', run('add.ws').output === '42\n');
  check('the embedded fact.ws computes 5!', run('fact.ws').output === '120\n');
}
{
  const data = embedded(pgPage, 'df-examples');
  const byName = Object.fromEntries(data.map((e) => [e.name.split(' ')[0], e]));
  check('the embedded xkcd-random.df prints 4',
    DF.run(byName['xkcd-random.df'].source).output === '4\n\n');
}

// --- the sitemap lists the pages ---------------------------------------

{
  const xml = readFileSync(join(out, 'sitemap.xml'), 'utf8');
  const listed = (xml.match(/<loc>/g) || []).length;
  check('the sitemap lists every page but 404', listed === pages.size - 1,
    `sitemap has ${listed}, site has ${pages.size} pages`);
  check('the sitemap uses the custom domain', xml.includes('https://langlib.wtf/'));
}

console.log(`\n${checks - failures}/${checks} checks passed`);
process.exit(failures === 0 ? 0 : 1);
