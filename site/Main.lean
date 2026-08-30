import Site

/-!
# The generator

    cd site && lake exe langlib-site [--root DIR] [--out DIR]

Reads the repository (default `..`), renders every page into the output
directory (default `out`), copies `static/` over it, and writes a sitemap.
Nothing here writes outside the output directory.
-/

open Site
open Site.Markdown

/-! ## Output -/

def writeFileMk (path : System.FilePath) (contents : String) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path contents

def writePage (outDir : System.FilePath) (page : Page) : IO Unit :=
  writeFileMk (outDir / page.file) (shell page)

/-- Copy `static/` verbatim, byte for byte, so `CNAME` and friends survive. -/
partial def copyTree (src dst : System.FilePath) : IO Unit := do
  for entry in (← src.readDir) do
    let target := dst / entry.fileName
    if (← entry.path.isDir) then
      IO.FS.createDirAll target
      copyTree entry.path target
    else
      IO.FS.createDirAll dst
      IO.FS.writeBinFile target (← IO.FS.readBinFile entry.path)

/-! ## Small pieces of page furniture -/

def kicker (text : String) : String :=
  s!"<div class=\"page-kicker\">{escape text}</div>\n"

/--
The line under a language heading: who, when, and how to run it locally. The
directory links are emitted only when the directories are there, so a language
whose Lean side is still landing does not get links into a 404.
-/
def langMeta (l : Lang) (hasExamples hasSource : Bool) : String :=
  let link (there : Bool) (kind label : String) : String :=
    if there then
      s!" · <a href=\"{repoURL}/tree/{repoBranch}/Langlib/{kind}/{escape l.examplesDir}/\">{label}</a>"
    else ""
  s!"<p class=\"muted\">{escape l.author}, {escape l.year} · " ++
  s!"<code>{escape l.runner}</code>" ++
  link hasExamples "Examples" "examples" ++
  link hasSource "Languages" "Lean source" ++
  "</p>\n"

/-- A strip of links to the other languages, so a reader can keep browsing. -/
def langStrip (all : List Lang) (current : String) : String :=
  let links := all.map fun l =>
    if l.slug == current then s!"<strong>{escape l.name}</strong>"
    else s!"<a href=\"/{escape l.slug}/\">{escape l.name}</a>"
  "<p class=\"small muted\">" ++ String.intercalate " · " links ++ "</p>\n"

/-- The note at the foot of every rendered document, saying where it came from. -/
def sourceNote (path : String) : String :=
  s!"<p class=\"source-note\">This page is <code>{escape path}</code> from the " ++
  s!"repository, rendered. Corrections belong " ++
  s!"<a href=\"{repoURL}/blob/{repoBranch}/{escape path}\">in the source file</a>, " ++
  "not here: the site is generated from it.</p>\n"

/-- Colour the status words in the matrix without touching the document. -/
def colourStatus (html : String) : String :=
  html
    |>.replace "<td>yes</td>" "<td><span class=\"s-yes\">yes</span></td>"
    |>.replace "<td>wip</td>" "<td><span class=\"s-wip\">wip</span></td>"
    |>.replace "<td>open</td>" "<td><span class=\"s-no\">open</span></td>"
    |>.replace "<td>-</td>" "<td><span class=\"s-no\">-</span></td>"
    |>.replace "<td>n/a</td>" "<td><span class=\"s-no\">n/a</span></td>"

/-! ## Rendering documents -/

/-- Parse a Markdown document and render its body, minus the level-1 heading. -/
structure Rendered where
  title : String
  summary : String
  html : String
  toc : List (Nat × String × String)

def renderDoc (published : List Published) (path : String) (source : String) : Rendered :=
  let dir := String.intercalate "/" ((path.splitOn "/").dropLast)
  let rw := rewriter published dir
  let blocks := Markdown.parse source
  let rest := Markdown.body blocks
  { title := (Markdown.title? blocks).getD path
    summary := Markdown.summary rest
    html := Markdown.renderBlocks rw rest
    toc := Markdown.toc rest }

/-! ## The pages -/

def homePage (langs : List Lang) (soon : List Lang) (bfData bfPlayground : String)
    (turpExample : String) : Page :=
  let card (l : Lang) : String :=
    s!"<a class=\"card\" href=\"/{escape l.slug}/\">\n" ++
    s!"<span class=\"card-title\">{escape l.name}<span class=\"card-year\">{escape l.year}</span></span>\n" ++
    s!"<p class=\"card-note\">{escape l.blurb}</p>\n</a>\n"
  let soonCard (l : Lang) : String :=
    s!"<div class=\"card soon\">\n" ++
    s!"<span class=\"card-title\">{escape l.name}<span class=\"card-year\">soon</span></span>\n" ++
    s!"<p class=\"card-note\">{escape l.blurb}</p>\n</div>\n"
  let cards := String.join (langs.map card) ++ String.join (soon.map soonCard)
  let body :=
    "<section class=\"hero\">\n" ++
    "<h1>LangLib</h1>\n" ++
    "<p class=\"tagline\">The semantics of esoteric programming languages, written down " ++
    "precisely and made to run. In Lean 4.</p>\n" ++
    "<p class=\"lead\">Esoteric languages are not meant for realistic software. They exist " ++
    "to make a point, to win a bet, to parody a committee, or simply to be difficult. Fifty " ++
    "years of them have accumulated into a real body of design knowledge, scattered across " ++
    "personal pages, wikis and long-dead FTP servers. LangLib collects the designs, pins down " ++
    "what each one actually means, and ships an interpreter you can run.</p>\n" ++
    "<p>Every language here has a specification with sources and credits, a parser, a pure " ++
    "fuel-based reference interpreter, a standalone runner, example programs, and golden " ++
    "tests. The interpreters are ordinary Lean functions, which means they are also " ++
    "mathematical objects you can prove things about. That is the point of the exercise.</p>\n" ++
    "<div class=\"button-row\">\n" ++
    "<a class=\"button\" href=\"#playground\">Run brainfuck in your browser</a>\n" ++
    "<a class=\"button ghost\" href=\"#languages\">Browse the languages</a>\n" ++
    s!"<a class=\"button ghost\" href=\"{repoURL}\">Source on GitHub</a>\n" ++
    "</div>\n</section>\n" ++
    "<div class=\"section-head\" id=\"languages\">\n<h2>The languages</h2>\n" ++
    "<span class=\"more\"><a href=\"/status/\">Full status matrix</a></span>\n</div>\n" ++
    s!"<div class=\"cards\">\n{cards}</div>\n" ++
    "<div class=\"section-head\" id=\"playground\">\n<h2>Brainfuck, here, now</h2>\n" ++
    "<span class=\"more\"><a href=\"/playground/\">Whitespace and Deadfish too</a></span>\n</div>\n" ++
    "<p>The interpreter below is a JavaScript transcription of the semantics on the " ++
    "<a href=\"/brainfuck/\">brainfuck page</a>: 8-bit cells that wrap, a tape unbounded to " ++
    "the right, an error if you walk off the left end, and three selectable conventions for " ++
    "what a read does at end of input. The programs in the menu are the actual files from " ++
    "<code>Langlib/Examples/Brainfuck/</code>, embedded when this page was built. Turn the " ++
    "speed down and watch the tape.</p>\n" ++
    bfData ++ bfPlayground ++
    "<div class=\"section-head\" id=\"turpentine\">\n<h2>Turpentine, the way out</h2>\n" ++
    "<span class=\"more\"><a href=\"/turpentine/\">The language</a></span>\n</div>\n" ++
    "<p>Alan Perlis, 1982: <em>beware of the Turing tar-pit in which everything is possible " ++
    "but nothing of interest is easy</em>. Most of this library is exactly that. Brainfuck can " ++
    "compute anything a computer can compute, and computing 7 + 5 in it takes a paragraph.</p>\n" ++
    "<p>Turpentine is the solvent that dissolves tar. It is a small imperative language with " ++
    "variables, <code>while</code> loops, <code>invariant</code> and <code>decreases</code> " ++
    "annotations, and a type checker: you write the program once, in something legible, and " ++
    "the compilers do the suffering. The file extension is <code>.turp</code>, and yes, the " ++
    "name is the whole joke.</p>\n" ++
    s!"<pre><code>{escape turpExample}</code></pre>\n" ++
    "<p>That program compiles to brainfuck, to whitespace, to subleq, and to the rest of the " ++
    "zoo. Proving that those compilers preserve behaviour is the long game; the " ++
    "<a href=\"/verification/\">verification pipeline</a> says how, and the " ++
    "<a href=\"/status/\">status matrix</a> says how far along it is.</p>\n" ++
    "<div class=\"section-head\">\n<h2>Reading on</h2>\n</div>\n" ++
    "<div class=\"cards\">\n" ++
    "<a class=\"card\" href=\"/status/\"><span class=\"card-title\">Status matrix</span>" ++
    "<p class=\"card-note\">What is specified, parsed, interpreted, tested, compiled and " ++
    "proved, language by language.</p></a>\n" ++
    "<a class=\"card\" href=\"/related/\"><span class=\"card-title\">Related work</span>" ++
    "<p class=\"card-note\">Other people have formalised esolangs too. Here is who, and how " ++
    "LangLib differs.</p></a>\n" ++
    "<a class=\"card\" href=\"/roadmap/\"><span class=\"card-title\">Roadmap</span>" ++
    "<p class=\"card-note\">Languages we want next, and what makes a good candidate.</p></a>\n" ++
    "<a class=\"card\" href=\"/contributing/\"><span class=\"card-title\">Contributing</span>" ++
    "<p class=\"card-note\">What a complete language contribution looks like. Small focused " ++
    "pull requests review faster.</p></a>\n" ++
    "</div>\n" ++
    playgroundScripts ["brainfuck"]
  { url := "/", file := "index.html"
    title := "LangLib — the semantics of esoteric programming languages, in Lean 4"
    description :=
      "A Lean 4 library of esoteric programming language semantics: specifications, " ++
      "reference interpreters and runnable examples for brainfuck, whitespace, malbolge, " ++
      "Befunge-93, subleq, FRACTRAN, Thue, Ook! and Deadfish, plus Turpentine, the " ++
      "human-readable front end that compiles to them."
    body := body, wide := true }

def languagePage (published : List Published) (all : List Lang) (l : Lang)
    (source : String) (playground : String) (scripts : String)
    (hasExamples hasSource : Bool) : Page :=
  let path := s!"docs/{l.slug}/spec.md"
  let doc := renderDoc published path source
  let body :=
    kicker "Language" ++
    s!"<h1>{escape doc.title}</h1>\n" ++
    langMeta l hasExamples hasSource ++
    langStrip all l.slug ++
    doc.html ++
    playground ++
    sourceNote path ++
    scripts
  { url := s!"/{l.slug}/", file := s!"{l.slug}/index.html"
    title := s!"{l.name} — LangLib"
    description := l.blurb
    body := body, toc := doc.toc }

def docPage (published : List Published) (url file path title : String)
    (source : String) (lead : String := "") (kick : String := "")
    (transform : String → String := id) (wide : Bool := false) : Page :=
  let doc := renderDoc published path source
  let body :=
    (if kick.isEmpty then "" else kicker kick) ++
    s!"<h1>{escape doc.title}</h1>\n" ++
    lead ++
    transform doc.html ++
    sourceNote path
  { url := url, file := file, title := title
    description := if doc.summary.isEmpty then title else doc.summary
    body := body, toc := doc.toc, wide := wide }

def playgroundPage (bfData bfPg wsData wsPg dfData dfPg : String) : Page :=
  let body :=
    kicker "Playground" ++
    "<h1>Three machines in your browser</h1>\n" ++
    "<p>These interpreters are written in JavaScript, but they are not improvisations: each " ++
    "one implements the semantic decisions recorded on the language's page, down to the " ++
    "end-of-input conventions and the exact rounding of division, and each is checked " ++
    "against the same example programs the Lean test suite uses. The programs in the menus " ++
    "are those files, embedded when this page was built.</p>\n" ++
    "<p>Nothing is sent anywhere. Everything runs on your machine, in a step-at-a-time " ++
    "interpreter you can slow down, pause, and single-step.</p>\n" ++
    "<h2 id=\"brainfuck\">brainfuck<a class=\"anchor\" href=\"#brainfuck\" aria-hidden=\"true\">#</a></h2>\n" ++
    "<p>Eight commands over a tape of 8-bit cells. The tape grows to the right on demand; " ++
    "moving left of cell 0 is a runtime error rather than undefined behaviour, because a " ++
    "reference semantics that fails loudly is more useful than one that shrugs. The " ++
    "end-of-input selector covers all three conventions found in the wild: leave the cell " ++
    "alone (Müller's interpreter, our default), store 0 (the common modern default), or " ++
    "store 255 (the EOF-is-minus-one convention). Full details on the " ++
    "<a href=\"/brainfuck/\">brainfuck page</a>.</p>\n" ++
    bfData ++ bfPg ++
    "<h2 id=\"whitespace\">whitespace<a class=\"anchor\" href=\"#whitespace\" aria-hidden=\"true\">#</a></h2>\n" ++
    "<p>The left pane holds the program as it really is, which is to say blank. The pane " ++
    "beside it shows the same bytes with the invisible made visible: · for space, → for tab, " ++
    "¶ for linefeed. Underneath sits the stack machine those tokens actually describe, with " ++
    "its arbitrary-precision stack and its heap. Type a few spaces and tabs into the left " ++
    "pane and watch the instruction listing change. See the " ++
    "<a href=\"/whitespace/\">whitespace page</a> for the encoding.</p>\n" ++
    wsData ++ wsPg ++
    "<h2 id=\"deadfish\">Deadfish<a class=\"anchor\" href=\"#deadfish\" aria-hidden=\"true\">#</a></h2>\n" ++
    "<p>One accumulator and four commands: <code>i</code> increment, <code>d</code> " ++
    "decrement, <code>s</code> square, <code>o</code> print. Any other character prints a " ++
    "bare newline, including the newlines in the file itself. The single rule worth knowing " ++
    "is the reset: the accumulator becomes 0 the instant it is exactly -1 or exactly 256, " ++
    "and not one value either side. So <code>iissso</code> prints 0, because 16 squared is " ++
    "256, while <code>iissisdo</code> prints 288, because 17 squared is 289 and sails " ++
    "straight past the check. See the <a href=\"/deadfish/\">Deadfish page</a>.</p>\n" ++
    dfData ++ dfPg ++
    "<p class=\"source-note\">The interpreters are " ++
    s!"<a href=\"{repoURL}/blob/{repoBranch}/site/static/bf.js\">bf.js</a>, " ++
    s!"<a href=\"{repoURL}/blob/{repoBranch}/site/static/ws.js\">ws.js</a> and " ++
    s!"<a href=\"{repoURL}/blob/{repoBranch}/site/static/df.js\">df.js</a>, " ++
    "each about as long as the specification it implements, and each with a test harness " ++
    s!"under <a href=\"{repoURL}/tree/{repoBranch}/site/test\">site/test/</a> that runs the " ++
    "library's own example programs and checks the documented edge cases.</p>\n" ++
    playgroundScripts ["brainfuck", "whitespace", "deadfish"]
  { url := "/playground/", file := "playground/index.html"
    title := "Playground — LangLib"
    description :=
      "Run brainfuck, whitespace and Deadfish in your browser, one step at a time, on the " ++
      "example programs from the LangLib library."
    body := body, wide := true }

def notFoundPage : Page :=
  { url := "/404.html", file := "404.html"
    title := "Not found — LangLib"
    description := "No such page."
    body :=
      "<h1>Nothing here</h1>\n" ++
      "<p>The page you asked for does not exist. This is the only error message on the site " ++
      "that is not a considered semantic decision.</p>\n" ++
      "<p><a href=\"/\">Back to the front page</a>, or the " ++
      "<a href=\"/status/\">status matrix</a>, which lists everything there is.</p>\n" }

/-! ## Assembly -/

structure Options where
  root : String := ".."
  out : String := "out"

partial def parseArgs (args : List String) (o : Options) : IO Options :=
  match args with
  | [] => pure o
  | "--root" :: v :: rest => parseArgs rest { o with root := v }
  | "--out" :: v :: rest => parseArgs rest { o with out := v }
  | a :: _ => throw <| IO.userError s!"unknown argument: {a}"

def loadExamples (root : String) (refs : List ExampleRef) : IO (List (List (String × String))) :=
  refs.filterMapM fun r => do
    match ← readDoc? root s!"Langlib/Examples/{r.file}" with
    | none => pure none
    | some source =>
      pure <| some
        [ ("name", r.label), ("source", source), ("input", r.input)
        , ("eof", r.eof), ("note", r.note) ]

def sitemap (pages : List Page) : String :=
  let entries := String.join <| pages.filterMap fun p =>
    if p.file == "404.html" then none
    else some s!"  <url><loc>{escape (siteURL ++ p.url)}</loc></url>\n"
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  "<urlset xmlns=\"http://www.sitemaps.org/schemas/sitemap/0.9\">\n" ++
  entries ++ "</urlset>\n"

def main (args : List String) : IO UInt32 := do
  let o ← parseArgs args {}
  let root := o.root
  let outDir : System.FilePath := o.out

  -- Which of the in-progress languages have landed their spec since the last build?
  let arrived ← comingSoon.filterM fun l =>
    (System.FilePath.mk root / s!"docs/{l.slug}/spec.md").pathExists
  let stillSoon := comingSoon.filter fun l => !(arrived.any (·.slug == l.slug))
  let allLangs := langs ++ arrived.map ({ · with ready := true })

  -- The publication table drives every relative link in every document.
  let published : List Published :=
    [ { path := "README.md", url := "/" }
    , { path := "docs/README.md", url := "/status/" }
    , { path := "docs", url := "/status/" }
    , { path := "docs/RELATED.md", url := "/related/" }
    , { path := "docs/ROADMAP.md", url := "/roadmap/" }
    , { path := "docs/TESTING.md", url := "/testing/" }
    , { path := "docs/verification.md", url := "/verification/" }
    , { path := "docs/turpentine/spec.md", url := "/turpentine/" }
      -- docs/README.md still points the front end at its pre-rename path
    , { path := "docs/wtf/spec.md", url := "/turpentine/" }
    , { path := "CONTRIBUTING.md", url := "/contributing/" }
    ] ++ allLangs.map fun l => { path := s!"docs/{l.slug}/spec.md", url := s!"/{l.slug}/" }

  -- Example programs, read from the library itself.
  let bfExamples ← loadExamples root brainfuckExamples
  let wsExamples ← loadExamples root whitespaceExamples
  let dfExamples ← loadExamples root deadfishExamples
  let bfData := exampleData "bf-examples" bfExamples
  let wsData := exampleData "ws-examples" wsExamples
  let dfData := exampleData "df-examples" dfExamples
  let bfPg := brainfuckPlayground "bf-examples"
  let wsPg := whitespacePlayground "ws-examples"
  let dfPg := deadfishPlayground "df-examples"

  let turpExample := (← readDoc? root "Langlib/Examples/Turpentine/isqrt.turp").getD
    "// Langlib/Examples/Turpentine/isqrt.turp was not found in this checkout.\n"

  -- Language pages, each with its playground where we have one.
  let languagePages ← allLangs.mapM fun l => do
    let source ← readDoc root s!"docs/{l.slug}/spec.md"
    let (pg, scripts) :=
      if l.slug == "brainfuck" then
        (playgroundHeading "Run it here" ++
          "<p>The same eight commands, in your browser. The programs are the files in " ++
          "<code>Langlib/Examples/Brainfuck/</code>; the interpreter implements the " ++
          "decisions listed above, end-of-input selector included.</p>\n" ++ bfData ++ bfPg,
         playgroundScripts ["brainfuck"])
      else if l.slug == "whitespace" then
        (playgroundHeading "Run it here" ++
          "<p>The left pane is the program as it really is. The pane beside it shows the " ++
          "same bytes as · space, → tab and ¶ linefeed, and the listing underneath is what " ++
          "the tokeniser made of them.</p>\n" ++ wsData ++ wsPg,
         playgroundScripts ["whitespace"])
      else if l.slug == "deadfish" then
        (playgroundHeading "Run it here" ++
          "<p>Four commands, one accumulator, and the reset that catches everybody.</p>\n" ++
          dfData ++ dfPg,
         playgroundScripts ["deadfish"])
      else ("", "")
    let hasExamples ← (System.FilePath.mk root / s!"Langlib/Examples/{l.examplesDir}").pathExists
    let hasSource ← (System.FilePath.mk root / s!"Langlib/Languages/{l.examplesDir}").pathExists
    pure <| languagePage published allLangs l source pg scripts hasExamples hasSource

  let statusSource ← readDoc root "docs/README.md"
  let relatedSource ← readDoc root "docs/RELATED.md"
  let roadmapSource ← readDoc root "docs/ROADMAP.md"
  let testingSource ← readDoc root "docs/TESTING.md"
  let verifySource ← readDoc root "docs/verification.md"
  let turpSource ← readDoc root "docs/turpentine/spec.md"
  let contribSource ← readDoc root "CONTRIBUTING.md"

  let pages : List Page :=
    [ homePage allLangs stillSoon bfData bfPg turpExample ] ++
    languagePages ++
    [ docPage published "/turpentine/" "turpentine/index.html" "docs/turpentine/spec.md"
        "Turpentine — LangLib" turpSource
        (lead :=
          "<p class=\"muted\"><code>lake exe turpentine</code> · " ++
          s!"<a href=\"{repoURL}/tree/{repoBranch}/Langlib/Examples/Turpentine/\">examples</a> · " ++
          s!"<a href=\"{repoURL}/tree/{repoBranch}/Langlib/Languages/Turpentine/\">Lean source</a></p>\n")
        (kick := "Front end")
    , docPage published "/status/" "status/index.html" "docs/README.md"
        "Status matrix — LangLib" statusSource
        (lead := "<p>What exists, per language: the specification, the parser, the " ++
          "interpreter, the examples and tests, the runner, the compiler from Turpentine, " ++
          "and the proof that the compiler is correct. The last column is the long game.</p>\n")
        (kick := "Where things stand")
        (transform := colourStatus) (wide := true)
    , docPage published "/related/" "related/index.html" "docs/RELATED.md"
        "Related work — LangLib" relatedSource (kick := "Elsewhere")
    , docPage published "/roadmap/" "roadmap/index.html" "docs/ROADMAP.md"
        "Roadmap — LangLib" roadmapSource (kick := "What is next")
    , docPage published "/testing/" "testing/index.html" "docs/TESTING.md"
        "Testing — LangLib" testingSource (kick := "How we know")
    , docPage published "/verification/" "verification/index.html" "docs/verification.md"
        "Verification pipeline — LangLib" verifySource (kick := "The long game")
    , docPage published "/contributing/" "contributing/index.html" "CONTRIBUTING.md"
        "Contributing — LangLib" contribSource (kick := "Join in")
    , playgroundPage bfData bfPg wsData wsPg dfData dfPg
    , notFoundPage
    ]

  IO.FS.createDirAll outDir
  for page in pages do
    writePage outDir page
  writeFileMk (outDir / "sitemap.xml") (sitemap pages)
  writeFileMk (outDir / "robots.txt")
    s!"User-agent: *\nAllow: /\nSitemap: {siteURL}/sitemap.xml\n"

  let staticDir := System.FilePath.mk "static"
  if (← staticDir.pathExists) then
    copyTree staticDir outDir
  else
    IO.eprintln "site generator: static/ is missing; the pages will have no stylesheet"

  -- Documents may carry their own images (the Piet spec shows its example
  -- programs). Each `docs/<lang>/img/` lands next to that language's page,
  -- so the relative `img/...` in the Markdown resolves on the site exactly
  -- as it does on the repository page.
  for lang in allLangs do
    let imgDir := System.FilePath.mk root / "docs" / lang.slug / "img"
    if (← imgDir.pathExists) then
      copyTree imgDir (outDir / lang.slug / "img")

  IO.println s!"wrote {pages.length} pages to {outDir}"
  pure 0
where
  playgroundHeading (title : String) : String :=
    s!"<h2 id=\"{escape (slug title)}\">{escape title}" ++
    s!"<a class=\"anchor\" href=\"#{escape (slug title)}\" aria-hidden=\"true\">#</a></h2>\n"
