import Site.Docs

/-!
# The page shell

One template, one stylesheet, one script. Everything a page needs is passed in
as already-rendered HTML, so the generator stays a pipeline: read Markdown,
render blocks, drop the result into `shell`.
-/

namespace Site

open Site.Markdown

/-- A navigation entry in the masthead. -/
structure NavItem where
  label : String
  url : String
  deriving Inhabited

def navItems : List NavItem :=
  [ ⟨"Languages", "/#languages"⟩
  , ⟨"Playground", "/playground/"⟩
  , ⟨"Turpentine", "/turpentine/"⟩
  , ⟨"Status", "/status/"⟩
  , ⟨"Related work", "/related/"⟩
  , ⟨"Contributing", "/contributing/"⟩
  ]

/-- A page to be written out. -/
structure Page where
  /-- The URL path, e.g. `/brainfuck/`. -/
  url : String
  /-- The output file relative to the output directory. -/
  file : String
  /-- The `<title>`. -/
  title : String
  /-- The `<meta name="description">`. -/
  description : String
  /-- The page body, already HTML. -/
  body : String
  /-- Headings for the sidebar table of contents. -/
  toc : List (Nat × String × String) := []
  /-- Drop the reading-width limit (used by the status matrix and playground). -/
  wide : Bool := false
  deriving Inhabited

/-- Escape a string for a JSON string literal, `<` included so it is safe in `<script>`. -/
def jsonString (s : String) : String :=
  let body := s.foldl (init := "") fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | '<'  => acc ++ "\\u003c"
    | '>'  => acc ++ "\\u003e"
    | '&'  => acc ++ "\\u0026"
    | c =>
      if c.toNat < 0x20 then
        let hex := Nat.toDigits 16 c.toNat
        acc ++ "\\u" ++ "".pushn '0' (4 - hex.length) ++ String.ofList hex
      else acc.push c
  "\"" ++ body ++ "\""

/-- A JSON object from already-encoded fields. -/
def jsonObject (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (k, v) => jsonString k ++ ":" ++ v) ++ "}"

def jsonArray (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

private def tocHtml (entries : List (Nat × String × String)) : String :=
  if entries.isEmpty then "" else
  let items := String.join <| entries.map fun (n, text, id) =>
    let cls := if n ≥ 3 then " class=\"sub\"" else ""
    s!"<li{cls}><a href=\"#{escape id}\">{escape (Markdown.plain text)}</a></li>\n"
  s!"<nav class=\"toc\" aria-label=\"On this page\">\n<div class=\"toc-title\">On this page</div>\n<ul>\n{items}</ul>\n</nav>\n"

/-- Render a complete HTML document. -/
def shell (page : Page) : String :=
  let nav := String.join <| navItems.map fun item =>
    let current := if page.url == item.url then " aria-current=\"page\"" else ""
    s!"<a href=\"{escape item.url}\"{current}>{escape item.label}</a>"
  let content :=
    if page.toc.isEmpty then
      s!"<div class=\"prose{if page.wide then " wide" else ""}\">\n{page.body}</div>\n"
    else
      s!"<div class=\"doc-layout\">\n<div class=\"prose{if page.wide then " wide" else ""}\">\n{page.body}</div>\n{tocHtml page.toc}</div>\n"
  let canonical := siteURL ++ page.url
  "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n" ++
  "<meta charset=\"utf-8\">\n" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" ++
  s!"<title>{escape page.title}</title>\n" ++
  s!"<meta name=\"description\" content=\"{escape page.description}\">\n" ++
  s!"<link rel=\"canonical\" href=\"{escape canonical}\">\n" ++
  s!"<meta property=\"og:title\" content=\"{escape page.title}\">\n" ++
  s!"<meta property=\"og:description\" content=\"{escape page.description}\">\n" ++
  s!"<meta property=\"og:url\" content=\"{escape canonical}\">\n" ++
  "<meta property=\"og:type\" content=\"website\">\n" ++
  "<meta property=\"og:site_name\" content=\"langlib\">\n" ++
  "<link rel=\"icon\" href=\"/favicon.svg\" type=\"image/svg+xml\">\n" ++
  "<link rel=\"stylesheet\" href=\"/style.css\">\n" ++
  -- applied before first paint so a chosen theme does not flash
  "<script>try{var t=localStorage.getItem('langlib-theme');" ++
  "if(t)document.documentElement.setAttribute('data-theme',t)}catch(e){}</script>\n" ++
  "<script src=\"/site.js\" defer></script>\n" ++
  "</head>\n<body>\n" ++
  "<a class=\"skip-link\" href=\"#main\">Skip to content</a>\n" ++
  "<header class=\"masthead\">\n<div class=\"masthead-inner\">\n" ++
  "<a class=\"brand\" href=\"/\">langlib<span class=\"dot\">.wtf</span></a>\n" ++
  s!"<nav aria-label=\"Site\">{nav}" ++
  "<button class=\"theme-toggle\" type=\"button\" hidden>dark</button>" ++
  "</nav>\n</div>\n</header>\n" ++
  s!"<main class=\"page\" id=\"main\">\n{content}</main>\n" ++
  "<footer class=\"footer\">\n<div class=\"footer-inner\">\n" ++
  "<div>LangLib is Apache 2.0. The languages belong to the people who " ++
  "thought of them, and are credited on their pages.</div>\n" ++
  s!"<div><a href=\"{repoURL}\">Source on GitHub</a></div>\n" ++
  "</div>\n</footer>\n</body>\n</html>\n"

/-! ## Playground markup

The generator emits the markup and the example data; `playground.js` attaches
behaviour. With scripting off, the reader still sees the programs.
-/

private def loadScripts (files : List String) : String :=
  String.join <| files.map fun f => s!"<script src=\"/{f}\"></script>\n"

/-- The three interpreters plus the wiring, loaded once per page that needs them. -/
def playgroundScripts (kinds : List String) : String :=
  let files := (kinds.map fun k =>
    match k with
    | "brainfuck" => "bf.js"
    | "whitespace" => "ws.js"
    | "deadfish" => "df.js"
    | _ => "") |>.filter (· != "")
  loadScripts (files ++ ["playground.js"])

private def controls (extra : String) : String :=
  extra ++
  "<span class=\"spacer\"></span>\n" ++
  "<label>Speed <input type=\"range\" data-role=\"speed\" min=\"0\" max=\"6\" value=\"3\" " ++
  "aria-label=\"Steps per frame\"><span data-role=\"speed-label\" class=\"muted\"></span></label>\n" ++
  "<button class=\"pg-btn\" type=\"button\" data-role=\"step\">Step</button>\n" ++
  "<button class=\"pg-btn\" type=\"button\" data-role=\"reset\">Reset</button>\n" ++
  "<button class=\"pg-btn primary\" type=\"button\" data-role=\"run\">Run</button>\n"

/-- Without scripting the panes stay empty, so say what to run instead. -/
private def noScriptNote (runner program : String) : String :=
  "<noscript><div class=\"pg-cell span2\"><p class=\"pg-note\">This playground needs " ++
  "JavaScript, and yours is switched off, which is a defensible position. The same " ++
  "programs run locally: <code>" ++ escape runner ++ " " ++ escape program ++
  "</code>.</p></div></noscript>\n"

private def exampleSelect : String :=
  "<label>Example <select data-role=\"example\"></select></label>\n"

private def statusBar (extra : String := "") : String :=
  "<div class=\"pg-status\">" ++
  "<span data-role=\"status\">not started</span>" ++
  "<span data-role=\"steps\"></span>" ++
  extra ++
  "</div>\n"

/-- The brainfuck playground. `dataId` names the embedded example JSON. -/
def brainfuckPlayground (dataId : String) : String :=
  let eof :=
    "<label>At end of input <select data-role=\"eof\">" ++
    "<option value=\"unchanged\">leave the cell</option>" ++
    "<option value=\"zero\">store 0</option>" ++
    "<option value=\"minus1\">store 255</option>" ++
    "</select></label>\n"
  s!"<div class=\"pg\" data-kind=\"brainfuck\" data-examples=\"{escape dataId}\">\n" ++
  "<div class=\"pg-bar\">\n" ++ exampleSelect ++ eof ++ controls "" ++ "</div>\n" ++
  "<div class=\"pg-grid\">\n" ++
  noScriptNote "lake exe brainfuck" "Langlib/Examples/Brainfuck/hello.b" ++
  "<div class=\"pg-cell\">\n<div class=\"pg-label\">Program</div>\n" ++
  "<textarea class=\"program\" data-role=\"program\" spellcheck=\"false\" " ++
  "aria-label=\"Brainfuck program\"></textarea>\n" ++
  "<p class=\"pg-note small muted\" data-role=\"example-note\"></p>\n</div>\n" ++
  "<div class=\"pg-cell\">\n<div class=\"pg-label\">Input <span class=\"hint\">what the program reads</span></div>\n" ++
  "<textarea class=\"small\" data-role=\"input\" spellcheck=\"false\" aria-label=\"Program input\"></textarea>\n" ++
  "<div class=\"pg-label\" style=\"margin-top:0.7rem\">Output</div>\n" ++
  "<pre class=\"pg-out\" data-role=\"output\" aria-live=\"polite\"></pre>\n</div>\n" ++
  "<div class=\"pg-cell span2\">\n<div class=\"pg-label\">Tape " ++
  "<span class=\"hint\">8-bit cells, unbounded to the right</span></div>\n" ++
  "<div class=\"tape-wrap\"><div class=\"tape\" data-role=\"tape\"></div></div>\n</div>\n" ++
  "<div class=\"pg-cell span2\">\n<div class=\"pg-label\">Instruction pointer</div>\n" ++
  "<pre class=\"pg-code\" data-role=\"code\"></pre>\n</div>\n" ++
  "</div>\n" ++ statusBar "<span data-role=\"pointer\"></span>" ++
  "</div>\n"

/-- The Whitespace playground, which spends most of its effort making the program visible. -/
def whitespacePlayground (dataId : String) : String :=
  s!"<div class=\"pg\" data-kind=\"whitespace\" data-examples=\"{escape dataId}\">\n" ++
  "<div class=\"pg-bar\">\n" ++ exampleSelect ++ controls "" ++ "</div>\n" ++
  "<div class=\"pg-grid\">\n" ++
  noScriptNote "lake exe whitespace" "Langlib/Examples/Whitespace/hello.ws" ++
  "<div class=\"pg-cell\">\n<div class=\"pg-label\">Program <span class=\"hint\">as written: blank</span></div>\n" ++
  "<textarea class=\"program\" data-role=\"program\" spellcheck=\"false\" " ++
  "aria-label=\"Whitespace program\"></textarea>\n" ++
  "<p class=\"pg-note small muted\" data-role=\"example-note\"></p>\n</div>\n" ++
  "<div class=\"pg-cell\">\n<div class=\"pg-label\">Program <span class=\"hint\">" ++
  "with the invisible made visible: · space, → tab, ¶ linefeed</span></div>\n" ++
  "<pre class=\"pg-code ws-glyphs\" data-role=\"glyphs\"></pre>\n</div>\n" ++
  "<div class=\"pg-cell\">\n<div class=\"pg-label\">Input</div>\n" ++
  "<textarea class=\"small\" data-role=\"input\" spellcheck=\"false\" aria-label=\"Program input\"></textarea>\n" ++
  "<div class=\"pg-label\" style=\"margin-top:0.7rem\">Output</div>\n" ++
  "<pre class=\"pg-out\" data-role=\"output\" aria-live=\"polite\"></pre>\n</div>\n" ++
  "<div class=\"pg-cell\">\n<div class=\"pg-label\">Instructions <span class=\"hint\">what those tokens mean</span></div>\n" ++
  "<pre class=\"pg-code\" data-role=\"listing\"></pre>\n</div>\n" ++
  "<div class=\"pg-cell\">\n<div class=\"pg-label\">Stack</div>\n" ++
  "<pre class=\"stack-view\" data-role=\"stack\"></pre>\n</div>\n" ++
  "<div class=\"pg-cell\">\n<div class=\"pg-label\">Heap</div>\n" ++
  "<pre class=\"heap-view\" data-role=\"heap\"></pre>\n</div>\n" ++
  "</div>\n" ++ statusBar ++ "</div>\n"

/-- The Deadfish playground, which needs almost nothing, being Deadfish. -/
def deadfishPlayground (dataId : String) : String :=
  s!"<div class=\"pg\" data-kind=\"deadfish\" data-examples=\"{escape dataId}\">\n" ++
  "<div class=\"pg-bar\">\n" ++ exampleSelect ++ controls "" ++ "</div>\n" ++
  "<div class=\"pg-grid\">\n" ++
  noScriptNote "lake exe deadfish" "Langlib/Examples/Deadfish/hello.df" ++
  "<div class=\"pg-cell\">\n<div class=\"pg-label\">Program <span class=\"hint\">i d s o</span></div>\n" ++
  "<textarea class=\"program small\" data-role=\"program\" spellcheck=\"false\" " ++
  "aria-label=\"Deadfish program\"></textarea>\n" ++
  "<div class=\"pg-label\" style=\"margin-top:0.7rem\">Accumulator</div>\n" ++
  "<pre class=\"pg-out\" data-role=\"acc\">0</pre>\n</div>\n" ++
  "<div class=\"pg-cell\">\n<div class=\"pg-label\">Output</div>\n" ++
  "<pre class=\"pg-out\" data-role=\"output\" aria-live=\"polite\"></pre>\n</div>\n" ++
  "<div class=\"pg-cell span2\">\n<div class=\"pg-label\">Instruction pointer</div>\n" ++
  "<pre class=\"pg-code\" data-role=\"code\"></pre>\n</div>\n" ++
  "</div>\n" ++ statusBar ++ "</div>\n"

/-- Embed example programs for a playground as JSON. -/
def exampleData (id : String) (examples : List (List (String × String))) : String :=
  let items := examples.map fun fields =>
    jsonObject (fields.map fun (k, v) => (k, jsonString v))
  s!"<script type=\"application/json\" id=\"{escape id}\">{jsonArray items}</script>\n"

end Site
