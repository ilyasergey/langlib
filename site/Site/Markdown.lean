import Site.Html

/-!
# A small Markdown renderer

Enough CommonMark plus GitHub tables to render the langlib documentation
faithfully: ATX headings, paragraphs, fenced code, bullet and numbered lists
with nesting, pipe tables, block quotes, thematic breaks, and the inline set
we actually use (code spans, links, bare URLs, `**strong**`, `*emphasis*`,
backslash escapes).

The point of rendering `docs/*.md` rather than copying it is that the site
cannot drift from the documentation. That makes this file the contract: if a
document starts using a construct that is not here, the construct shows up
verbatim on the page, which is ugly enough to notice.

Link destinations go through a rewriting function so that a relative link
between two documents becomes a link between two site pages (see
`Site/Docs.lean`).
-/

namespace Site.Markdown

open Site

inductive Align where
  | left | center | right
  deriving Inhabited, BEq

inductive Block where
  | heading (level : Nat) (text : String)
  | para (text : String)
  | code (lang : String) (body : String)
  | bullets (items : List (List Block))
  | numbers (items : List (List Block))
  | table (header : List String) (align : List Align) (rows : List (List String))
  | quote (body : List Block)
  | rule
  deriving Inhabited

/-- The link rewriter: takes a destination as written, returns one for the site. -/
abbrev Rewrite := String → String

/-! ## Inline parsing -/

private partial def findSub (needle : List Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if needle.isPrefixOf (c :: rest) then
      some ([], (c :: rest).drop needle.length)
    else
      (findSub needle rest).map fun (b, a) => (c :: b, a)

private def isSpaceChar (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t'

/-- Find the closing `*` of an emphasis run: a `*` not preceded by whitespace. -/
private partial def findEm (seen : List Char) : List Char → Option (List Char × List Char)
  | [] => none
  | '*' :: rest =>
    match seen with
    | prev :: _ => if isSpaceChar prev then findEm ('*' :: seen) rest
                   else some (seen.reverse, rest)
    | [] => findEm ('*' :: seen) rest
  | c :: rest => findEm (c :: seen) rest

private def urlStop (c : Char) : Bool :=
  isSpaceChar c || c == '<' || c == '>' || c == '"' || c == '`' || c == ')' || c == ']'

/-- Trim the punctuation a sentence leaves clinging to the end of a bare URL. -/
private def trimUrlTail (cs : List Char) : List Char × List Char :=
  let clingy (c : Char) :=
    c == '.' || c == ',' || c == ';' || c == ':' || c == '!' || c == '?'
  let back := cs.reverse.takeWhile clingy
  (cs.take (cs.length - back.length), back.reverse)

mutual

/-- Render inline markdown to HTML. -/
partial def inline (rw : Rewrite) (s : String) : String :=
  inlineGo rw "" s.toList

partial def inlineGo (rw : Rewrite) (acc : String) : List Char → String
  | [] => acc
  | '\\' :: c :: rest =>
    if c.isAlphanum then inlineGo rw (acc ++ "\\" ++ escape (String.singleton c)) rest
    else inlineGo rw (acc ++ escape (String.singleton c)) rest
  | '`' :: rest =>
    -- a code span delimited by a run of n backticks
    let ticks := 1 + (rest.takeWhile (· == '`')).length
    let fence := List.replicate ticks '`'
    let body := rest.drop (ticks - 1)
    match findSub fence body with
    | some (content, after) =>
      let text := String.ofList content
      let text := if text.startsWith " " && text.endsWith " " && trim text != ""
                  then dropChars 1 text |> fun t => takeChars (t.toList.length - 1) t
                  else text
      inlineGo rw (acc ++ "<code>" ++ escape text ++ "</code>") after
    | none => inlineGo rw (acc ++ String.ofList fence) body
  | '*' :: '*' :: rest =>
    match findSub ['*', '*'] rest with
    | some (content, after) =>
      inlineGo rw (acc ++ "<strong>" ++ inlineGo rw "" content ++ "</strong>") after
    | none => inlineGo rw (acc ++ "**") rest
  | '*' :: rest =>
    match rest with
    | c :: _ =>
      if isSpaceChar c then inlineGo rw (acc ++ "*") rest
      else match findEm [] rest with
        | some (content, after) =>
          inlineGo rw (acc ++ "<em>" ++ inlineGo rw "" content ++ "</em>") after
        | none => inlineGo rw (acc ++ "*") rest
    | [] => acc ++ "*"
  | '[' :: rest =>
    match findSub [']'] rest with
    | some (text, after) =>
      match after with
      | '(' :: dest =>
        match findSub [')'] dest with
        | some (url, tail) =>
          let href := rw (trim (String.ofList url))
          inlineGo rw
            (acc ++ "<a href=\"" ++ escape href ++ "\">" ++ inlineGo rw "" text ++ "</a>")
            tail
        | none => inlineGo rw (acc ++ "[") rest
      | _ => inlineGo rw (acc ++ "[") rest
    | none => inlineGo rw (acc ++ "[") rest
  | cs@(c :: rest) =>
    if c == 'h' && (List.isPrefixOf "http://".toList cs || List.isPrefixOf "https://".toList cs) then
      let (url, tail) := cs.span (fun ch => !urlStop ch)
      let (url, back) := trimUrlTail url
      let text := String.ofList url
      inlineGo rw (acc ++ "<a href=\"" ++ escape text ++ "\">" ++ escape text ++ "</a>")
        (back ++ tail)
    else if c == '\n' then
      inlineGo rw (acc.push ' ') rest
    else
      inlineGo rw (acc ++ escape (String.singleton c)) rest

end

/-! ## Plain text

Headings reach the table of contents and the description meta tag as source
Markdown. Both want text, so this strips the markup rather than rendering it.
-/

mutual

partial def plain (s : String) : String := plainGo "" s.toList

partial def plainGo (acc : String) : List Char → String
  | [] => acc
  | '\\' :: c :: rest => plainGo (acc.push c) rest
  | '`' :: rest => plainGo acc rest
  | '*' :: rest => plainGo acc rest
  | '[' :: rest =>
    match findSub [']'] rest with
    | some (text, after) =>
      match after with
      | '(' :: dest =>
        match findSub [')'] dest with
        | some (_, tail) => plainGo (acc ++ plainGo "" text) tail
        | none => plainGo (acc.push '[') rest
      | _ => plainGo (acc.push '[') rest
    | none => plainGo (acc.push '[') rest
  | '\n' :: rest => plainGo (acc.push ' ') rest
  | c :: rest => plainGo (acc.push c) rest

end

/-! ## Block parsing -/

private def headingLevel (l : String) : Option Nat :=
  let hs := (l.toList.takeWhile (· == '#')).length
  if hs ≥ 1 && hs ≤ 6 && (l.toList[hs]? == some ' ') then some hs else none

private def isFence (l : String) : Bool := (trim l).startsWith "```"

private def isRule (l : String) : Bool :=
  let t := trim l
  t == "---" || t == "***" || t == "___" || t == "____"

private def bulletWidth (l : String) : Option Nat :=
  let i := indentOf l
  match l.toList.drop i with
  | c :: ' ' :: _ => if c == '*' || c == '-' || c == '+' then some (i + 2) else none
  | _ => none

private def numberWidth (l : String) : Option Nat :=
  let i := indentOf l
  let after := l.toList.drop i
  let digits := after.takeWhile Char.isDigit
  if digits.isEmpty || digits.length > 9 then none
  else match after.drop digits.length with
    | '.' :: ' ' :: _ => some (i + digits.length + 2)
    | ')' :: ' ' :: _ => some (i + digits.length + 2)
    | _ => none

private def isDelimRow (l : String) : Bool :=
  let t := trim l
  !t.isEmpty
  && t.toList.all (fun c => c == '|' || c == '-' || c == ':' || c == ' ')
  && t.toList.any (· == '-')

/--
Split a table row on its unescaped pipes. GitHub's rule is that `\|` inside a
cell is a literal pipe, which Befunge-93's command table depends on, so the
escape is resolved here rather than left to the inline pass.
-/
private def splitCells : List Char → List String
  | [] => [""]
  | '\\' :: '|' :: rest =>
    match splitCells rest with
    | c :: cs => (("|" ++ c)) :: cs
    | [] => ["|"]
  | '|' :: rest => "" :: splitCells rest
  | c :: rest =>
    match splitCells rest with
    | s :: cs => (String.singleton c ++ s) :: cs
    | [] => [String.singleton c]

private def splitRow (l : String) : List String :=
  let t := trim l
  let t := if t.startsWith "|" then dropChars 1 t else t
  let t := if t.endsWith "|" && !t.endsWith "\\|" then takeChars (t.toList.length - 1) t else t
  (splitCells t.toList).map trim

private def alignOf (s : String) : Align :=
  let t := trim s
  match t.startsWith ":", t.endsWith ":" with
  | true, true => .center
  | false, true => .right
  | _, _ => .left

/-- Does this line begin a block that would interrupt a paragraph? -/
private def interrupts (l : String) : Bool :=
  isBlank l || isFence l || isRule l || (headingLevel l).isSome
  || (bulletWidth l).isSome || (numberWidth l).isSome || l.startsWith ">"

mutual

partial def parseBlocks : List String → List Block
  | [] => []
  | l :: rest =>
    if isBlank l then parseBlocks rest
    else if isFence l then
      let lang := trim (dropChars 3 (trim l))
      let body := rest.takeWhile (fun x => !isFence x)
      let after := (rest.drop body.length).drop 1
      .code lang (String.intercalate "\n" body) :: parseBlocks after
    else if isRule l then
      .rule :: parseBlocks rest
    else match headingLevel l with
    | some n => .heading n (trim (dropChars (n + 1) l)) :: parseBlocks rest
    | none =>
      if l.startsWith ">" then
        let body := (l :: rest).takeWhile (fun x => x.startsWith ">")
        let after := (l :: rest).drop body.length
        let inner := body.map fun x =>
          let x := dropChars 1 x
          if x.startsWith " " then dropChars 1 x else x
        .quote (parseBlocks inner) :: parseBlocks after
      else match bulletWidth l, numberWidth l with
      | some w, _ => parseList false (indentOf l) w (l :: rest)
      | none, some w => parseList true (indentOf l) w (l :: rest)
      | none, none =>
        -- a pipe table needs a delimiter row directly under its header
        let isTable := hasSubstr l "|" && (match rest with
          | d :: _ => isDelimRow d && hasSubstr d "|"
          | [] => false)
        if isTable then
          match rest with
          | d :: more =>
            let body := more.takeWhile (fun x => hasSubstr x "|" && !isBlank x)
            let after := more.drop body.length
            .table (splitRow l) ((splitRow d).map alignOf) (body.map splitRow)
              :: parseBlocks after
          | [] => parseBlocks rest
        else
          let body := l :: rest.takeWhile (fun x => !interrupts x)
          let after := rest.drop (body.length - 1)
          .para (String.intercalate "\n" body) :: parseBlocks after

/-- Collect one list (`ordered` says which kind) whose markers sit at `i0`. -/
partial def parseList (ordered : Bool) (i0 w : Nat) : List String → List Block
  | [] => []
  | l :: rest =>
    let (items, after) := gatherItems ordered i0 w (l :: rest) []
    let blocks := items.map parseBlocks
    (if ordered then Block.numbers blocks else Block.bullets blocks) :: parseBlocks after

/-- Split the source into item bodies until the list ends. -/
partial def gatherItems (ordered : Bool) (i0 w : Nat) (ls : List String)
    (acc : List (List String)) : List (List String) × List String :=
  match ls with
  | [] => (acc.reverse, [])
  | l :: rest =>
    let marker := if ordered then numberWidth l else bulletWidth l
    match marker with
    | none => (acc.reverse, ls)
    | some mw =>
      if indentOf l != i0 then (acc.reverse, ls)
      else
        let first := dropChars mw l
        let (body, after) := gatherBody ordered i0 w rest [first]
        gatherItems ordered i0 w after (body :: acc)

/-- Everything belonging to the item already started, dedented by `w`. -/
partial def gatherBody (ordered : Bool) (i0 w : Nat) (ls : List String)
    (acc : List String) : List String × List String :=
  match ls with
  | [] => (acc.reverse, [])
  | l :: rest =>
    if isBlank l then
      -- a blank line continues the item only if more indented content follows
      match rest.dropWhile isBlank with
      | next :: _ =>
        if indentOf next > i0 && !isBlank next then
          gatherBody ordered i0 w rest ("" :: acc)
        else (acc.reverse, ls)
      | [] => (acc.reverse, ls)
    else if indentOf l > i0 then
      gatherBody ordered i0 w rest (dedent w l :: acc)
    else if ((if ordered then numberWidth l else bulletWidth l)).isSome then
      (acc.reverse, ls)
    else if interrupts l then
      (acc.reverse, ls)
    else
      -- lazy continuation of the item's paragraph
      gatherBody ordered i0 w rest (trim l :: acc)

end

/-! ## Rendering -/

private def alignAttr : Align → String
  | .left => ""
  | .center => " style=\"text-align:center\""
  | .right => " style=\"text-align:right\""

mutual

partial def renderBlock (rw : Rewrite) : Block → String
  | .heading n text =>
    let id := slug text
    let body := inline rw text
    if n ≤ 1 then s!"<h1>{body}</h1>\n"
    else
      let anchor := s!"<a class=\"anchor\" href=\"#{escape id}\" aria-hidden=\"true\">#</a>"
      s!"<h{n} id=\"{escape id}\">{body}{anchor}</h{n}>\n"
  | .para text => s!"<p>{inline rw text}</p>\n"
  | .code lang body =>
    let cls := if lang.isEmpty then "" else attr "class" s!"language-{lang}"
    s!"<pre><code{cls}>{escape body}</code></pre>\n"
  | .bullets items => s!"<ul>\n{renderItems rw items}</ul>\n"
  | .numbers items => s!"<ol>\n{renderItems rw items}</ol>\n"
  | .quote body => s!"<blockquote>\n{renderBlocks rw body}</blockquote>\n"
  | .rule => "<hr>\n"
  | .table header align rows =>
    let cell (tag : String) (i : Nat) (c : String) :=
      let a := alignAttr (align[i]?.getD .left)
      s!"<{tag}{a}>{inline rw c}</{tag}>"
    let head :=
      String.join (header.zipIdx.map fun (c, i) => cell "th" i c)
    let body := String.join (rows.map fun r =>
      "<tr>" ++ String.join (r.zipIdx.map fun (c, i) => cell "td" i c) ++ "</tr>\n")
    s!"<div class=\"table-wrap\">\n<table>\n<thead><tr>{head}</tr></thead>\n<tbody>\n{body}</tbody>\n</table>\n</div>\n"

partial def renderItems (rw : Rewrite) (items : List (List Block)) : String :=
  String.join <| items.map fun bs =>
    match bs with
    | [.para text] => s!"<li>{inline rw text}</li>\n"
    | _ => s!"<li>\n{renderBlocks rw bs}</li>\n"

partial def renderBlocks (rw : Rewrite) (bs : List Block) : String :=
  String.join (bs.map (renderBlock rw))

end

/-- Parse and render a whole document. -/
def render (rw : Rewrite) (source : String) : String :=
  renderBlocks rw (parseBlocks (lines source))

/-- Parse only, for callers that want the structure (title, table of contents). -/
def parse (source : String) : List Block := parseBlocks (lines source)

/-- The document's first level-1 heading, if it has one. -/
def title? (bs : List Block) : Option String :=
  bs.findSome? fun
    | .heading 1 t => some t
    | _ => none

/-- Everything after the first level-1 heading. -/
def body (bs : List Block) : List Block :=
  match bs with
  | .heading 1 _ :: rest => rest
  | _ => bs

/-- Level-2 and level-3 headings, for a table of contents. -/
def toc (bs : List Block) : List (Nat × String × String) :=
  bs.filterMap fun
    | .heading n t => if n == 2 || n == 3 then some (n, t, slug t) else none
    | _ => none

/-- The document's first paragraph rendered as plain text, for meta tags. -/
def summary (bs : List Block) : String :=
  let raw := bs.findSome? fun
    | .para t => some t
    | _ => none
  match raw with
  | none => ""
  | some t => trim (plain t)

end Site.Markdown
