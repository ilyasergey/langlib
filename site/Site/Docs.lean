import Site.Markdown

/-!
# Reading the repository, and rewriting links between documents

Every page of langlib.wtf that carries prose is generated from a Markdown
file that already exists in the repository. Nothing is forked. The only work
this module does is (a) find those files relative to the repository root and
(b) turn a link as written in the repository into a link that works on the
site.

Rule for (b): resolve the destination against the directory of the document
being rendered, then look the resulting repository path up in a table. A path
the site publishes becomes a site URL; anything else becomes a link into the
repository on GitHub, so a reader following `Langlib/Examples/Brainfuck/` ends
up looking at the actual examples.
-/

namespace Site

/-- Where the repository lives on GitHub, for links to files the site does not publish. -/
def repoURL : String := "https://github.com/langlib/langlib"

/-- The branch those links point at. -/
def repoBranch : String := "master"

/-- The site's own domain, used for canonical links and Open Graph tags. -/
def siteURL : String := "https://langlib.wtf"

/-- Join two repository-relative path fragments, resolving `.` and `..`. -/
def resolvePath (base dest : String) : String :=
  let baseParts := if base.isEmpty then [] else (base.splitOn "/").filter (· != "")
  let parts := (dest.splitOn "/").filter (· != "")
  let start := if dest.startsWith "/" then [] else baseParts
  let out := parts.foldl (init := start) fun acc p =>
    if p == "." then acc
    else if p == ".." then acc.dropLast
    else acc ++ [p]
  String.intercalate "/" out

/-- Split a `path#fragment` destination. -/
def splitFragment (s : String) : String × String :=
  match s.splitOn "#" with
  | [p] => (p, "")
  | p :: rest => (p, "#" ++ String.intercalate "#" rest)
  | [] => (s, "")

/-- A document the site publishes: its path in the repository and its URL here. -/
structure Published where
  path : String
  url : String
  deriving Inhabited

/--
Build the link rewriter for a document living at `baseDir` (a repository
relative directory, e.g. `docs/brainfuck`), given the publication table.
-/
def rewriter (published : List Published) (baseDir : String) : Markdown.Rewrite :=
  fun dest =>
    let dest := trim dest
    if dest.isEmpty then "#"
    else if startsWithAny dest ["http://", "https://", "mailto:", "//"] then dest
    else if dest.startsWith "#" then dest
    else
      let (path, frag) := splitFragment dest
      if path.isEmpty then frag
      else
        let full := resolvePath baseDir path
        match published.find? (·.path == full) with
        | some p => p.url ++ frag
        | none =>
          -- not published here, so send the reader to the repository
          let kind := if full.endsWith "/" then "tree" else "blob"
          s!"{repoURL}/{kind}/{repoBranch}/{full}{frag}"

/-- Read a file, failing loudly: a missing document is a bug in the generator. -/
def readDoc (root : String) (path : String) : IO String := do
  let full := System.FilePath.mk root / path
  unless (← full.pathExists) do
    throw <| IO.userError s!"site generator: {path} does not exist under {root}"
  IO.FS.readFile full

/-- Read a file if it is there, otherwise `none` (used for optional examples). -/
def readDoc? (root : String) (path : String) : IO (Option String) := do
  let full := System.FilePath.mk root / path
  if (← full.pathExists) then pure (some (← IO.FS.readFile full)) else pure none

end Site
