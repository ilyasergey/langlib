/-!
# Small HTML helpers

Escaping, slugs, and a few string utilities that the rest of the generator
leans on. Nothing clever: the site is a few dozen pages, so clarity beats
speed everywhere in this package.
-/

namespace Site

/-- ASCII-trim, spelled once so the deprecation dance lives in one place. -/
def trim (s : String) : String := s.trimAscii.toString

/-- Escape text for HTML character data and double-quoted attributes. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
    | c   => acc.push c

/-- A GitHub-flavoured anchor slug: lowercase, alphanumerics and dashes. -/
def slug (s : String) : String :=
  let cs := s.toList.filterMap fun c =>
    if c.isAlphanum then some c.toLower
    else if c == ' ' || c == '-' || c == '_' then some '-'
    else none
  -- collapse runs of dashes and trim them from both ends
  let rec collapse : List Char → List Char
    | [] => []
    | '-' :: rest =>
      let rest := collapse rest
      match rest with
      | '-' :: _ => rest
      | _ => '-' :: rest
    | c :: rest => c :: collapse rest
  let cs := collapse cs
  let cs := cs.dropWhile (· == '-')
  let cs := (cs.reverse.dropWhile (· == '-')).reverse
  String.ofList cs

/-- Does `s` start with any of `ps`? -/
def startsWithAny (s : String) (ps : List String) : Bool :=
  ps.any (s.startsWith ·)

/-- Split on `\n`, dropping a single trailing empty line. -/
def lines (s : String) : List String :=
  let ls := (s.replace "\r\n" "\n").splitOn "\n"
  match ls.reverse with
  | "" :: rest => rest.reverse
  | _ => ls

/-- Number of leading spaces. -/
def indentOf (s : String) : Nat := (s.toList.takeWhile (· == ' ')).length

/-- Is the line entirely blank? -/
def isBlank (s : String) : Bool := s.all fun c => c == ' ' || c == '\t'

/-- Remove up to `n` leading spaces. -/
def dedent (n : Nat) (s : String) : String :=
  let rec go : Nat → List Char → List Char
    | 0, cs => cs
    | _ + 1, [] => []
    | k + 1, c :: rest => if c == ' ' then go k rest else c :: rest
  String.ofList (go n s.toList)

/-- Drop the first `n` characters. -/
def dropChars (n : Nat) (s : String) : String := String.ofList (s.toList.drop n)

/-- Keep the first `n` characters. -/
def takeChars (n : Nat) (s : String) : String := String.ofList (s.toList.take n)

/-- `String.contains` for substrings. -/
def hasSubstr (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- An HTML attribute, already escaped. -/
def attr (name value : String) : String := s!" {name}=\"{escape value}\""

end Site
