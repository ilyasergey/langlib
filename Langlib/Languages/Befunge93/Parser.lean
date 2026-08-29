import Langlib.Languages.Befunge93.Syntax

/-!
# Befunge-93: loader

"Parsing" Befunge-93 is loading text into the playfield: rows from the top,
columns from the left, everything else spaces. Any character is legal in a
cell (unvisited cells are free comment space), so the only parse errors are
size errors: a line wider than 80 columns or a program taller than 25 lines.

`bef.c` v2.25 silently truncates long lines and drops lines past the 25th;
we reject oversized programs instead (see `docs/befunge93/spec.md`,
decision 12). A trailing newline at end of file is not an extra line, and a
trailing `'\r'` (CRLF sources) is stripped from each line.
-/

namespace Langlib.Befunge93

/-- Load Befunge-93 source into a `Playfield`. Fails only when the program
does not fit on the 80x25 torus. -/
def parse (src : String) : Except String Playfield := do
  let lines := (src.splitOn "\n").map fun l =>
    if l.endsWith "\r" then (l.dropEnd 1).toString else l
  -- A final newline produces one trailing empty entry; it is not a line.
  let lines := match lines.reverse with
    | "" :: rest => rest.reverse
    | _ => lines
  if lines.length > height then
    throw s!"program has {lines.length} lines; the playfield is only {height} tall"
  let mut pf := Playfield.empty
  let mut y := 0
  for line in lines do
    if line.length > width then
      throw s!"line {y + 1} is {line.length} characters long; the playfield is only {width} wide"
    let mut x := 0
    for c in line.toList do
      pf := pf.set x y (Int.ofNat c.toNat)
      x := x + 1
    y := y + 1
  return pf

end Langlib.Befunge93
