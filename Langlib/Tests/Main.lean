/-!
Test driver for langlib, run by `lake test`.

Golden tests for each language are registered here as languages land.
-/

def main : IO UInt32 := do
  IO.println "langlib test suite: no tests registered yet"
  return 0
