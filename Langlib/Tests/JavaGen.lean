import Langlib.Common.TestHarness
import Langlib.Languages.JavaGen

/-! # JavaGen: subtype, loader and record regressions

The Java conformance layer is `scripts/javagen-conformance.py`; these tests
also cover invalid programs and finite budgets that are not Java verdicts.
-/

namespace Langlib.Tests.JavaGen
open Langlib.Common
open Langlib.JavaGen

private def ex (name : String) : Source := .file s!"Langlib/Examples/JavaGen/{name}.jgen"

def suite : Suite where
  name := "javagen: subtyping and validation"
  run := runWithAnswer
  cases :=
    [ { name := "reflexive example", source := ex "reflexive",
        expect := .outputs "accepted\nBox<Z> <: Box<Z>\nZ <: Z\n" }
    , { name := "contravariant example", source := ex "contravariant",
        expect := .outputs ("accepted\nSink<Parent<Z>> <: Sink<Child<Z>>\n" ++
          "Child<Z> <: Parent<Z>\n  via Parent<Z>\nZ <: Z\n") }
    , { name := "ground rule retains erased payload", source := ex "ground",
        expect := .outputs "accepted\nFinish<Payload<Payload<Z>>> <: Z\n  via Z\n" }
    , { name := "equal diamond keeps first path", source := ex "diamond",
        expect := .outputs "accepted\nBottom<Z> <: Top<Z>\n  via Left<Z>\n  via Top<Z>\nZ <: Z\n" }
    , { name := "unrelated heads reject", source := ex "rejected",
        expect := .runtimeError "not a subtype" }
    , { name := "recursive argument is legal and loops", source := ex "loop",
        fuel := 20, expect := .diverges }
    , { name := "zero fuel cannot accept", source := .inline "zero Z; check Z <: Z;",
        fuel := 0, expect := .diverges }
    , { name := "one fuel accepts Z", source := .inline "zero Z; check Z <: Z;",
        fuel := 1, expect := .outputs "accepted\nZ <: Z\n" }
    , { name := "reflexivity needs final step", source := ex "reflexive",
        fuel := 1, expect := .diverges }
    , { name := "reflexivity exact budget", source := ex "reflexive",
        fuel := 2, expect := .outputs "accepted\nBox<Z> <: Box<Z>\nZ <: Z\n" }
    , { name := "zero fuel cannot reject", source := ex "rejected",
        fuel := 0, expect := .diverges }
    , { name := "stdin does not affect execution", source := ex "reflexive",
        input := "unused input\n", expect := .outputs "accepted\nBox<Z> <: Box<Z>\nZ <: Z\n" }
    , { name := "Z has no unary superclass",
        source := .inline "zero Z; interface A<x> {} check Z <: A<Z>;",
        expect := .runtimeError "not a subtype" }
    , { name := "unary constructor need not inherit Z",
        source := .inline "zero Z; interface A<x> {} check A<Z> <: Z;",
        expect := .runtimeError "not a subtype" }
    , { name := "contravariance rejects the covariant direction", source := .inline ("zero Z; interface P<x> {} interface C<x> extends P<x> {} " ++
         "interface S<x> {} check S<C<Z>> <: S<P<Z>>;"),
        expect := .runtimeError "not a subtype: P<Z> <: C<Z>" }
    , { name := "ground rewrite inside a transitive path is retained", source := .inline ("zero Z; interface C<x> extends M<M<Z>> {} interface M<x> extends Z {} " ++
         "check C<M<Z>> <: Z;"),
        expect := .outputs "accepted\nC<M<Z>> <: Z\n  via M<M<Z>>\n  via Z\n" }
    , { name := "forward declaration", source := .inline "zero Z; interface C<x> extends P<x> {} interface P<x> {} check C<Z> <: P<Z>;",
        expect := .outputs "accepted\nC<Z> <: P<Z>\n  via P<Z>\nZ <: Z\n" }
    , { name := "comments and CRLF", source := .inline "// comment\r\nzero\tZ; // after token\r\ncheck Z <: Z;// no newline",
        expect := .outputs "accepted\nZ <: Z\n" }
    , { name := "duplicate constructor", source := .inline "zero Z; interface A<x> {} interface A<x> {} check Z <: Z;",
        expect := .parseError "duplicate constructor" }
    , { name := "unknown query constructor", source := .inline "zero Z; check A<Z> <: Z;",
        expect := .parseError "unknown constructor" }
    , { name := "unknown nested superclass constructor", source := .inline "zero Z; interface A<x> extends A<B<A<x>>> {} check Z <: Z;",
        expect := .parseError "unknown constructor 'B'" }
    , { name := "even variable depth", source := .inline "zero Z; interface A<x> extends B<B<x>> {} interface B<x> {} check Z <: Z;",
        expect := .parseError "odd constructor depth" }
    , { name := "bare variable superclass", source := .inline "zero Z; interface A<x> extends x {} check Z <: Z;",
        expect := .parseError "odd constructor depth" }
    , { name := "direct cycle", source := .inline "zero Z; interface A<x> extends A<x> {} check Z <: Z;",
        expect := .parseError "cyclic inheritance" }
    , { name := "indirect cycle", source := .inline "zero Z; interface A<x> extends B<x> {} interface B<x> extends A<x> {} check Z <: Z;",
        expect := .parseError "cyclic inheritance" }
    , { name := "repeated direct superclass", source := .inline "zero Z; interface A<x> extends B<x>, B<x> {} interface B<x> {} check Z <: Z;",
        expect := .parseError "repeated direct superclass" }
    , { name := "unequal indirect diamond", source := .inline ("zero Z; interface T<x> {} interface L<x> extends T<x> {} " ++
         "interface R<x> extends T<Z> {} interface B<x> extends L<x>, R<x> {} " ++
         "check B<Z> <: T<Z>;"),
        expect := .parseError "multiple instantiation" }
    , { name := "diamond comparison includes nested substitutions", source := .inline ("zero Z; interface T<x> {} interface N<x> {} " ++
         "interface L<x> extends T<N<N<x>>> {} interface R<x> extends T<N<N<Z>>> {} " ++
         "interface B<x> extends L<x>, R<x> {} check Z <: Z;"),
        expect := .parseError "multiple instantiation" }
    , { name := "free variable in query", source := .inline "zero Z; check x <: Z;",
        expect := .parseError "closed" }
    , { name := "wrong binder", source := .inline "zero Z; interface A<y> {} check Z <: Z;", expect := .parseError "expected 'x'" }
    , { name := "Z is nullary", source := .inline "zero Z; check Z<Z> <: Z;",
        expect := .parseError "expected '<:'" }
    , { name := "unary constructor needs argument", source := .inline "zero Z; interface A<x> {} check A <: Z;", expect := .parseError "expected '<'" }
    , { name := "no trailing query", source := .inline "zero Z; check Z <: Z; check Z <: Z;",
        expect := .parseError "trailing token" }
    , { name := "empty source", source := .inline "", expect := .parseError "expected 'zero'" }
    , { name := "invalid character includes position", source := .inline "zero Z;\n@",
        expect := .parseError "2:1: unexpected character" }
    , { name := "infer addition", source := ex "add-two", expect := .outputs "4\n" }
    , { name := "infer zero", source := ex "zero-answer", expect := .outputs "0\n" }
    , { name := "Fibonacci ten via type recurrence", source := ex "fib", expect := .outputs "55\n" }
    , { name := "factorial five via type recurrence", source := ex "fact", expect := .outputs "120\n" }
    , { name := "sum one through ten", source := ex "sum", expect := .outputs "55\n" }
    , { name := "numeric fuel exhaustion", source := ex "fact", fuel := 10, expect := .diverges }
    , { name := "two answer holes", source := .inline "zero Z; check answer <: answer;",
        expect := .parseError "only one answer hole" }
    , { name := "numeral constructors are required", source := .inline "zero Z; check Z <: answer;",
        expect := .parseError "require" }
    , { name := "Succ must have no superclasses", source := .inline "zero Z; interface Succ<x> extends Z {} interface Pad<x> {} check Z <: answer;",
        expect := .parseError "must have no superclasses" }
    , { name := "answer forbidden in inheritance", source := .inline "zero Z; interface A<x> extends answer {} check Z <: Z;",
        expect := .parseError "only in a query" }
    , { name := "erasing the hole does not invent zero", source := .inline "zero Z; interface Succ<x> {} interface Pad<x> {} interface H<x> extends Z {} check H<answer> <: Z;",
        expect := .runtimeError "erased without being constrained" }
    , { name := "ambiguous answer head is refused", source := .inline "zero Z; interface Succ<x> {} interface Pad<x> {} interface H<x> extends Z, Succ<Z> {} check H<Z> <: answer;",
        expect := .runtimeError "ambiguous numeric heads" }
    , { name := "bad padding is refused", source := .inline "zero Z; interface Succ<x> {} interface Pad<x> {} check Succ<Succ<Z>> <: answer;",
        expect := .runtimeError "padded unary numeral" }
    ]

def suites : List Suite := [suite]

/-- Source round trips, stable output bytes, and preservation of payloads of
different sizes. These compare distinct computations rather than just exits. -/
def propertyChecks : IO (List String) := do
  let mut failures := []
  for name in ["reflexive", "contravariant", "ground", "diamond", "rejected", "loop",
      "add-two", "zero-answer", "fib", "fact", "sum"] do
    let src ← IO.FS.readFile s!"Langlib/Examples/JavaGen/{name}.jgen"
    match parseSyntax src with
    | .error e => failures := s!"{name}: {e}" :: failures
    | .ok ast =>
      unless (match parseSyntax ast.render with | .ok got => got == ast | .error _ => false) do
        failures := s!"{name}: parse/render round trip" :: failures
      match prepare ast with
      | .error e => failures := s!"{name}: {e}" :: failures
      | .ok p =>
        let eval := if p.source.answerSide.isSome then evalAnswer p else evalProg p
        let a := eval 2000
        let b := eval 4000
        if a.exit != .outOfFuel && (a.exit != b.exit || a.output != b.output) then
          failures := s!"{name}: completed result changed" :: failures
  let mut records : List ByteArray := []
  for n in [0, 1, 2, 8] do
    let payload := Ty.render (List.replicate n "P")
    let src := "zero Z; interface P<x> {} interface H<x> extends Z {} check H<" ++
      payload ++ "> <: Z;"
    match run src Input.empty 1 with
    | .error e => failures := e :: failures
    | .ok r =>
      if r.exit != .halted || records.any (· == r.output) then
        failures := s!"ground record lost payload of depth {n}" :: failures
      records := r.output :: records
  return failures.reverse

end Langlib.Tests.JavaGen
