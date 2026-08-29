# SKI combinator calculus

* **Authors**: Moses Schönfinkel (1924) and Haskell Curry (1930).
* **Canonical reference**: Schönfinkel, *Über die Bausteine der
  mathematischen Logik* (Mathematische Annalen 92, 1924); Curry,
  *Grundlagen der kombinatorischen Logik* (American Journal of Mathematics
  52, 1930). Both are the mathematics, not an implementation; the language
  below is the mathematics with a file extension.
* **Implementation**: [`Langlib/Languages/Ski/`](../../Langlib/Languages/Ski/).
* **Examples**: [`Langlib/Examples/Ski/`](../../Langlib/Examples/Ski/).

## Why it is here

Every other completeness proof in this library is a register-machine
simulation, which makes the collection lopsided: it says nothing about the
functional route to universality. SKI is the other route. It is also the
core of [Unlambda](../unlambda/spec.md), whose surface syntax is an
esoteric joke wrapped around exactly this calculus, so the two live next to
each other.

It is not itself an esoteric language, and this page does not pretend
otherwise. It is the smallest thing you can call a programming language:
three constants and juxtaposition.

## History

Schönfinkel's 1924 paper set out to remove bound variables from logic
entirely. He gave the combinators now called `I`, `K` and `S` (his `I`,
`C` and `S`), and showed that any expression built from them and
application can stand in for a quantifier-free formula with variables.
Curry rediscovered and developed the system in the 1930s, and the *bracket
abstraction* algorithm — the mechanical translation from lambda terms to
combinators — is his.

The name "SKI" is later folklore. What matters is the theorem: bracket
abstraction turns any closed lambda term into an equivalent term over `S`
and `K`, so the calculus is as expressive as the untyped lambda calculus,
and therefore computes every computable function.

## The language

A term is

```text
term ::= S | K | I | term term | ( term )
```

Application associates to the left, so `SKKI` means `((SK)K)I`, and
brackets are only needed for an argument that is itself an application.
The three reduction rules are

```text
I x     -> x
K x y   -> x
S x y z -> x z (y z)
```

`I` is definable as `SKK` and is kept only for legibility.

There is no input, no output, no state and no error. A run either reaches a
normal form or reduces forever.

## Semantic decisions in LangLib

Every decision is small, because there is not much language to decide
about.

* **Normal order.** The interpreter contracts the leftmost outermost
  redex. This is the strategy the standardisation theorem is stated about:
  if a term has a normal form, normal-order reduction reaches it.
  Applicative order would not, and `K I (SII(SII))` is the standard
  witness — normal order returns `I`, applicative order diverges trying to
  reduce the argument.
* **The observable behaviour is the normal form.** SKI has no output
  instruction, so `Langlib.Ski.evalProg` prints the normal form, rendered
  with the minimum number of brackets, followed by a newline. A term with
  no normal form runs out of fuel and prints nothing, which is how the
  tests pin down divergence.
* **Fuel is reduction steps.** One unit pays for one contraction.
* **Comments.** `#` to end of line, which the calculus of course does not
  have; the example files need somewhere to explain themselves.
* **Parse errors** name a line and column: an unrecognised character, an
  unclosed or unmatched bracket, empty brackets, and the empty program.

## Computational class

**Turing complete**, by bracket abstraction from the untyped lambda
calculus. LangLib's machine-checked statement of that claim is not yet
written; the entry in [docs/README.md](../README.md) tracks it. The
argument the proof will follow is the classical one, and it is the reason
this language is in the library: it reaches universality without a program
counter anywhere in sight.

## Trying it

`SKK` is the identity, so `SKKI` reduces to `I`.

```
lake exe ski Langlib/Examples/Ski/identity.ski
```

Output:

```
I
```

`K` is true and `SK` is false, because choosing a branch is choosing an
argument. The example applies the false one to `S` and `I`.

```
lake exe ski Langlib/Examples/Ski/booleans.ski
```

Output:

```
I
```

Bracket abstraction turns `\f\x\y. f y x` into a term with no variables in
it; applied to `K`, `S` and `I` it swaps the last two.

```
lake exe ski Langlib/Examples/Ski/flip.ski
```

Output:

```
I
```

Church numerals: two plus three, with the answer applied to `S` and `K` so
that counting the `S`s in the normal form counts the numeral.

```
lake exe ski Langlib/Examples/Ski/church.ski
```

Output:

```
S(S(S(S(SK))))
```

`SII(SII)` reduces to itself, so it has no normal form and the run ends by
exhausting its fuel.

```
lake exe ski --fuel 10000 Langlib/Examples/Ski/omega.ski
```

Output:

```
ski: out of fuel after 10000 steps (raise with --fuel)
```

## Compilation from Turpentine

Not planned: see [compiler.md](compiler.md).
