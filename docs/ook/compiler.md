# Compiling Turpentine to Ook!

* **Status**: implemented, and the syntax round trip is proved.
* **Family**: TapeIR, via brainfuck.
* **Implementation**: [`Langlib/Languages/Turpentine/Compile/Ook.lean`](../../Langlib/Languages/Turpentine/Compile/Ook.lean).
* **Completeness witness**: [`Langlib/Computability/Ook.lean`](../../Langlib/Computability/Ook.lean).
* **Tests**: [`Langlib/Tests/CompileOok.lean`](../../Langlib/Tests/CompileOok.lean), 27 cases.

## There really is nothing to generate

Ook! is brainfuck with the eight commands spelled as pairs of the words
`Ook.`, `Ook?`, `Ook!`. `Langlib/Languages/Ook/` has no interpreter of its
own: it parses into `Langlib.Brainfuck.Prog` and calls the brainfuck
evaluator. `Langlib.Ook.Prog` is a definitional abbreviation for
`Langlib.Brainfuck.Prog`.

So the backend is two lines. `compile` *is*
`Langlib.Turpentine.Compile.Brainfuck.compile` at a different type
ascription, and `compileSource` swaps `Langlib.Brainfuck.Prog.render` for
`Langlib.Ook.render`:

```lean
def compile (p : Program) : Except String Langlib.Ook.Prog :=
  Langlib.Turpentine.Compile.Brainfuck.compile p

def compileSource (src : String) : Except String String := do
  let prog ← parse src
  let ook ← compile prog
  return Langlib.Ook.render ook
```

The one thing the brainfuck backend does that this one cannot is the
header comment. Brainfuck has no comment syntax, so the brainfuck backend
smuggles its provenance note into a loop that never runs; Ook! rejects
anything that is not one of its three words, so every token in a compiled
`.ook` file is load-bearing.

## Fragment

Exactly the brainfuck backend's fragment: 16-bit two's complement
integers, fixed-size arrays, no recursion, runtime errors compiled to an
infinite loop. See [docs/brainfuck/compiler.md](../brainfuck/compiler.md)
for the tape layout, the number representation and the list of rejected
constructs. Anything that backend rejects, this one rejects with the same
message.

## Run a compiled program

Two compiled examples ship in the repository, and both were produced by
`compileSource` from Turpentine sources.

```
lake exe ook --eof zero Langlib/Examples/Ook/compiled/hello.ook
```

```
Hello, Turpentine!
```

`hello.ook` is `Langlib/Examples/Turpentine/hello.turp` compiled.
`letter-a.ook` is `printByte(65); printByte(10);` compiled; it prints one
letter.

```
lake exe ook --eof zero Langlib/Examples/Ook/compiled/letter-a.ook
```

```
A
```

The `--eof zero` is not decoration. The generated code reads bytes and
tests for end of input by comparing against zero, which is the convention
the brainfuck backend targets; run it under any other convention and the
`cat`-shaped programs will not terminate.

Here is what the top of a compiled file looks like. The opening run of
`Ook. Ook?` is the code walking right to its first working cell.

```
head -3 Langlib/Examples/Ook/compiled/hello.ook
```

```
Ook. Ook? Ook. Ook? Ook. Ook? Ook. Ook? Ook. Ook? Ook. Ook? Ook. Ook? Ook. Ook?
Ook. Ook? Ook. Ook? Ook. Ook? Ook. Ook? Ook. Ook? Ook! Ook? Ook! Ook! Ook? Ook!
Ook. Ook. Ook. Ook. Ook. Ook. Ook. Ook. Ook. Ook. Ook. Ook. Ook. Ook. Ook. Ook.
```

## What it costs

Every brainfuck command becomes two four-character words plus one
separator, so an Ook! file is exactly **ten times** the size in bytes of
the brainfuck it came from. (Nine times is the figure usually quoted; that
counts the words without the separator.)

| Turpentine example | brainfuck commands | Ook! bytes |
|---|---|---|
| `printByte(65); printByte(10);` | 96 | 960 |
| `hello.turp` | 460 | 4,600 |
| `cat.turp` | 27,376 | 273,760 |
| `sumdigits.turp` | 336,448 | 3,364,480 |
| `gcd.turp` | 260,165 | 2,601,650 |
| `collatz.turp` | 367,350 | 3,673,500 |
| `sort.turp` | 522,986 | 5,229,860 |

The certified compiler is dearer again, because it goes through the
unlimited register machine and a unary tape. The URM program `S 0; S 0`,
which computes 2, compiles to 10,197 brainfuck commands, hence **101,970
bytes** of Ook!, and that number is pinned down by a test.

Files of that size are the point rather than a defect. They are also why
the test suite compiles the small examples.

## The correctness story

Two claims, and they are different claims.

**The program is right.** `Langlib.Ook.Prog` is `Langlib.Brainfuck.Prog`
and `Langlib.Ook.run` is the brainfuck evaluator, so the compiled program
is the brainfuck backend's compiled program and inherits whatever is known
about it. The hand-written backend is not verified; what *is* verified is
the derived compiler obtained from the completeness witness, and
`Langlib.Computability.agree` says the two must agree wherever both accept
a program.

**The text is right.** This is the Ook!-specific part, and it is proved:

```lean
theorem parse_renderOok (p : Prog) :
    Langlib.Ook.parse (renderOok p) = .ok p
```

for every `p`. Parsing the rendering of any brainfuck program gives that
program back, through the shipped `Langlib.Ook.parse`: its character-level
tokeniser and its pair-consuming loop are both covered, so this is a
statement about the parser users actually run, not about a model of it.
`Langlib.Computability.parse_render_compile` instantiates it at the
compiler's own output.

### The `renderOok` caveat, stated plainly

`Langlib.Ook.render` lays its words out sixteen to a line with a
`private partial def chunks`, and `Langlib.Brainfuck.Op.render` is itself a
`partial def`. Lean compiles a `partial def` to an **opaque** constant: no
equations, no reduction, and therefore no theorem can mention it at all.
`#print Langlib.Brainfuck.Op.render` says `opaque` and that is the end of
the matter.

`renderOok` is a total re-implementation of the same layout, and it is
what the theorem is about. The gap between it and the shipped renderer is
closed by test, not by proof: the `shipped renderer = proved renderer`
suite in `Langlib/Tests/CompileOok.lean` compares the two byte-for-byte on
the programs the backend emits. That is an honest test-level bridge, and
it is worth knowing it is a test.

Also not proved, and not claimed: the other direction,
`renderOok <$> parse s = s`. It is false. Parsing forgets line breaks, and
a hand-written Ook! program need not use this layout.

## Ook! is Turing complete

`Langlib/Computability/Ook.lean` carries
`ookComplete : TuringComplete OokLang`. Since the program type and the
evaluator are brainfuck's, the witness is `brainfuckComplete`'s
unchanged: same compiler from the unlimited register machine, same input
encoding, same output decoding, same simulation proof. What
`parse_renderOok` adds is that those programs can be written down as Ook!
and read back, which is what makes the claim a claim about the *language*.

What that does **not** say, and the distinction matters:

* It does not say Ook! computes every partial computable function. Going
  from "simulates every URM program that halts" to that statement is a
  cited classical result (Shepherdson and Sturgis 1963), not a Lean proof;
  cslib proves no equivalence between URM-computability and any other
  model. `Langlib.Computability.computes_of_turingComplete` is the honest
  statement of what does follow.
* It says nothing about divergence. `simulates` constrains halting runs
  only, so nothing here rules out a compiled program halting where the
  source machine loops.

### The axiom audit

```
lake env lean scripts/axioms.lean
```

The Ook! lines of the output:

```
'Langlib.Computability.ookComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.OokSyntax.parse_renderOok' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.parse_render_compile' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.OokSyntax.tokenize_renderOok' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.OokSyntax.pairKey' depends on axioms: [propext, Quot.sound]
```

Only Lean's three standard axioms, and `pairKey` needs two of them. There
is no `sorryAx` and no `axiom` anywhere in the development.

## How the parser proof is arranged

Worth recording, because the same shape works for any of langlib's
`for`-loop parsers.

`Langlib.Ook.parse` is two loops over private state, and neither loop body
can be named from another module: `Tok`, `Pos`, `classify`, `tokenize` and
`pairUp` are all `private`. Writing the body out by hand does not help
either, because the `match` in a copy compiles to a different auxiliary
matcher than the original, and `rw` will not unify the two.

The way through is to quantify over the loop body. `TokSpec f` says what
the tokeniser's body does on one character; `PairSpec g` says what the
pair loop's body does on one word pair. The loop lemmas take those as
hypotheses and never look inside `f` or `g`, so they mention no private
name and no matcher. At the point of application, `refine` unifies the
body variable with the real body, and every hypothesis is then closed by
`rfl` on a concrete character or word. The position type and the token
type stay abstract throughout, which is what keeps `Pos` and `Tok` out of
the statements.

The two remaining obligations are arithmetic: the token count is even (so
`parse`'s odd-number-of-Ooks check passes), and `pairUp` recovers exactly
the word pairs the program spells.

## Running the tests

```
lake test
```

The Ook! compiler suites are `turpentine -> ook`,
`turpentine -> ook (reference cross-check)`,
`turpentine -> ook (shipped renderer = proved renderer)`,
`urm -> ook (certified compiler)` and
`urm -> ook (rendered source size)`, 27 cases in total. The first two are
the differential test: one expected string, run once by
`Langlib.Turpentine.run` and once by compiling to Ook! text, parsing that
text back and running it on the brainfuck core. Every expected string was
taken from a run of the reference interpreter first.
