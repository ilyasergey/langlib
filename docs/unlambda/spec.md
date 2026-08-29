# Unlambda

* **Author**: David Madore, 1999.
* **Canonical reference**: Madore's *The Unlambda Programming Language*
  page, http://www.madore.org/~david/programs/unlambda/, and the
  `unlambda-2.0.0.tar.gz` distribution it offers, which ships four
  interpreters (C, reference-counting C, Java, Scheme) and a specification
  section. Where they disagree, and they do, this page says which one
  LangLib follows and why. Community page:
  https://esolangs.org/wiki/Unlambda (CC0).
* **Implementation**: [`Langlib/Languages/Unlambda/`](../../Langlib/Languages/Unlambda/).
* **Examples**: [`Langlib/Examples/Unlambda/`](../../Langlib/Examples/Unlambda/).

## The joke

Every other tarpit in this library is a machine with the comforts removed:
a tape, a stack, a register file. Unlambda is a *functional* language with
the comforts removed, and the comfort it removes is the one thing everybody
assumes a functional language must have. There are no variables. There are
no lambdas. In a language named after the lambda.

What is left is application — written prefix, with a backquote, so that no
parentheses are ever needed — and a handful of nullary builtins. Madore's
own summary is that the language is "an obfuscated functional programming
language", and the obfuscation is not syntax. It is that you must write
every program in the image of bracket abstraction, and you must do the
abstraction yourself.

## History

Madore published Unlambda in 1999 with the S and K combinators, the
identity `i`, the black hole `v`, the printer `.x`, the delay `d`, and
call/cc as `c` — a call/cc in a language with no variables, which is the
sort of thing that gets a language remembered. Version 2 added `e` to exit,
`@` to read a byte, `?x` to test it and `|` to hand it back.

The distribution's own examples include a quine and a Fibonacci printer,
and the language became the standard reference for "esoteric but
genuinely functional".

## The language

A program is one expression:

```text
expr ::= ` expr expr        -- application, prefix
       | k | s | i | v | d | c | e | @ | |
       | .x                 -- print the byte x, return the argument
       | ?x                 -- was the last byte read x?
       | r                  -- .x with x a newline
```

The builtins, as functions:

| Builtin | Applied to `a` | |
|---|---|---|
| `i` | `a` | identity |
| `k` | a function returning `a` | so `` ``kXY `` is `X` |
| `s` | substitution | `` ```sXYZ `` is `` ``XZ`YZ `` |
| `v` | `v` | the black hole: swallows everything, forever |
| `.x` | `a`, after printing `x` | |
| `r` | `a`, after printing a newline | |
| `d` | a promise holding `a` | *special form*: see below |
| `c` | `a` applied to the current continuation | call/cc |
| `e` | — | exits the program |
| `@` | `a` applied to `i` (a byte was read) or to `v` (end of input) | |
| `?x` | `a` applied to `i` if the last byte read was `x`, else to `v` | |
| `|` | `a` applied to `.b`, where `b` was the last byte read (`v` if none) | |

`d` is the only special form. In `` `FG ``, if `F` evaluates to `d` then
`G` is *not* evaluated; the result is a promise, and `G` runs when the
promise is applied. That test is on the value of `F`, not on its syntax,
which matters: `` ``id X `` delays too, because `` `id `` evaluates to `d`.

Conditionals are the thing the table does not have. There is no `if`. The
idiom is that `i` and `v` are the two branches of every test: `?x` hands
its argument `i` or `v`, and `v` swallows whatever comes next, so putting
the "then" branch behind a promise and applying it gives a conditional
whose "else" is doing nothing at all. `until.unl` shows the harder case,
where the program has to *stop*, and does it with call/cc.

## Semantic decisions in LangLib

The reference implementations disagree with each other in several places,
so each of these says what we do and why.

1. **The evaluator is an abstract machine**, with an explicit continuation
   stack rather than metalanguage recursion. Forced by the language: `c`
   has to capture the rest of the computation and restore it later, and
   `d` has to be intercepted on a value that has just arrived. One fuel
   unit pays for one machine step — an expression evaluated, an
   application performed, or a value returned to a continuation.
2. **Program and input come from different places.** Madore's interpreters
   read both from standard input, stopping at the end of the first complete
   expression and treating the rest as the program's input. LangLib takes
   the program from a file and the input from stdin, so trailing text is a
   mistake and is reported with its line and column.
3. **`r` is `.x` carrying a newline**, not a separate builtin, exactly as
   the specification says. A `.x` whose byte is a newline renders back as
   `r`, which keeps a rendered program on one line.
4. **The delay rule tests the value.** `` `FG `` delays whenever `F`
   *evaluates* to `d`, however it got there.
5. **`d` applied to an already-evaluated value keeps that value.** This
   happens through `c`: `` `cd `` hands `d` a continuation, which is a
   value, and Madore's "Promises" note says the result is a promise holding
   it. So `` ``cd.X `` prints `X`.
6. **The `s` rule can be caught by the delay rule.** In `` ```sXYZ ``, the
   value of `` `XZ `` is computed first and `` `YZ `` waits; if `` `XZ ``
   evaluates to `d`, the waiting application becomes a promise rather than
   running.
7. **`e` exits.** The two C interpreters in the 2.0.0 distribution parse
   `e` as a second spelling of `c`; the specification section, the Java
   interpreter and the Scheme one make it exit. We follow the
   specification, so `` ``e.X.Y `` prints nothing.
8. **End of input is `v`.** `@` applies its argument to `i` when it read a
   byte and to `v` when it did not, and `|` with no byte read yet hands
   over `v` rather than a printer. This is the specification's rule and all
   four interpreters agree.
9. **Both letter cases are accepted** for every builtin letter. The
   interpreters are split on `r` alone — Java and Scheme take `R`, C and
   Caml do not — while all of them take `K`, `S`, `I`, `V`, `D`, `C` and
   `E`, so the only uniform rule is the permissive one.
10. **`.x` and `?x` carry a byte, not a character.** The parser scans
    bytes, as Madore's do, so `.é` in a UTF-8 file is a dot carrying the
    first byte of the encoding followed by an unrecognised command, and it
    is reported as one.
11. **`#` starts a comment** that runs to the end of the line. Whitespace
    is ignored everywhere except immediately after `.` or `?`, where the
    next byte is the payload — including a space or a newline.
12. **There are no runtime errors.** Every value can be applied to every
    value, so a run either halts or runs forever. The only failures are
    parse errors and running out of fuel.

## Computational class

**Turing complete**, and by the route no other language in this library
takes. Unlambda contains the `S` and `K` combinators and application, which
is the whole of the [SKI calculus](../ski/spec.md); bracket abstraction
embeds the untyped lambda calculus into SKI; so Unlambda computes every
computable function. `c` and `d` are not needed for the argument and are
out of scope for it.

LangLib's machine-checked version of this claim is not yet written — see
the status matrix in [docs/README.md](../README.md). It is the one
completeness proof in the plan that is not a register-machine simulation,
which is exactly why the library carries SKI as a separate language.

## Trying it

A chain of printers, applied left to right: `` `.H.e `` prints `H` and
returns `.e`, and `r` at the end prints the newline.

```
lake exe unlambda Langlib/Examples/Unlambda/hello.unl
```

Output:

```
Hello, world!
```

The delay special form, doing the one thing that makes it a special form:
the operand that appears *second* in the source runs *first*.

```
lake exe unlambda Langlib/Examples/Unlambda/delay.unl
```

Output:

```
now
later
```

Unlambda has no numbers, so a counter has to be the program's own shape.
Five copies of one step function, each wrapping the last in another
asterisk.

```
lake exe unlambda Langlib/Examples/Unlambda/stars.unl
```

Output:

```
*
**
***
****
*****
```

`c` captures the continuation of the `c` itself; here the captured
continuation is handed a printer, so the `c` returns immediately and the
operand that would have printed `skipped` is never evaluated.

```
lake exe unlambda Langlib/Examples/Unlambda/callcc.unl
```

Output:

```
start
end
```

The conditional idiom, reading input: `@` reads a byte and selects `i` or
`v`, and the recursive call sits behind a `d` promise so that only the `i`
branch forces it.

```
echo -n meow | lake exe unlambda Langlib/Examples/Unlambda/cat.unl
```

Output:

```
meow
```

Stopping is harder than continuing, because `v` can swallow a branch but
cannot select one. This one echoes until the first `q` and then throws the
whole computation away with a captured continuation.

```
echo -n abcqdef | lake exe unlambda Langlib/Examples/Unlambda/until.unl
```

Output:

```
abc
```

## Compilation from Turpentine

Planned, and unlike every other backend it would not be a machine
simulation: see [compiler.md](compiler.md).
