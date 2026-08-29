# URM compilation foundations for FRACTRAN

LangLib now contains a runnable URM-to-FRACTRAN compiler and proved
prime-exponent arithmetic lemmas. The whole-program simulation remains open,
so the library does not declare `fractranComplete : TuringComplete
FractranLang`.

## Representation

`URMFractran.primeAt` is an executable sequence of distinct primes. It starts
at 2 and finds each later prime by decidable search for the least prime larger
than its predecessor. Register `r` is the exponent of `primeAt r`, so register
0 is the exponent of 2.

The compiler reserves later prime indices for control phases and two scratch
counters. A micro-step consumes one control-prime factor, changes register or
scratch exponents, and produces the next control-prime factor. Distinct
control factors keep each emitted fraction gated to its own phase.

The four URM instructions compile as follows:

- `Z r` alternates two control phases while removing factors of register
  prime `r`. First-match ordering selects the removal fraction while another
  factor remains, then selects the continuation fraction.
- `S r` replaces the current control factor with the next one and adds one
  register factor.
- `T m r` first zeros `r`, transfers each factor of `m` into both `r` and a
  scratch exponent, then transfers the scratch factors back into `m`.
- `J m r q` removes pairs from `m` and `r` into separate scratch exponents.
  The pair-removal fraction occurs before the one-sided fractions. When one
  register becomes empty, first-match selection chooses the unequal branch.
  When both become empty, it chooses the equal branch. Both branches restore
  the registers before continuing.

An unconditional self-loop alternates through a private control phase. A
literal fraction `p/p` would reduce to `1/1`, which would apply in every
state.

## Output convention

FRACTRAN has no native I/O. `URMFractran.CompiledProgram` therefore bundles
the emitted fraction list with its positive starting integer. The
`ProgLang FractranLang` runner calls the existing FRACTRAN interpreter with
that integer and uses `pow2` output mode.

On reaching the halt marker, cleanup removes registers 1 through the finite
register bound. Its final fraction removes the control marker and produces
exactly `2 ^ R₀`. The interpreter's `pow2` mode prints `R₀`, and
`URMFractran.decodeOutput` parses that decimal exponent.

The register bound covers every register mentioned by the program and every
initial input register. A URM step cannot introduce another register index,
so cleanup has a finite list to traverse.

## What Lean proves

The arithmetic layer uses finite-support token stores `Nat →₀ Nat`.
Lean proves:

```lean
theorem factorization_encodeTokens (s : Tokens) (i : Nat) :
    (encodeTokens s).factorization (primeAt i) = s i
```

```lean
theorem encodeTokens_dvd_iff {a b : Tokens} :
    encodeTokens a ∣ encodeTokens b ↔ a ≤ b
```

```lean
theorem encodeTokens_apply {consume state produce : Tokens}
    (h : consume ≤ state) :
    encodeTokens state / encodeTokens consume * encodeTokens produce =
      encodeTokens (state - consume + produce)
```

```lean
theorem step_single_rule (r : Rule) (state : Tokens)
    (h : r.Enabled state) :
    Langlib.Fractran.step [r.toFrac] (encodeTokens state) =
      some (encodeTokens (state - r.consume + r.produce))
```

`step_single_rule_disabled` proves the corresponding inapplicable case.
Together these results verify the prime-exponent encoding and one-rule
execution against `Langlib.Fractran.step`.

`tokenProduct_coprime` proves that products formed from disjoint generated
prime indices are coprime, and `frac_eq_of_disjoint` proves that
`Frac.reduced` leaves such an emitted fraction unchanged.

## Remaining proof

The missing theorem connects the generated multi-rule blocks to one URM
step. It must establish these invariants for every reachable compiled state:

- exactly one control-prime exponent is one and every other control exponent
  is zero;
- scratch exponents are zero at URM instruction boundaries;
- first-match selection chooses the intended rule within the active block;
- each `Z`, `T`, and `J` loop terminates at the claimed continuation state;
- the halt cleanup produces `2 ^ R₀` and the `pow2` interpreter output
  decodes to register 0.

That per-instruction result then needs induction over `Cslib.URM.Steps` and a
fuel composition proof for `Langlib.Fractran.exec`. Until those obligations
are proved, the runnable compiler is an executable scaffold checked by
differential tests. It is not a certified compiler and does not support a
`TuringComplete FractranLang` witness.

Even after a future `TuringComplete` witness lands, that interface will say
only that every halting URM run has a corresponding halting FRACTRAN run. It
will not constrain divergent URM runs. The identification of URM-computable
functions with all partial computable functions remains the cited classical
result of Shepherdson and Sturgis (1963), since cslib does not formalize that
equivalence.

## Measured cost and verification

The two-increment program compiles to 3 fractions, 18 rendered characters,
and runs for 3 fraction applications before the interpreter observes the
halt. The required interpreter fuel is 4 because observing that no fraction
applies costs one more unit.

The focused build succeeds with warnings absent:

```text
$ lake build Langlib.Tests.URMFractran
✔ [1050/1050] Built Langlib.Tests.URMFractran (880ms)
Build completed successfully (1050 jobs).
```

The scratch suite imports `Langlib.Tests.URMFractran` and calls
`Langlib.Common.runSuites`. Its result is:

```text
── urm -> fractran (runnable compiler scaffold) (10 tests)
  ok   empty program preserves register 0
  ok   constant built by increments
  ok   zero clears the answer register
  ok   transfer copies into the answer register
  ok   self-transfer is a no-op
  ok   taken jump skips increments
  ok   untaken jump, left register larger
  ok   untaken jump, right register larger
  ok   jump past the end halts
  ok   addition loop uses a backward unconditional jump
── urm -> fractran (measured cost) (1 tests)
  ok   two increments
all 11 tests passed
```

The suite includes a constant, zeroing, transfer, forward equality jumps,
both unequal cases, a jump past the program, and an addition loop with a
backward unconditional jump. These tests compare the decoded FRACTRAN answer
with LangLib's executable URM interpreter.
