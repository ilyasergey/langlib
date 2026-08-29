# Verified URM compilation to FRACTRAN

LangLib proves FRACTRAN Turing complete through a total compiler from
cslib's unlimited register machine:

```lean
def fractranComplete : TuringComplete FractranLang
```

The witness contains a runnable fraction-list compiler, an input-dependent
positive starting integer, an output decoder, and a proof through the real
fuel-based FRACTRAN interpreter.

## Prime-exponent representation

`URMFractran.primeAt` is an executable sequence of distinct primes beginning
with 2. A finite token store `Nat →₀ Nat` is encoded by

```text
∏ i, primeAt(i) ^ tokens(i).
```

Register `r` is stored as the exponent of `primeAt r`; register 0 is thus the
exponent of 2. Later prime indices are reserved for program-counter phases,
two scratch counters, and cleanup phases.

The arithmetic layer proves that prime factorization recovers every token,
that the encoding is injective, and that divisibility is componentwise token
inclusion:

```lean
theorem factorization_encodeTokens (s : Tokens) (i : Nat) :
    (encodeTokens s).factorization (primeAt i) = s i

theorem encodeTokens_dvd_iff {a b : Tokens} :
    encodeTokens a ∣ encodeTokens b ↔ a ≤ b
```

It also proves that an enabled syntactic rule performs exactly one concrete
`Langlib.Fractran.step`. Disabled rules are skipped, which connects the
ordered token semantics directly to FRACTRAN's first-match interpreter.

## Instruction compiler

Every reachable micro-state has one active control token. Every generated
instruction rule consumes a control token owned by its program counter and
phase. Rules from earlier blocks are therefore disabled when another block
is active.

- `Z r` alternates two phases while consuming all factors of register `r`.
- `S r` changes the control phase and adds one register factor.
- `T m r` clears `r`, copies `m` into `r` and a scratch counter, then restores
  `m` from the scratch counter.
- `J m r q` removes paired factors into two scratch counters. Ordered rules
  distinguish the equal case from either unequal direction, then restore
  both source registers before taking the selected control target.

The jump proof covers equal registers, left-larger and right-larger
registers, forward targets, backward targets, and targets beyond the program
length. Self-jumps use a private phase instead of a fraction that reduces to
`1/1`.

The local instruction results are lifted to cslib's transition relations:

```lean
theorem urmStep_compileRules ...
    (hstep : Cslib.URM.Step P s t) :
    RulesSteps (compileRules P inputs)
      (boundaryTokens (layout P inputs) s.pc s.regs)
      (boundaryTokens (layout P inputs) t.pc t.regs)

theorem urmSteps_compileRules ...
    (hsteps : Cslib.URM.Steps P s t) : ...
```

## Cleanup and output

At a halted program counter, the active marker is the halt token. Cleanup
removes registers 1 through the finite register bound, preserves register 0,
and consumes its last control token. `cleanupSteps_compileRules` proves this
trace under the first-match semantics of the entire compiled list, including
all preceding instruction blocks. Its exact target is

```lean
Finsupp.single 0 (regs 0)
```

whose prime encoding is `2 ^ regs 0`.

The `FractranLang` runner uses the existing interpreter's `final` output
mode. Once cleanup reaches `2 ^ R₀`, no compiled fraction applies because
every denominator consumes a control prime. The interpreter halts and emits
the decimal line for `2 ^ R₀`. `URMFractran.decodeOutput` parses that exact
line and applies `Fractran.pow2?`, yielding `R₀`. The proof includes the
round trip:

```lean
theorem decodeOutput_encode (n : Nat) :
    decodeOutput ((toString (2 ^ n) ++ "\n").toUTF8) = some n
```

`encodeInput_eq_encodeTokens_boundary` proves that the compiler's starting
integer is exactly the prime encoding of `Cslib.URM.State.init inputs`, for
empty and nonempty programs.

## End-to-end theorem

`simulationRules` composes all URM steps with cleanup. `simulationConcrete`
turns the token trace into concrete fraction steps. `exec_final_of_steps`
constructs sufficient interpreter fuel, including the final no-rule check.
The resulting theorem is:

```lean
theorem simulation (P : Program) (inputs : List Nat) (result : Nat)
    (h : Cslib.URM.HaltsWithResult P inputs result) :
    ∃ fuel,
      (Fractran.evalProg { out := .final }
        (compileProgram P inputs).code
        (compileProgram P inputs).start fuel).exit = Exit.halted ∧
      decodeOutput
        (Fractran.evalProg { out := .final }
          (compileProgram P inputs).code
          (compileProgram P inputs).start fuel).output = some result
```

As with the shared `TuringComplete` interface, this is the defined, halting
direction. It does not claim that a divergent URM program produces a
divergent FRACTRAN run.

## Differential tests and measured cost

`Langlib/Tests/URMFractran.lean` compares the compiled artifact with the
executable URM reference on constants, zeroing, transfer, self-transfer,
equal and unequal jumps, a jump beyond the program, and an addition loop
with a backward unconditional jump.

The measured two-increment example compiles to 3 fractions and 18 rendered
characters. It performs 3 fraction applications. The interpreter requires
one additional fuel unit to observe that no fraction applies.

Focused verification:

```text
lake build Langlib.Tests.URMFractran
✔ [1050/1050] Built Langlib.Tests.URMFractran
Build completed successfully (1050 jobs).
```

The dedicated suite reports:

```text
── urm -> fractran (verified compiler) (10 tests)
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

The standalone audit command is:

```text
lake env lean scripts/axioms.lean
```

The FRACTRAN simulation and `fractranComplete` report only Lean's standard
logical axioms, with no `sorryAx` or project-specific axioms.
