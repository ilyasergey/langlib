# A finite-state restriction of Befunge-93

This result concerns `BoundedByteBefunge93`, a restricted language defined
in `Langlib/Computability/Befunge93.lean`. It does not classify either the
reference `bef.c` machine or LangLib's main Befunge-93 semantics.

## Three different machines

The name Befunge-93 is used for machines with materially different storage
models.

The reference interpreter `bef.c` has a fixed 80 by 25 byte playfield and
a stack of fixed-width `signed long` values. Its stack depth is unbounded.
Its configurations therefore do not form a finite set. The usual
classification treats it as finite control with one finite-alphabet stack,
which is a pushdown system. The pushdown argument is a cited classical
result and is not formalized here. In particular, LangLib's
`BoundedStorage` interface cannot express this argument because that
interface requires a finite configuration space.

LangLib's executable semantics uses unbounded `Int` values in both the
playfield and stack. The playfield then acts as 2000 unbounded registers.
This file proves no computational-class theorem about that semantics.

The proved model has the distinct name `BoundedByteBefunge93`. It has:

* the ordinary 80 by 25 toroidal playfield and loader size checks;
* byte-valued playfield cells and byte-valued stack entries;
* a fixed stack capacity of 16 entries;
* modulo-256 arithmetic;
* no input or output commands;
* no random-direction command;
* a runtime error on stack overflow, division by zero, modulo by zero, an
  I/O command, `?`, or any other unsupported instruction.

The deterministic core still includes directions, horizontal and vertical
conditionals, string mode, ordinary stack operations, bridge, `g`, `p`, and
self-modification. Input passed through `ProgLang.run` is ignored.

## Finite configuration proof

`BoundedByteBefunge93.State` contains the complete state that can affect a
future transition: the 2000 byte cells, the bounded stack backing store and
depth, the two coordinates, four-way direction, string-mode bit, and one of
three statuses. Output is absent because this restricted language has no
output command.

The mathematical state count corresponds to

```text
256^2000 * 80 * 25 * 4 * 256^16 * 17 * 2 * 3
```

The Lean witness uses `Fintype.card State` directly. Its index is the
standard equivalence from a finite type to `Fin (Fintype.card State)`, so
the index is globally bounded and injective for every `State`. This detail
matters because `BoundedStorage.Config` is fixed for the whole language and
`index_inj` ranges over every value of that type.

The operational configuration after `n` steps is `exec n initialState`.
The theorem `exec_succ` shows that one more unit of fuel applies `step` to
the current configuration. Equal configurations therefore have equal
successors. The run result's halting flag is determined by the status field,
so equal configurations also agree on halting.

These facts produce the declarations:

```lean
noncomputable def boundedStorage : BoundedStorage BoundedByteBefunge93
```

```lean
noncomputable def haltingDecidable (p : Program) (input : Input) :
    Decidable (∃ fuel, (evalProg p input fuel).isHalted = true)
```

The second declaration is an instance of the general finite-state search
theorem in `Langlib.Computability.BoundedStorage`. Its bound is enormous,
so it is a decidability proof rather than a practical model checker.

## Scope of the result

Lean proves finite-state halting decidability only for
`BoundedByteBefunge93`. There is no `BoundedStorage` declaration for
`Langlib.Befunge93`, no such declaration for `bef.c`, and no
`TuringComplete` declaration in this file.

For `bef.c`, unbounded stack depth blocks this finite-state proof even
though the stack alphabet is finite. A separate formalization of pushdown
reachability would be needed to obtain a machine-checked halting result for
that model. For LangLib's unbounded-`Int` semantics, a completeness proof
would require a compiler and simulation theorem and remains open here.

## Verification

The focused targets build successfully. Expect the final line below.

```
lake build Langlib.Computability.Befunge93 Langlib.Tests.BoundedBefunge93
```

Output:

```text
Build completed successfully (788 jobs).
```

The scratch runner checks 19 operational cases, including the exact stack
limit, torus movement, self-modification, rejected commands, parser bounds,
and divergence. Expect all cases to pass.

```
lake env lean --run /private/tmp/run-bounded-befunge93.lean
```

Output:

```text
── bounded byte Befunge-93 core (19 tests)
  ok   immediate halt
  ok   full stack can halt
  ok   seventeenth push overflows the fixed stack
  ok   empty pop yields zero
  ok   string mode uses the bounded byte stack
  ok   zero horizontal branch moves right
  ok   left movement wraps around the torus
  ok   bridge skips one cell
  ok   self modification writes a byte cell
  ok   put then get stays inside byte storage
  ok   division by zero is an error
  ok   modulo by zero is an error
  ok   output is outside the no-I/O fragment
  ok   input is outside the no-input fragment
  ok   random direction is outside the deterministic fragment
  ok   unsupported instruction is an error
  ok   two-cell horizontal loop diverges
  ok   ordinary loader still enforces width 80
  ok   ordinary loader still enforces height 25
all 19 tests passed
```

The focused axiom audit reports only Lean's standard logical axioms. Expect
the following three lines.

```
lake env lean /private/tmp/audit-bounded-befunge93.lean
```

Output:

```text
'Langlib.Computability.BoundedByteBefunge93.exec_succ' depends on axioms: [propext, Quot.sound]
'Langlib.Computability.BoundedByteBefunge93.boundedStorage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlib.Computability.BoundedByteBefunge93.haltingDecidable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The repository-wide `scripts/axioms.lean` also contains these audit lines.
At the time this result was checked, that combined script was temporarily
blocked by a missing object file from concurrent work on the URM compiler.
The focused audit above imports only this module and verifies its complete
axiom dependencies.
