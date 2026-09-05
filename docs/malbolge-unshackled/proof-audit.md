# Malbolge Unshackled: proof audit and revised construction

Audit date: 2026-09-05. **LangLib has no completed Lean proof of MU's Turing
completeness.** The existing local theorems are useful, but the proposed
unary-tape simulation cannot be initialized with the loader's memory fill.
The recommendation is to retain the counter-machine front end and replace
the target representation with **finitely many cells holding unbounded
natural numbers**, using runtime rotation loops for arithmetic.

The new kernel-checked results are in
[`Obstructions.lean`](../../Langlib/Computability/MalbolgeUnshackled/Obstructions.lean).
This page supersedes the construction recommendations in the earlier
[technical account](../computability-malbolge-unshackled.md) and
[compiler notebook](compiler.md). It distinguishes a proposed construction
from the operational theorems still needed to establish it.

The implementation following this audit is described in
[runtime-proof.md](runtime-proof.md): fixed-cell representation, reusable
working calls, a repeating rotation loop, marker algebra, reusable width
growth, code-initialization writes, and a 34-step marker reset with preserved
constants are now checked. Arithmetic, runtime scan exit, integration of
rotation/reset/growth for overflow retry, general source
initialization, and the completeness witness remain open.

## What the current proof actually establishes

The shared interface is
[`TuringComplete`](../../Langlib/Common/Computability.lean): a total,
runnable compiler, input encoder, output decoder, and a theorem preserving
halting answers. The interpreter must be lawful with respect to fuel. MU
already has the language and lawfulness instances. The target-independent
[`Counter`](../../Langlib/Computability/Counter.lean) development already
translates URM programs and their finite inputs into `inc`, nonzero `dec`,
`emit`, and structured `loop`, with `counterProgram_spec` proving the
translation. This part should be reused.

The MU development proves address and value algebra, single-step rules
connected to `exec`, finite sequences under memory hypotheses, and an
invariant for a particular nonterminating cycle. Its `sim_inc` and `sim_dec`
describe mathematical memory updates. They do **not** show that MU
execution performs those updates. Likewise, `walk_iterate` composes passes
*assuming each pass exists*. There is no instruction sequence implementing
an arbitrary counter command, and no total runtime compiler for these
commands. The Turpentine backend evaluates its supported source with a fuel
bound at compile time and emits its output; it supplies no universality
argument.

## Obstructions and overstatements

### The infinite blank tail is impossible with the canonical kind of fill

`RegMem DB SI R f m` requires both cells of every register's tape pair to
be blank beyond their finite lengths. In particular, it requires infinitely
many **adjacent pairs** of natural addresses to contain `Value.zero`.

`finite_natural_support` proves that every `Memory` has a bound above
which its finite hash map contains no natural addresses.
`restTable_adjacent_nonzero_lead` proves that, for fill seeds with leading
trit zero, at least one of every two adjacent natural addresses has a
nonzero leading trit. Consequently:

```lean
theorem not_regMem_of_natural_fill
    (hp : p.lead = .t0) (hq : q.lead = .t0)
    (hrest : m.rest = restTable p q phase)
    (hR : 0 < R) (hSI : 0 < SI) (f : RegFile) :
    ¬ RegMem DB SI R f m
```

This is stronger than the earlier experiment over printable seeds: it
covers all natural seeds and every positive stride. It applies to every
finite map of overrides, so writing a finite prefix cannot repair the
invariant. Execution's memory writes preserve `rest` by definition.
The theorem assumes the displayed fill equation; connecting that equation
to all outputs of the mutable `loadWith` loop is still unproved.

A tape-based design could instead track an allocated finite prefix, its
frontier, and the untouched periodic tail, or use the fill as the blank
encoding. Neither repair implements an allocator. The two-step crazy
identity does not do that: it computes a value into its operand cells and
assumes the needed constants are already accessible. It does not establish
an in-place write to an arbitrary virgin cell or regenerate those constants.

### Restoring instructions does not restore their operands

`two_sweep` encrypts code twice. With two-cycle words, that restores the
code. Its second sweep consists of no-ops, so it does not undo the first
sweep's writes to data. Its conclusion does not give a reusable calling
convention for the whole gadget.

For a concrete counterexample, a marked branch changes its two operands
from `cellOne, digitAt .t2 j` to `cellMark, digitAt .t1 j`. The new theorem
`flag_branch_mark_reuse` proves that feeding another mark through those
changed operands yields **zero**, whereas the intended target is `3 ^ j`.
Re-entry must restore operands, scratch values, return flags, and code
phases, or explicitly describe how the next call accepts their new states.

### Straight-line arithmetic is not automatically a reusable layout

`flagAddr_gadget` assumes two consecutive crazy instructions. In the
`70 ↔ 74` orbit, those instructions are available only at residues 86 and
82 modulo 94. `no_adjacent_two_cycle_crazy` proves that two adjacent cells
cannot both satisfy these requirements. The gadget is a valid single-use
lemma; it cannot simply be instantiated as a row of period-two cells.
Separate working cells joined by stable jumps remain a possible repair,
with a new layout and operand schedule to prove.

There is also a pointer obligation. After the three instructions in
`flagAddr_gadget`, `d = d₀ + 1`. A subsequent jump reads the selected
address there and finishes with `c = flagAddr j flag + 1` and
`d = d₀ + 2`. Thus the two entry addresses are `3^j + 1` and
`2*3^j + 1`, with printable landing words at their predecessors.
The third operand must contain `Value.ofNat d₀`: for slot-dependent
`d₀`, that is an unbounded **stored pointer** to manufacture. Counting
instructions alone does not establish the walk's claimed slot stride.
The alternative branch through absolute addresses 0 and 1 needs its own
way to recover the walk cursor.

### A value-width bound is not a storage bound

`WidthBounded W s` constrains the accumulator and memory **contents**. It
does not constrain `c`, `d`, or the number of cells visited or written.
`widthBounded_update_d` makes this separation explicit. A finite alphabet
does not imply a finite tape; the tape alphabet of a Turing machine is
finite too. The proved result bounds stored jump targets in a rotation-free
run, but successor still advances pointers.

Accordingly, `widthBounded_step1` alone proves neither that rotation is
mandatory for universality nor that rotation-free MU has bounded storage.
No such negative result is asserted here. Rotation **is** needed for the
proposed fixed-cell natural-counter representation: finitely many bounded
width values cannot represent its arbitrarily large counters.

Similarly, `restTable_not_printable` rules out uninterrupted execution
through untouched fill. It does not rule out writing new code outside the
original image, or jumping over bad cells. `rotr_forces_halt` identifies a
halt opcode 42 addresses later; it does not prove that execution reaches it.

### An arbitrary image need not be a source program

`ProgLang.Prog MalbolgeUnshackledLang` is `Image`, whose fields allow an
arbitrary periodic background. Choosing a zero background can make the old
tape invariant satisfiable, but that choice is not justified by the loader.
The generic `TuringComplete` interface does not demand a parse round trip.

For a claim about MU source programs, the construction must additionally
provide source text accepted by `load`, and an initialization theorem
reaching the runtime invariant. Merely constructing an `Image` with useful
non-natural initial constants, or assuming an initialized `State`, leaves
this obligation open. A noncomputable compiler choosing answers is also
excluded by the project's existing runnable-witness convention.

## A concrete reference predating MalbolgeLisp

Matthias Lutter published a
[Brainfuck interpreter in MU](https://lutter.cc/unshackled/brainfuck.html)
with [HeLL source](https://lutter.cc/unshackled/brainfuck.hell), whose header
dates it to **2016**. Its specified dialect has unbounded integer cells and
an unbounded tape. This is earlier constructive evidence than the 2020
MalbolgeLisp project; the earlier documentation's chronology was incorrect.

The source is organized into instruction dispatch, memory access, arithmetic,
and a loop over the current rotation width. Its increment routine reports
carry; a caller retains the original value, grows the width on overflow,
and retries. It also supplies decrement with borrow and a width-growth
routine with a return path. These are the mechanisms the present proof is
missing. This inspection identifies a construction to formalize; it is not
a proof that the published program is correct for every execution.

[LMFAO](https://lutter.cc/unshackled/assembler.html) assembles that source.
Its README explains instruction-cycle constraints and how restoration
entries work; its initializer generates the desired runtime memory.
Neither its layout search nor its generated initializer is a Lean theorem.
Both the interpreter source and assembler are GPLv3. They were inspected
as references; no source from either is copied into this contribution.

The inspected downloads can be identified independently of later edits:

| Download | SHA-256 |
|---|---|
| `brainfuck.hell` | `691643df522485d26565bc7e313dd25876f93cd59e19b98605594f59b93d985a` |
| `lmfao-0.1.5.tar.gz` | `59ca911fb62a6adf47ebca19282accd5f685470dc41d7c39f6c31b4857d48f42` |

The [canonical Haskell interpreter](http://oerjan.nvg.org/esoteric/Unshackled.hs)
was also inspected: rotation uses the current width; only `MovD` can trigger
growth when the destination exceeds `maxWidth`. LangLib's instance fixes
the minimum deterministic policy. Proving portability to every allowed
growth policy is a separate strengthening.

## Recommended construction: fixed cells, unbounded counters

Compile the finite `Counter.Code` into finite control blocks. Allocate one
fixed cell per counter, plus finite scratch, constants, and return flags.
At command boundaries, a counter cell holds `Value.ofNat (σ.regs r)`.
Unlike an infinite blank tail, this invariant only demands initialization
of finitely many cells. The *contents* grow without bound at runtime.

The runtime invariant should include:

* the register equations and `n < 3 ^ w` for each stored counter;
* the current rotation width `w`, the maximum destination width, and enough
  headroom for every ordinary control/data address;
* the control entry, data pointer, scratch-cell invariants, and instruction
  and return-flag phases needed to call the next routine;
* separation of counters, code, constants, and growth-return cells;
* the actual periodic fill, unchanged input, the output count, and an open
  output stream.

The decisive routines and their specifications are as follows. All are
**remaining operational obligations**, not assumed axioms or completed
lemmas.

| Routine | Required effect and termination argument |
|---|---|
| Read/reset/write | Copy an unknown counter into scratch and commit it back; preserve the other counters and restore the calling convention. |
| Width scan | Traverse exactly the current `w` trit positions, with a rotating marker; return values to their original orientation. Keep `w` fixed during the scan by bounding all ordinary `MovD` destinations. |
| Increment at width `w` | On scratch `n < 3^w`, return `(n+1) mod 3^w` and carry iff `n+1 = 3^w`. Prove the per-trit carry table and induct over the scan. |
| Decrement at width `w` | Return the modular predecessor and borrow iff `n=0`, with the corresponding borrow invariant. |
| Grow and return | Terminate at the continuation with a strictly larger legal width, original counters unchanged, and ordinary routines callable again. Check the distant destination's fill and the entire return path. |
| Zero test | Decrement a scratch copy; borrow distinguishes zero. Discard scratch so the stored counter is unchanged. |
| Emit | Load 42 and output one `*`; restore the runtime invariant. Existing `step1_out` and byte-count lemmas handle the observable result. |

For increment, keep the source counter unchanged until success. On carry,
grow the width and retry from that source. If `n+1 = 3^w` and growth gives
`w' > w`, then `n+1 < 3^w'`, so the retry fits. This gives a finite
termination argument without a compiler-supplied bound on counter values.
Regenerate width-dependent scratch masks after growth; masks prepared for
the old width cannot simply be reused. The counter semantics only permits
decrement of a nonzero register.

`rot_one` and `growRotWidth_double` are arithmetic ingredients for growth,
but **they are not a grow-and-return routine**. A remote `MovD` must get
back to fixed code, and ordinary calls must not unexpectedly grow the width
mid-scan. Lutter's source provides a concrete design to study for both.
This is the first substantial milestone, alongside a reusable width scan;
another generic induction assuming a scan would not establish it.

Once these routines exist, compile structured loops with static entry and
continuation labels. Give every call site sufficient return-flag machinery
and verify its phases. Prove a finite `run?` segment per counter command,
then compose by induction over `Counter.Ev` (or `EvN` when splitting the
loop premise is convenient). No source execution takes place in `compile`.
Finally connect the initializer, the counter simulation, and a halt cell
using `exec_halts_of_run?` and `counterProgram_spec`; use empty runtime
input and `some output.size` as the decoder.

The assembler must be a total function with a proved layout scheme, or use
checked certificates with a total method of producing them for compiled
programs. Successful external assembly of examples is not a proof that
arbitrarily large generated control graphs can be laid out. Initialize only
the finite required cells, respecting the loader's opcode and character
constraints. Keep the source-realization theorem alongside the witness.

## Alternative: verify the published Brainfuck interpreter

A second route is to verify Lutter's fixed interpreter, its initializer,
and the Brainfuck dialect it implements. Feed it a serialized compilation
of the URM through the existing counter-to-Brainfuck construction, followed
by the `!` delimiter, and prove its halt sentinel and output count.

This requires a dialect bridge: LangLib's Brainfuck uses bytes, whereas
Lutter's dialect uses unbounded signed integers and Unicode I/O. The
existing unary-column construction is a good candidate, but its full runs
must be shown not to rely on byte wraparound, negative cells, left-boundary
behavior, or incompatible output. Names alone do not give that simulation.
Also, the generic `encodeInput` field cannot depend on the URM program: a
fixed interpreter with the compiled program in its input needs that stream
injected by a generated MU wrapper, or the Brainfuck code initialized in
memory by `compile`. One cannot silently give `encodeInput` an extra
program argument. The fixed-counter route avoids both this dialect bridge
and the interpreter's dynamic instruction and data tape allocator.

## Validation and next acceptance criterion

The new obstruction results are compiled by `lake build` and listed in
[`scripts/axioms.lean`](../../scripts/axioms.lean). They use only the
standard Lean axioms; no `sorry`, user axiom, or native evaluation shortcut
is used. They do not establish that MU is incomplete.

The next runtime milestone should be a **loadable counter program that
increments through a width boundary, grows, returns, and continues**, with
a symbolic correctness theorem parameterized by the initial counter and
width. Test repeat calls and both branch outcomes, and check against
LangLib's interpreter. Only after that exists should the four-command
compiler and final completeness witness be described as assembly work.
