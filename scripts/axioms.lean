/-
Axiom audit for LangLib's computability results.

A theorem resting on `sorryAx` type-checks perfectly well and looks exactly
like a real one, so `lake build` succeeding is not evidence that a proof is
honest. This file prints the axiom dependencies of every completeness
result in the library.

Run it:

    lake env lean scripts/axioms.lean

Expected output, for every declaration listed: only the three standard
axioms of Lean's logic,

    [propext, Classical.choice, Quot.sound]

Anything else, and in particular `sorryAx`, means the result is not what it
claims to be. Add a line here whenever a new completeness or
incompleteness instance lands.
-/
import Langlib.Computability.Whitespace
import Langlib.Computability.Subleq
import Langlib.Computability.Derived
import Langlib.Computability.Brainfuck
import Langlib.Computability.Deadfish
import Langlib.Computability.Malbolge
import Langlib.Computability.Befunge93

open Langlib.Computability

-- Whitespace: Turing complete, via cslib's unlimited register machine.
-- The bridge to cslib's vocabulary: a Turing-complete language computes
-- every URM-computable partial function, wherever it is defined.
#print axioms computes_of_turingComplete
#print axioms BoundedStorage.halts_iff_search
#print axioms BoundedStorage.halting_decidable

#print axioms whitespaceComplete
#print axioms URMWhitespace.simulation
#print axioms URMWhitespace.compile

-- Subleq: Turing complete. Registers are single unbounded signed cells, the
-- answer leaves the machine in unary, and the compiled program halts by
-- jumping to a negative address.
#print axioms subleqComplete
#print axioms URMSubleq.simulation
#print axioms URMSubleq.compile

-- The certified compilation pipeline: Turpentine to the unlimited register
-- machine, and the composition with any completeness witness.
#print axioms Langlib.Turpentine.Compile.URM.compileToURM_correct
#print axioms Langlib.Turpentine.Compile.URM.reaches_compileStmt
#print axioms Langlib.Turpentine.Compile.URM.reaches_compileExpr
#print axioms Langlib.Turpentine.Compile.URM.compileToURM

-- The pieces the widened fragment rests on: initialisers (the declarations
-- run as a prelude, and the lemma saying evaluation ignores names it does
-- not read), `&&` and `||` (the emitted code evaluates the right operand
-- even where the source short-circuits), and `/` and `%`.
#print axioms Langlib.Turpentine.Compile.URM.exec_declPrelude
#print axioms Langlib.Turpentine.Compile.URM.evalExpr_mono
#print axioms Langlib.Turpentine.Compile.URM.reaches_compileExpr_total
#print axioms Langlib.Turpentine.Compile.URM.reaches_andCode
#print axioms Langlib.Turpentine.Compile.URM.reaches_orCode
#print axioms Langlib.Turpentine.Compile.URM.reaches_divModCode
#print axioms Langlib.Turpentine.Compile.URM.binCode_correct

#print axioms derived
#print axioms derivedWhitespace
#print axioms derivedSubleq
#print axioms derivedBrainfuck
#print axioms agree

-- Brainfuck: Turing complete via paired unary tape columns. The compiler
-- embeds inputs, simulates a structured counter dispatcher, and encodes the
-- answer as the number of output bytes.
#print axioms brainfuckComplete
#print axioms URMBrainfuck.simulation
#print axioms URMBrainfuck.compile

-- Deadfish: exact straight-line termination and direct decidable halting.
-- The fixed-Config BoundedStorage interface cannot represent its arbitrarily
-- long program-dependent executions; no such witness exists.
#print axioms Deadfish.exec_exit_eq_halted_iff
#print axioms Deadfish.evalProg_exit_eq_halted_iff
#print axioms Deadfish.isHalted_eq_true_iff
#print axioms Deadfish.halts
#print axioms Deadfish.haltingDecidable
#print axioms Deadfish.no_boundedStorage

-- Malbolge: exact finite-control cardinality for each fixed input length.
-- The current BoundedStorage interface cannot package the input-dependent
-- cursor type, so this audit covers the proved finite-core fallback only.
#print axioms malbolgeCore_card
#print axioms malbolgeControlBound_eq
#print axioms malbolgeControlIndex_lt
#print axioms malbolgeControlIndex_inj
#print axioms malbolgeControl_ignores_output
#print axioms malbolgeInitialState_wellFormed
#print axioms malbolgeStateControl_index_lt

-- Bounded byte Befunge-93 core: the playfield and stack alphabet are bytes,
-- stack depth is fixed at 16, and input, output, and random direction are
-- excluded. These claims do not apply to bef.c or LangLib's Int semantics.
#print axioms BoundedByteBefunge93.exec_succ
#print axioms BoundedByteBefunge93.boundedStorage
#print axioms BoundedByteBefunge93.haltingDecidable

-- Piet: axiom-clean stack and colour-transition foundations for the partial
-- straight-corridor compiler. Arbitrary J routing and pietComplete remain open.
#print axioms URMPiet.push_uses_source_block_size
#print axioms URMPiet.runCode_rollNat_prefix
#print axioms URMPiet.runCode_storeTop
#print axioms URMPiet.runCode_copyAt
#print axioms URMPiet.runCode_Z
#print axioms URMPiet.runCode_S
#print axioms URMPiet.runCode_T
#print axioms URMPiet.opFor_advance
#print axioms URMPiet.compileStraight
#print axioms URMPiet.advance_ne
