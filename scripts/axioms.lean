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

#print axioms derived
#print axioms derivedWhitespace
#print axioms derivedSubleq
#print axioms agree

-- Brainfuck: Turing complete via paired unary tape columns. The compiler
-- embeds inputs, simulates a structured counter dispatcher, and encodes the
-- answer as the number of output bytes.
#print axioms brainfuckComplete
#print axioms URMBrainfuck.simulation
#print axioms URMBrainfuck.compile
