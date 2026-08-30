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
import Langlib.Languages.Subleq.Trace
import Langlib.Languages.Turpentine.Compile.Derived
import Langlib.Languages.Turpentine.Trace
import Langlib.Languages.Turpentine.Certified.BespokeWhitespace
import Langlib.Computability.Brainfuck
import Langlib.Computability.Deadfish
import Langlib.Computability.Malbolge
import Langlib.Computability.Befunge93
import Langlib.Computability.Thue
import Langlib.Computability.Ook
import Langlib.Computability.Brainloller
import Langlib.Computability.Piet
import Langlib.Computability.Fractran
import Langlib.Languages.Turpentine.Certified.BespokeSubleq
import Langlib.Computability.MalbolgeUnshackled
import Langlib.Computability.Unlambda
import Langlib.Computability.Ski

open Langlib.Common
open Langlib.Computability
open Langlib.Turpentine.Certified
open Langlib.Turpentine.Compile

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
#print axioms derivedFractran
#print axioms derivedThue
#print axioms derivedPiet
#print axioms derivedOok
#print axioms derivedBrainloller
#print axioms derivedUnlambda
#print axioms derivedSki
#print axioms agree
#print axioms Langlib.Common.CertifiedCompiler.agree

-- Certified compilation, generically: the answer-only notion, the I/O-aware
-- notion, and the proof that the second implies the first.
#print axioms Langlib.Common.IOCertifiedCompiler.toCertified
#print axioms Langlib.Common.IOCertifiedCompiler.toCertifiedOf
#print axioms Langlib.Common.IOCertifiedCompiler.output_eq
#print axioms Langlib.Common.IOCertifiedCompiler.agree
#print axioms Langlib.Common.TraceLang.ofInputFree

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

-- Malbolge: exact finite-control cardinality for each fixed input length,
-- and the halting decision that now rests on it. The witness is a
-- `BoundedRun` rather than a `BoundedStorage`, because a faithful input
-- cursor's range depends on the input, so the configuration type is not
-- globally finite; `BoundedRun` asks for finiteness along a run, which is
-- all the pigeonhole argument uses.
#print axioms malbolgeCore_card
#print axioms malbolgeControlBound_eq
#print axioms malbolgeControlIndex_lt
#print axioms malbolgeControlIndex_inj
#print axioms malbolgeControl_ignores_output
#print axioms malbolgeInitialState_wellFormed
#print axioms malbolgeStateControl_index_lt

-- The dynamic half: one iteration as a function, the successor law the
-- reference loop does not give directly, the run invariant, and the
-- configuration injectivity the pigeonhole needs.
#print axioms Langlib.Computability.exec_one
#print axioms Langlib.Computability.exec_succ
#print axioms Langlib.Computability.runWF_exec
#print axioms Langlib.Computability.stepOnce_congr
#print axioms Langlib.Computability.config_ext
#print axioms Langlib.Computability.malbolgeBoundedRun
#print axioms Langlib.Computability.malbolgeHaltingDecidable

-- The weakened interface the Malbolge witness needs, and the fact that the
-- globally finite one still implies it.
#print axioms BoundedRun.halts_iff_search
#print axioms BoundedRun.halting_decidable
#print axioms BoundedStorage.toBoundedRun

-- Bounded byte Befunge-93 core: the playfield and stack alphabet are bytes,
-- stack depth is fixed at 16, and input, output, and random direction are
-- excluded. These claims do not apply to bef.c or LangLib's Int semantics.
#print axioms BoundedByteBefunge93.exec_succ
#print axioms BoundedByteBefunge93.boundedStorage
#print axioms BoundedByteBefunge93.haltingDecidable

-- Thue: executable URM generator and proved local obligations.  The
-- counter-macro arithmetic, unique-marker encoding, and final-state decoder
-- are proved.  The rewrite-level simulation remains open, so there is no
-- thueComplete declaration to audit.
#print axioms URMThue.control_token_injective
#print axioms URMThue.encodeState_marker_count
#print axioms URMThue.RuleAnchored
#print axioms URMThue.headRules_anchored
#print axioms URMThue.nextPC_mem_outcomes
#print axioms URMThue.instruction_macro_correct
#print axioms URMThue.macroCode_correct
#print axioms URMThue.initial_macro_invariant
#print axioms URMThue.decodeOutput_encodeState

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

-- FRACTRAN: axiom-clean prime-exponent arithmetic and the runnable
-- URM-to-FRACTRAN compiler. The whole-program simulation remains open.
#print axioms URMFractran.encodeTokens_injective
#print axioms URMFractran.factorization_encodeTokens
#print axioms URMFractran.encodeTokens_dvd_iff
#print axioms URMFractran.rule_den_dvd_iff
#print axioms URMFractran.encodeTokens_apply
#print axioms URMFractran.step_single_rule
#print axioms URMFractran.step_single_rule_disabled
#print axioms URMFractran.tokenProduct_coprime
#print axioms URMFractran.frac_eq_of_disjoint
#print axioms URMFractran.registerBound_pos
#print axioms URMFractran.encodeInput_pos

-- The hand-written Turpentine-to-subleq backend, verified on the fragment
-- `var answer : int := k; printByte(answer);` (1 <= k <= 255) and
-- `var answer : int;` with an empty body.  `bespokeSubleq` is the second
-- inhabitant of `TurpentineCompiler SubleqLang`; `bespokeSubleq_agrees_derived`
-- is `agree` instantiated at it and the derived compiler.
#print axioms BespokeSubleq.stepSub
#print axioms BespokeSubleq.stepOut
#print axioms BespokeSubleq.eval_of_reaches
#print axioms BespokeSubleq.reaches_print
#print axioms BespokeSubleq.reaches_skip
#print axioms BespokeSubleq.run_print
#print axioms BespokeSubleq.run_skip
#print axioms BespokeSubleq.progOf_shapeOf
#print axioms BespokeSubleq.printLit_range
#print axioms BespokeSubleq.haltsWith_progSkip
#print axioms BespokeSubleq.haltsWith_progPrint
#print axioms BespokeSubleq.decodeOutput_empty
#print axioms BespokeSubleq.decodeOutput_push
#print axioms BespokeSubleq.km_ne
#print axioms BespokeSubleq.backend_skipZero
#print axioms BespokeSubleq.backend_printLit
#print axioms BespokeSubleq.compile_eq
#print axioms BespokeSubleq.compile_progSkip
#print axioms BespokeSubleq.compile_progPrint
#print axioms bespokeSubleq
#print axioms bespokeSubleq_agrees_derived
#print axioms bespokeSubleq_agrees_derived_nonvacuous

-- Ook!: Turing complete, by re-labelling the brainfuck witness (the program
-- type and the evaluator are literally brainfuck's), plus the syntactic half
-- that makes it a claim about the language: parsing the rendering of any
-- program gives that program back, through the shipped `Langlib.Ook.parse`.
#print axioms ookComplete
#print axioms OokSyntax.parse_render
#print axioms parse_render_compile
#print axioms OokSyntax.tokenize_render
#print axioms OokSyntax.pairKey

-- Brainloller: Turing complete, the same way. Of the pictorial round trip
-- this proves the brainfuck parser is a left inverse of the renderer, that a
-- rendered program is all command characters (so the encoder's filter drops
-- nothing), and the composition of the two. The pixel walk itself is not
-- proved; see the header of Langlib/Computability/Brainloller.lean and the
-- `walks` suites in Langlib/Tests/CompileBrainloller.lean.
#print axioms brainlollerComplete
#print axioms BrainlollerSyntax.parse_renderBf
#print axioms BrainlollerSyntax.bfCommands_renderBf
#print axioms BrainlollerSyntax.decodeProg_of_decode
#print axioms BrainlollerSyntax.colour_roundTrip
#print axioms decode_compile

-- Arrays in the certified fragment: the slot layout past one register per
-- variable (disjoint blocks, sized by the declared type), the dispatch chain
-- that turns a computed index into static code, the element write, and the
-- inversions of the reference evaluator at `a[i]` and `len(a)`. The
-- defaults lemmas are what an array declaration rests on, since it emits no
-- code and relies on the registers already being zero.
#print axioms Langlib.Turpentine.Compile.URM.layoutFrom_spec
#print axioms Langlib.Turpentine.Compile.URM.goodSlots_of_layout
#print axioms Langlib.Turpentine.Compile.URM.reaches_dispatchT
#print axioms Langlib.Turpentine.Compile.URM.Agree.updateIndex
#print axioms Langlib.Turpentine.Compile.URM.agreeVal_write
#print axioms Langlib.Turpentine.Compile.URM.evalExpr_index_inv
#print axioms Langlib.Turpentine.Compile.URM.evalExpr_len_inv
#print axioms Langlib.Turpentine.Compile.URM.defEnv_get
#print axioms Langlib.Turpentine.Compile.URM.agreeVal_default

-- Thue: rule-family separation under the concrete substring selector, the
-- macro and dispatch simulations built on it, and the completeness witness.
#print axioms URMThue.encCode_injective
#print axioms URMThue.encPhase_injective
#print axioms URMThue.token_injective
#print axioms URMThue.firstOccurrence_token_right
#print axioms URMThue.firstOccurrence_token_left
#print axioms URMThue.applyAt_rule_right
#print axioms URMThue.applyAt_rule_left
#print axioms URMThue.generate_shaped
#print axioms URMThue.finishRules_shaped
#print axioms URMThue.compileRules_shaped
#print axioms URMThue.RuleShape.active_of_match
#print axioms URMThue.compileRules_match_active
#print axioms URMThue.compileRules_firstMatch_active
#print axioms URMThue.control_rule_mem_compileRules
#print axioms URMThue.phaseRules_active
#print axioms URMThue.generate_hasPhase
#print axioms URMThue.finishRules_hasPhase
#print axioms URMThue.compileAt_origin
#print axioms URMThue.compileRules_firstMatch_origin
#print axioms URMThue.outcomes_functional
#print axioms URMThue.reaches_inc
#print axioms URMThue.reaches_dec
#print axioms URMThue.reaches_zeroTest_zero
#print axioms URMThue.reaches_zeroTest_nonzero
#print axioms URMThue.reaches_emit
#print axioms URMThue.generate_append
#print axioms URMThue.reaches_exec
#print axioms URMThue.reaches_count
#print axioms URMThue.reaches_finish
#print axioms URMThue.firstMatch_eq_control
#print axioms URMThue.reaches_step
#print axioms URMThue.reaches_steps
#print axioms URMThue.firstMatch_control_none
#print axioms URMThue.simulation
#print axioms thueComplete

-- Piet dispatcher and singleton-block normalization. The runnable compiler
-- supports arbitrary J, while the image-level evalGrid simulation remains open.
#print axioms URMPiet.runCode_copyAt_list
#print axioms URMPiet.runCode_storeTop_list
#print axioms URMPiet.runCode_initialCode
#print axioms URMPiet.runCode_beginDispatch_list
#print axioms URMPiet.runCode_selectInstr_list
#print axioms URMPiet.runCode_guardedZ_list
#print axioms URMPiet.runCode_guardedS_list
#print axioms URMPiet.runCode_guardedT_list
#print axioms URMPiet.runCode_guardedEq_list
#print axioms URMPiet.runCode_guardedNext_list
#print axioms URMPiet.runCode_guardedJ_list
#print axioms URMPiet.runCode_endDispatch_list
#print axioms URMPiet.runCode_prepareBranch_list
#print axioms URMPiet.runCode_steerBranch_zero
#print axioms URMPiet.runCode_steerBranch_one
#print axioms URMPiet.runCode_pushNatUnit
#print axioms URMPiet.unitCode_unitize
#print axioms URMPiet.coloredRuns_length_of_unit
#print axioms URMPiet.runCode_unitize
#print axioms URMPiet.compile
#print axioms URMPiet.dispatchUpdate_step
#print axioms URMPiet.runCode_dispatcherCode
#print axioms URMPiet.coloredRuns_getElem?_unit
#print axioms URMPiet.unitCorridor_of_row
#print axioms URMPiet.loopGrid_width
#print axioms URMPiet.loopGrid_get_bottomWhite
#print axioms URMPiet.loopGrid_halt
#print axioms URMPiet.exec_toPivot
#print axioms URMPiet.exec_loop_branch
#print axioms URMPiet.exec_halt_branch
#print axioms URMPiet.reaches_iteration
#print axioms URMPiet.exec_run
#print axioms URMPiet.simulation
#print axioms pietComplete
#print axioms URMPiet.slide_left_run
#print axioms URMPiet.slide_return
#print axioms URMPiet.tryFrom_white
#print axioms URMPiet.exec_white
#print axioms URMPiet.flood_lblock
#print axioms URMPiet.localInfoAt?_lblock
#print axioms URMPiet.tryFrom_lblock

-- The first hand-written backend proved correct: Turpentine to Whitespace,
-- over the fragment `BespokeWhitespace.checkFragment` accepts (scalar
-- declarations with no initialiser, one of them `answer : int`; `skip`,
-- sequencing, well-typed assignment, `if`, `while`, `assert`, and output:
-- `print`/`println` of an int, a bool or a string literal; every operator
-- except `/` and `%`). `bespokeCompile_correct` is the answer-only
-- end-to-end theorem, `bespokeCompile_behaves` the behavioural one, and
-- `bespokeWhitespace_agrees_derived` is `agree` instantiated at the bespoke
-- and derived compilers for Whitespace.
#print axioms bespokeWhitespace
#print axioms bespokeWhitespace_agrees_derived
-- The behavioural half: the library's first `IOCertifiedCompiler`, with
-- `encodeTrace = id`, and the typing soundness the print cases needed.
#print axioms bespokeWhitespaceIO
#print axioms bespokeWhitespaceIOErased
#print axioms BespokeWhitespace.bespokeCompile_core
#print axioms BespokeWhitespace.bespokeCompile_behaves
#print axioms BespokeWhitespace.decodeAnswer_epilogue
#print axioms BespokeWhitespace.evalExpr_hasTy
#print axioms BespokeWhitespace.reaches_bytesCode
#print axioms BespokeWhitespace.bespokeCompile
#print axioms BespokeWhitespace.binOfChars_spell_toDigits
#print axioms BespokeWhitespace.labelOf_inj
#print axioms BespokeWhitespace.Emits.pure
#print axioms BespokeWhitespace.Emits.bind
#print axioms BespokeWhitespace.Emits.seq
#print axioms BespokeWhitespace.Emits.det
#print axioms BespokeWhitespace.emits_emit
#print axioms BespokeWhitespace.emits_emits
#print axioms BespokeWhitespace.emits_fresh
#print axioms BespokeWhitespace.labelsOf_append
#print axioms BespokeWhitespace.unlabel_labelOf
#print axioms BespokeWhitespace.labelIdxs_append
#print axioms BespokeWhitespace.labelIdxs_label
#print axioms BespokeWhitespace.Clean.labels_nodup
#print axioms BespokeWhitespace.Clean.mono
#print axioms BespokeWhitespace.Clean.ofNoLabels
#print axioms BespokeWhitespace.Clean.ofEq
#print axioms BespokeWhitespace.nodup_app
#print axioms BespokeWhitespace.Clean.appendUp
#print axioms BespokeWhitespace.clean_label
#print axioms BespokeWhitespace.CodeAt.get
#print axioms BespokeWhitespace.CodeAt.left
#print axioms BespokeWhitespace.CodeAt.right
#print axioms BespokeWhitespace.codeAt_of_eq
#print axioms BespokeWhitespace.LabelsOk.left
#print axioms BespokeWhitespace.LabelsOk.right
#print axioms BespokeWhitespace.labelsOk_of_eq
#print axioms BespokeWhitespace.noLabel_iff
#print axioms BespokeWhitespace.labelsOk_of_nodup
#print axioms BespokeWhitespace.reaches_dup
#print axioms BespokeWhitespace.reaches_drop
#print axioms BespokeWhitespace.reaches_mul
#print axioms BespokeWhitespace.reaches_jump
#print axioms BespokeWhitespace.reaches_jn_taken
#print axioms BespokeWhitespace.reaches_jn_untaken
#print axioms BespokeWhitespace.Agrees.update
#print axioms BespokeWhitespace.emits_addrOf
#print axioms BespokeWhitespace.emits_emitBool
#print axioms BespokeWhitespace.emits_cmpTail
#print axioms BespokeWhitespace.emitsE_intLit
#print axioms BespokeWhitespace.emitsE_boolLit
#print axioms BespokeWhitespace.emitsE_var
#print axioms BespokeWhitespace.emitsE_neg
#print axioms BespokeWhitespace.emitsE_not
#print axioms BespokeWhitespace.emitsE_arith
#print axioms BespokeWhitespace.emitsE_cmp
#print axioms BespokeWhitespace.emitsE_cmpLe
#print axioms BespokeWhitespace.emitsE_ne
#print axioms BespokeWhitespace.emitsE_and
#print axioms BespokeWhitespace.emitsE_or
#print axioms BespokeWhitespace.clean_boolTail
#print axioms BespokeWhitespace.clean_boolTail_jz
#print axioms BespokeWhitespace.clean_boolTail_jn
#print axioms BespokeWhitespace.clean_neTail
#print axioms BespokeWhitespace.mem_of_contains
#print axioms BespokeWhitespace.emitsExpr
#print axioms BespokeWhitespace.reaches_cast
#print axioms BespokeWhitespace.CodeAt.head
#print axioms BespokeWhitespace.CodeAt.right'
#print axioms BespokeWhitespace.LabelsOk.right'
#print axioms BespokeWhitespace.LabelsOk.single
#print axioms BespokeWhitespace.reaches_boolTail
#print axioms BespokeWhitespace.reaches_boolTail_jz
#print axioms BespokeWhitespace.reaches_boolTail_jn
#print axioms BespokeWhitespace.reaches_neTail
#print axioms BespokeWhitespace.exc_pure
#print axioms BespokeWhitespace.exc_throw
#print axioms BespokeWhitespace.exc_bind_ok
#print axioms BespokeWhitespace.exc_bind_err
#print axioms BespokeWhitespace.evalExpr_bin_eq
#print axioms BespokeWhitespace.evalExpr_bin_inv
#print axioms BespokeWhitespace.evalExpr_and_eq
#print axioms BespokeWhitespace.evalExpr_or_eq
#print axioms BespokeWhitespace.evalExpr_var_inv
#print axioms BespokeWhitespace.evalExpr_neg_inv
#print axioms BespokeWhitespace.evalExpr_not_inv
#print axioms BespokeWhitespace.encV_bool_eq_ite
#print axioms BespokeWhitespace.encV_bool_ne_ite
#print axioms BespokeWhitespace.encV_bool_sub_eq_zero
#print axioms BespokeWhitespace.evalBin_add_enc
#print axioms BespokeWhitespace.evalBin_sub_enc
#print axioms BespokeWhitespace.evalBin_mul_enc
#print axioms BespokeWhitespace.evalBin_lt_enc
#print axioms BespokeWhitespace.evalBin_le_enc
#print axioms BespokeWhitespace.evalBin_gt_enc
#print axioms BespokeWhitespace.evalBin_ge_enc
#print axioms BespokeWhitespace.evalBin_eq_enc
#print axioms BespokeWhitespace.evalBin_ne_enc
#print axioms BespokeWhitespace.layout_forIn
#print axioms BespokeWhitespace.compileChecked_unfold
#print axioms BespokeWhitespace.slotSize_scalar
#print axioms BespokeWhitespace.layoutGo_notMem
#print axioms BespokeWhitespace.layoutGo_ok
#print axioms BespokeWhitespace.typesGo_notMem
#print axioms BespokeWhitespace.typesGo_get
#print axioms BespokeWhitespace.zeroHeap_empty
#print axioms BespokeWhitespace.ZeroHeap.insertZero
#print axioms BespokeWhitespace.emits_declLoop
#print axioms BespokeWhitespace.initEnv_unfold
#print axioms BespokeWhitespace.initEnv_forIn
#print axioms BespokeWhitespace.allZeroEnv_empty
#print axioms BespokeWhitespace.encV_default
#print axioms BespokeWhitespace.initGo_zero
#print axioms BespokeWhitespace.agrees_of_zero
#print axioms BespokeWhitespace.boolTail_length
#print axioms BespokeWhitespace.sim_twoOps
#print axioms BespokeWhitespace.simExpr_bin
#print axioms BespokeWhitespace.simExpr
#print axioms BespokeWhitespace.emitsS_skip
#print axioms BespokeWhitespace.emitsS_seq
#print axioms BespokeWhitespace.emitsS_assign
#print axioms BespokeWhitespace.emitsS_ite
#print axioms BespokeWhitespace.emitsS_while
#print axioms BespokeWhitespace.emitsS_assert
#print axioms BespokeWhitespace.emitsStmt
#print axioms BespokeWhitespace.simStmt
#print axioms BespokeWhitespace.nodupB_spec
#print axioms BespokeWhitespace.isIntTy_eq
#print axioms BespokeWhitespace.checkFragment_ok
#print axioms BespokeWhitespace.emitsS_printAnswer
#print axioms BespokeWhitespace.compileChecked_of_gen
#print axioms BespokeWhitespace.bespokeCompile_correct

-- FRACTRAN: full URM simulation through the ordered fraction interpreter,
-- finite halt cleanup to `2 ^ R₀`, and the shared completeness witness.
#print axioms URMFractran.urmStep_compileRules
#print axioms URMFractran.urmSteps_compileRules
#print axioms URMFractran.cleanupSteps_compileRules
#print axioms URMFractran.simulationRules
#print axioms URMFractran.simulationConcrete
#print axioms URMFractran.compile_terminal_none
#print axioms URMFractran.exec_final_of_steps
#print axioms URMFractran.decodeOutput_encode
#print axioms URMFractran.simulation
#print axioms fractranComplete


-- MALBOLGE UNSHACKLED: no completeness witness yet. What is proved is the
-- ground floor a witness has to be built on: the arithmetic of natural
-- addresses, the two obstructions a compiler must get past, the fact that
-- `jmp` alone does not overwrite its own cell (which is what lets anything
-- loop), the jump-table spacing law, a program that provably never halts,
-- and the algebra of the crazy operation.
-- See docs/computability-malbolge-unshackled.md.

-- Addresses, decoding, and the step-level reading of `exec`.
#print axioms Unshackled.toNat?_ofNat
#print axioms Unshackled.modClass_ofNat
#print axioms Unshackled.succ_ofNat
#print axioms Unshackled.decode_at_ofNat
#print axioms Unshackled.exec_hang
#print axioms Unshackled.exec_halt
#print axioms Unshackled.exec_step
#print axioms Unshackled.exec_of_hang
#print axioms Unshackled.step1_sound
#print axioms Unshackled.exec_of_run?

-- The two obstructions, and the alternating cells a loop can use.
#print axioms Unshackled.opcode_ne_encrypt
#print axioms Unshackled.decode_encrypt_ne
#print axioms Unshackled.restTable_not_printable
#print axioms Unshackled.alternatingCell_spec

-- `jmp` is the only self-preserving instruction, and memory is a function.
#print axioms Unshackled.get_set_self
#print axioms Unshackled.get_set_ne
#print axioms Unshackled.exec_jmp
#print axioms Unshackled.jmp_cell_stable
#print axioms Unshackled.exec_nonjmp_encrypts_self
#print axioms Unshackled.exec_crazy
#print axioms Unshackled.crazy_consumes_operand

-- What a loadable jump table may look like.
#print axioms Unshackled.gap_of_repeated_word
#print axioms Unshackled.no_repeated_word_gap_two

-- The loop gadget, and the three-step loop that instantiates it.
#print axioms Unshackled.neverHalts_of_invariant
#print axioms Unshackled.image_neverHalts
#print axioms Unshackled.not_halts_of_invariant
#print axioms Unshackled.Loop.step_phase₀
#print axioms Unshackled.Loop.step_phase₁
#print axioms Unshackled.Loop.step_phase₂
#print axioms Unshackled.Loop.looping_step
#print axioms Unshackled.Loop.neverHalts

-- The algebra of the crazy operation: what a rot-free backend can compute.
#print axioms Unshackled.crz_trit
#print axioms Unshackled.ext_of_trits
#print axioms Unshackled.crzTrit_zero_ne_zero
#print axioms Unshackled.crz_toTwoConst
#print axioms Unshackled.crz_fromTwoConst
#print axioms Unshackled.crz_two_steps

-- The width algebra: rot-free steps keep every storable value in a finite
-- alphabet, so `*` is mandatory for unbounded storage; the escalator that
-- mints wide addresses is the rot/movd feedback.
#print axioms Unshackled.width_crz_le
#print axioms Unshackled.width_rot_le
#print axioms Unshackled.width_succ_le
#print axioms Unshackled.width_ofChar_le
#print axioms Unshackled.step_widthBounded
#print axioms Unshackled.widthBounded_step1
#print axioms Unshackled.rot_one
#print axioms Unshackled.width_rot_one
#print axioms Unshackled.growRotWidth_double

-- The branch arithmetic: seven crazy operations turn any accumulator into
-- either of two chosen jump targets, decided by a flag cell.
#print axioms Unshackled.trit_map2
#print axioms Unshackled.crz_absorb
#print axioms Unshackled.crz_zero_zero
#print axioms Unshackled.crz_zero_eof
#print axioms Unshackled.cols_spec
#print axioms Unshackled.shape_uniform₁
#print axioms Unshackled.shape_uniform₂
#print axioms Unshackled.branch_arith

-- The machine half: step lemmas over step1, straight-line crazy rows as a
-- fold, and the eight-instruction branch gadget.
#print axioms Unshackled.step1_eq
#print axioms Unshackled.step1_crazy
#print axioms Unshackled.step1_movd
#print axioms Unshackled.step1_jmp
#print axioms Unshackled.run?_add
#print axioms Unshackled.crazy_run
#print axioms Unshackled.branch_gadget
#print axioms Unshackled.branch_gadget_cases

-- The copy algebra: a read-write hop is the trit 3-cycle, so three hops
-- move an unknown value exactly.
#print axioms Unshackled.trit_vmap
#print axioms Unshackled.hop_eq_vmap
#print axioms Unshackled.hop_hop_hop

-- Why the unbounded part cannot live in fresh memory: a virgin phase that
-- can rotate can also halt, 42 addresses along in the same phase.
#print axioms Unshackled.opcode_of_decode
#print axioms Unshackled.virgin_phase_parity
#print axioms Unshackled.rotr_forces_halt
#print axioms Unshackled.halt_forces_rotr

-- Re-enterable rows: the no-op sweep that restores a two-cycle gadget.
#print axioms Unshackled.encrypt_encrypt_two_cycle
#print axioms Unshackled.nop_run
#print axioms Unshackled.row_restored

-- Terminating runs: splitting a run, the halting ending a simulation needs,
-- and the well-founded loop rule.
#print axioms Unshackled.exec_run?_add
#print axioms Unshackled.exec_halts_of_run?
#print axioms Unshackled.image_halts_of_run?
#print axioms Unshackled.run_of_measure
#print axioms Unshackled.branch_on_mark

-- Mixed rows and the two-sweep gadget: a straight-line row that restores
-- itself and so may be entered any number of times.
#print axioms Unshackled.row_run
#print axioms Unshackled.rowFold_false
#print axioms Unshackled.two_sweep

-- Emitting, and reading the answer back: the counter machine counts bytes,
-- so the decoder is the byte count.
#print axioms Unshackled.doOutput_star
#print axioms Unshackled.step1_out
#print axioms Unshackled.size_append_star
#print axioms Unshackled.decodeBytes_append_star
#print axioms Unshackled.outClosed_of_step1_out

-- The register encoding: with blank = ...000 and mark = ...111, set, clear
-- and test each cost one crazy operation.
#print axioms Unshackled.crz_set_mark
#print axioms Unshackled.crz_clear_mark
#print axioms Unshackled.crz_test_blank
#print axioms Unshackled.crz_test_mark
#print axioms Unshackled.crz_restore_mark
#print axioms Unshackled.register_test_roundtrip

-- Chains: a working cell joined to the next by a stable jmp, which removes
-- padding from the layout entirely.
#print axioms Unshackled.chain_link
#print axioms Unshackled.chain_run
#print axioms Unshackled.enter_chain
#print axioms Unshackled.chainFold_congr
#print axioms Unshackled.gadget_run

-- The chosen register encoding: blank ...000, mark ...222, tested
-- non-destructively by the accumulator ...111, which hands back the branch
-- flag with no conversion.
#print axioms Unshackled.crz_probe_blank
#print axioms Unshackled.crz_probe_mark
#print axioms Unshackled.crz_load_testAcc
#print axioms Unshackled.register_probe
#print axioms Unshackled.probe_feeds_branch

-- The accumulator ladder (three self-restoring constants, a three-cycle)
-- and the two-visit register writes it drives.
#print axioms Unshackled.ladder_blank_to_one
#print axioms Unshackled.ladder_one_to_eof
#print axioms Unshackled.ladder_eof_to_blank
#print axioms Unshackled.ladder_cycle
#print axioms Unshackled.register_set
#print axioms Unshackled.register_clear
#print axioms Unshackled.no_single_step_blank_to_mark
#print axioms Unshackled.no_single_step_mark_to_blank

-- Registers as a difference of two unary tapes, which makes inc, dec and
-- the zero test all forward walks.
#print axioms Unshackled.TapePair.value_inc
#print axioms Unshackled.TapePair.value_dec
#print axioms Unshackled.TapePair.inc_wf
#print axioms Unshackled.TapePair.dec_wf
#print axioms Unshackled.TapePair.value_eq_zero_iff

-- The register file, and its refinement of Counter.CState.
#print axioms Unshackled.RegFile.refines_init
#print axioms Unshackled.RegFile.refines_up
#print axioms Unshackled.RegFile.refines_down
#print axioms Unshackled.RegFile.refines_emit
#print axioms Unshackled.RegFile.refines_zero_iff

-- Where the tapes live: the interleaved slot layout and its update lemmas.
#print axioms Unshackled.slot_inj
#print axioms Unshackled.regAddr_inj
#print axioms Unshackled.regMem_first_blank
#print axioms Unshackled.regMem_mark_below
#print axioms Unshackled.regMem_up
#print axioms Unshackled.regMem_down

-- The simulation invariant, and the four ways a command moves it.
#print axioms Unshackled.sim_init
#print axioms Unshackled.sim_inc
#print axioms Unshackled.sim_dec
#print axioms Unshackled.sim_emit
#print axioms Unshackled.sim_frame
#print axioms Unshackled.sim_loop_test

-- Why a branch flag has to be read from a cell rather than computed.
#print axioms Unshackled.crzChain_trit
#print axioms Unshackled.crzChain_agree
#print axioms Unshackled.no_accumulator_flag

-- The two printability conditions a jmp involves, and why only one is a
-- side condition.
#print axioms Unshackled.ofOpcode?_ne_outOfBounds
#print axioms Unshackled.decode_outOfBounds_iff
#print axioms Unshackled.printable_of_decode
#print axioms Unshackled.printable_of_decode_jmp

-- UNLAMBDA: the functional route. The call-by-value big-step relation and
-- its bridge to the CEK machine, bracket abstraction, the counter machine
-- rendered in combinators, and the completeness witness.
#print axioms URMUnlambda.run_reaches
#print axioms URMUnlambda.lam_spec
#print axioms URMUnlambda.ev_app_lam
#print axioms URMUnlambda.numE_spec
#print axioms URMUnlambda.succF_spec
#print axioms URMUnlambda.predF_spec
#print axioms URMUnlambda.getE_spec
#print axioms URMUnlambda.setE_spec
#print axioms URMUnlambda.selfE_unfold
#print axioms URMUnlambda.loopE_zero
#print axioms URMUnlambda.loopE_succ
#print axioms URMUnlambda.codeE_spec
#print axioms URMUnlambda.simulation
#print axioms URMUnlambda.compile
#print axioms unlambdaComplete

-- Whitespace reports its own I/O events, which is what a behavioural
-- statement about a compiler into whitespace has to rest on. `exec_wf` is
-- the invariant carried through the interpreter; the two `evalTrace`
-- lemmas are the `TraceLang` laws. The `Input` and `ByteArray` lemmas
-- under them are shared infrastructure: `readLine?` used to be a `partial
-- def` and `ByteArray.toList` has no lemmas in core, so both had to be
-- given equations before anything could be said about a read.
#print axioms ByteArray.toList_eq
#print axioms Langlib.Common.Input.read?_remaining
#print axioms Langlib.Common.Input.readLineGo_data
#print axioms Langlib.Common.Input.readLineGo_pos_le
#print axioms Langlib.Common.Input.readLine?_data
#print axioms Langlib.Common.Input.readLine?_pos_le
#print axioms Langlib.Common.Input.between_append_remaining
#print axioms Langlib.Whitespace.exec_wf
#print axioms Langlib.Whitespace.evalTrace_outputs
#print axioms Langlib.Whitespace.evalTrace_inputs

-- Turpentine reports its own events too, which is the other half a
-- behavioural compiler statement needs: `TurpentineBehavesWith` is the
-- I/O-aware refinement of `TurpentineHaltsWith`, and `behavesWith_wf` is
-- what stops it from being satisfiable by an invented trace.
#print axioms Langlib.Turpentine.exec_wf
#print axioms Langlib.Turpentine.evalTrace_outputs
#print axioms Langlib.Turpentine.evalTrace_inputs
#print axioms Langlib.Turpentine.behavesWith_trace
#print axioms Langlib.Turpentine.behavesWith_wf
#print axioms Langlib.Turpentine.behavesWith_haltsWith

-- Subleq reports its events too. One instruction, two of whose forms do
-- I/O, so the record is short; the laws come from the same invariant.
-- With this the two backends the library has proved answer-correct can
-- both be stated behaviourally.
#print axioms Langlib.Subleq.exec_wf
#print axioms Langlib.Subleq.evalTrace_outputs
#print axioms Langlib.Subleq.evalTrace_inputs

-- SKI: the same counter machine in front, and nothing shared behind it.
-- Head reduction and its bridge to the interpreter, the combinators, the
-- simulation, the unary answer, and the completeness witness.
#print axioms URMSki.hstep_step
#print axioms URMSki.hstep_app
#print axioms URMSki.eval_K
#print axioms URMSki.numT_spec
#print axioms URMSki.succT_spec
#print axioms URMSki.predT_spec
#print axioms URMSki.getT_spec
#print axioms URMSki.setT_spec
#print axioms URMSki.hr_selfT_unfold
#print axioms URMSki.loop_step
#print axioms URMSki.codeT_sim
#print axioms URMSki.unary_spec
#print axioms URMSki.decodeOutput_unaryNF
#print axioms URMSki.simulation
#print axioms URMSki.compile
#print axioms skiComplete
