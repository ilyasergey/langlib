import Langlib.Common.Io
import Langlib.Languages.Thue.Syntax
import Langlib.Languages.Thue.Parser

/-!
# Thue: reference semantics

A pure, fuel-based rewriting engine. Thue is deliberately nondeterministic:
at each step, *some* rule is applied at *some* occurrence of its lhs. The
semantic choices (all recorded with sources in `docs/thue/spec.md`) are:

* the default strategy is deterministic, for reproducible tests: scan the
  rules in program order and apply the first rule whose lhs occurs in the
  state, at its leftmost occurrence;
* `Strategy.random seed` restores the original spirit: all
  (occurrence, rule) pairs are collected, ordered by position (ties by rule
  order), and one is chosen uniformly by a seeded 64-bit LCG (Knuth's MMIX
  multiplier), so runs are reproducible per seed;
* a rhs of exactly `:::` reads one input line (without its newline); at end
  of input it substitutes the empty string;
* a rhs `~text` erases the lhs and appends `text` and a newline to the
  output (Colagioia's interpreter prints with `puts`);
* an empty rhs erases the lhs;
* execution halts when no rule's lhs occurs in the state; one unit of fuel
  pays for one rewrite step.

`Config.finalState` is a langlib extension: on a normal halt the final state
and a newline are appended to the output, which makes pure rewriters (like
the binary-increment example) observable.
-/

namespace Langlib.Thue

open Langlib.Common

/-- How the next (occurrence, rule) pair is chosen. -/
inductive Strategy where
  /-- Deterministic: first rule in program order whose lhs occurs, at its
  leftmost occurrence. The langlib default. -/
  | first
  /-- Seeded pseudo-random choice, uniform over all occurrences of all
  rules' left-hand sides; mirrors the original interpreter's default, with
  a documented generator instead of `rand()`. -/
  | random (seed : UInt64)
deriving Repr, BEq, Inhabited

structure Config where
  strategy : Strategy := .first
  /-- Langlib extension: on a normal halt, append the final state and a
  newline to the output. -/
  finalState : Bool := false
deriving Repr, BEq, Inhabited

/-- One step of the PRNG: Knuth's MMIX linear congruential generator,
`s' = 6364136223846793005 * s + 1442695040888963407 (mod 2^64)`. -/
def lcgNext (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

/-- Advance the PRNG and pick an index below `n` (from the high 31 bits, so
small moduli are not fed the weak low bits). -/
def lcgPick (s : UInt64) (n : Nat) : UInt64 × Nat :=
  let s' := lcgNext s
  (s', (s' >>> 33).toNat % n)

/-- The machine state: the string being rewritten (as a character list),
the input cursor, the output accumulated so far, and the PRNG state. -/
structure MState where
  str : List Char
  input : Input
  output : ByteArray := .empty
  rng : UInt64 := 0

/-- All positions (0-based, in characters) at which `pat` occurs in `s`,
including overlapping occurrences, in increasing order. The empty pattern
occurs nowhere (the parser never produces an empty lhs). -/
def occurrences (pat s : List Char) : List Nat :=
  if pat.isEmpty then [] else go s 0
where
  go : List Char → Nat → List Nat
    | [], _ => []
    | l@(_ :: tl), i => (if pat.isPrefixOf l then [i] else []) ++ go tl (i + 1)

/-- Leftmost occurrence of `pat` in `s`, if any. Short-circuits (and is
tail-recursive), so scanning a large state stays cheap. -/
def firstOccurrence? (pat s : List Char) : Option Nat :=
  if pat.isEmpty then none else go s 0
where
  go : List Char → Nat → Option Nat
    | [], _ => none
    | l@(_ :: tl), i => if pat.isPrefixOf l then some i else go tl (i + 1)

/-- Deterministic choice: first rule in order with a match, leftmost
occurrence. -/
def firstMatch : List Rule → List Char → Option (Nat × Rule)
  | [], _ => none
  | r :: rs, s =>
    match firstOccurrence? r.lhs.toList s with
    | some p => some (p, r)
    | none => firstMatch rs s

/-- Every (position, rule index, rule) match, sorted by position with ties
broken by rule order. This is the candidate list the random strategy draws
from, mirroring the original interpreter's occurrence list. -/
def allMatches (rules : List Rule) (s : List Char) : List (Nat × Nat × Rule) :=
  (go rules 0).mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 ≤ b.2.1)
where
  go : List Rule → Nat → List (Nat × Nat × Rule)
    | [], _ => []
    | r :: rs, i => ((occurrences r.lhs.toList s).map fun p => (p, i, r)) ++ go rs (i + 1)

/-- Apply rule `r` at position `pos` (where its lhs is known to occur),
performing the rule's I/O effect. -/
def applyAt (st : MState) (pos : Nat) (r : Rule) : MState :=
  let pre := st.str.take pos
  let post := st.str.drop (pos + r.lhs.toList.length)
  match r.rhs with
  | .str rep => { st with str := pre ++ rep.toList ++ post }
  | .input =>
    match st.input.readLine? with
    | some (line, input') => { st with str := pre ++ line.toList ++ post, input := input' }
    | none => { st with str := pre ++ post }
  | .output o =>
    { st with str := pre ++ post, output := st.output ++ (o ++ "\n").toUTF8 }

/-- One rewrite step; `none` means no rule's lhs occurs (the program halts). -/
def step (cfg : Config) (rules : List Rule) (st : MState) : Option MState :=
  match cfg.strategy with
  | .first =>
    (firstMatch rules st.str).map fun (p, r) => applyAt st p r
  | .random _ =>
    match allMatches rules st.str with
    | [] => none
    | ms =>
      let (rng', idx) := lcgPick st.rng ms.length
      match ms[idx]? with
      | some (p, _, r) => some (applyAt { st with rng := rng' } p r)
      | none => none  -- unreachable: idx < ms.length

/-- Execute with the given fuel; one unit of fuel per rewrite step. -/
def exec (cfg : Config) (rules : List Rule) : Nat → MState → MState × Exit
  | 0, st => (st, .outOfFuel)
  | fuel + 1, st =>
    match step cfg rules st with
    | none => (st, .halted)
    | some st' => exec cfg rules fuel st'

/-- Run a parsed program: the pure interpreter core. -/
def evalProg (cfg : Config) (p : Prog) (input : Input) (fuel : Nat) : RunResult :=
  let seed := match cfg.strategy with
    | .random s => s
    | .first => 0
  let (st, exit) := exec cfg p.rules fuel { str := p.initial.toList, input, rng := seed }
  let output :=
    if cfg.finalState && exit == .halted then
      st.output ++ (String.ofList st.str ++ "\n").toUTF8
    else
      st.output
  { output, exit }

/-- Parse and run: the entry point used by the runner and the tests. -/
def run (cfg : Config := {}) (src : String) (input : Input) (fuel : Nat) :
    Except String RunResult := do
  let prog ← parse src
  return evalProg cfg prog input fuel

end Langlib.Thue
