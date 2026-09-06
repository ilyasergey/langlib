import Langlib.Languages.JavaGen.Validation

/-!
# A finite-control sweeping transducer compiled to JavaGen

The construction isolates the read/write and end-turn mechanism of
Grigore (2017), §5. A transition reads one symbol and writes any finite
word, including the empty word. An end transition either reverses the
scan or halts. Compilation enumerates finite control/alphabet tables;
it never runs the source machine.

This is the target half of the universal compiler. The URM bridge and
answer readout remain separate obligations. Concrete halts currently
retain the final tape in the ordinary subtype derivation record.
-/

namespace Langlib.JavaGen.Sweep
open Langlib.JavaGen

/-- Both domains are finite, while the tape and replacement words are unbounded. -/
structure Machine (states symbols : Nat) where
  initial : Fin states
  transition : Fin states → Fin symbols → Fin states × List (Fin symbols)
  boundary : Fin states → Option (Fin states)

structure Config (states symbols : Nat) where
  control : Fin states
  /-- Written symbols, nearest to the scanning head first. -/
  left : List (Fin symbols) := []
  /-- Unread symbols, in scanning order. -/
  right : List (Fin symbols) := []
deriving Repr, DecidableEq, BEq

/-- End turns reverse the direction of scanning without a hidden tape traversal. -/
def advance (m : Machine states symbols) (c : Config states symbols) :
    Option (Config states symbols) :=
  match c.right with
  | a :: rest =>
    let (next, word) := m.transition c.control a
    some ⟨next, word.reverse ++ c.left, rest⟩
  | [] => (m.boundary c.control).map (fun next => ⟨next, [], c.left⟩)

def stateName (s : Fin states) : String := "State_" ++ toString s.val
def letterName (a : Fin symbols) : String := "Letter_" ++ toString a.val
def turnName (s : Fin states) : String := "Turn_" ++ toString s.val

def pad (word : List (Fin symbols)) : Ty :=
  word.flatMap (fun a => [letterName a, "ScanPad"])

@[simp] theorem pad_append (u v : List (Fin symbols)) : pad (u ++ v) = pad u ++ pad v := by
  simp [pad]

/-- Every represented tape ends in the two constructors used for turning. -/
def tape (word : List (Fin symbols)) : Ty := pad word ++ ["End", "End"]

def query (c : Config states symbols) : Query :=
  ⟨stateName c.control :: tape c.left, tape c.right⟩

/-- Reading/writing always takes two subtype transitions, regardless of word length. -/
def readBase (m : Machine states symbols) (s : Fin states) (a : Fin symbols) : Template :=
  let (next, word) := m.transition s a
  ⟨[letterName a, "ScanPad", stateName next] ++ pad word.reverse, .var⟩

def endBase (m : Machine states symbols) (s : Fin states) : Template :=
  match m.boundary s with
  | none => ⟨["End", "End"], .zero⟩
  | some _ => ⟨["End", turnName s, "ScanPad"], .var⟩

def stateDecl (m : Machine states symbols) (s : Fin states) : Decl :=
  ⟨stateName s, List.ofFn (readBase m s) ++ [endBase m s]⟩

/-- Each continuing state gets one distinct inert turn head. -/
def turnBases (m : Machine states symbols) : List Template :=
  (List.ofFn fun s : Fin states =>
    (m.boundary s).map (fun next =>
      (⟨[turnName s, "ScanPad", stateName next, "End", "End"], .var⟩ : Template))).filterMap id

def declarations (m : Machine states symbols) : List Decl :=
  [⟨"ScanPad", []⟩, ⟨"End", turnBases m⟩] ++
  List.ofFn (stateDecl m) ++
  List.ofFn (fun a : Fin symbols => (⟨letterName a, []⟩ : Decl)) ++
  List.ofFn (fun s : Fin states => (⟨turnName s, []⟩ : Decl))

def programAt (m : Machine states symbols) (c : Config states symbols) : Program :=
  { classes := declarations m, query := query c }

def program (m : Machine states symbols) (input : List (Fin symbols)) : Program :=
  programAt m ⟨m.initial, [], input⟩

/-- Use the ordinary validator, including all indirect inheritance paths. -/
def compile (m : Machine states symbols) (input : List (Fin symbols)) : Except String Prepared :=
  prepare (program m input)

end Langlib.JavaGen.Sweep
