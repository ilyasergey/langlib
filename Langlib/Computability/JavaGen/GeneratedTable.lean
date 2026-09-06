import Langlib.Computability.JavaGen.Names
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup

/-! # Uniform structural properties of generated class declarations

The finite head vocabulary distinguishes control, letters, turns and the two
fixed constructors. These facts cover syntax-level validation without imposing
a bound on the tape or on transition replacement words. Relating them to the
executable validator's traversal is proved separately in ValidationProof.
-/

namespace Langlib.Computability.JavaGen.Sweep
open Langlib.JavaGen

inductive Head (states symbols : Nat) where
  | padding
  | boundary
  | state (index : Fin states)
  | letter (index : Fin symbols)
  | turn (index : Fin states)
deriving DecidableEq

def Head.name : Head states symbols → String
  | .padding => "ScanPad"
  | .boundary => "End"
  | .state s => stateName s
  | .letter a => letterName a
  | .turn s => turnName s

theorem head_name_injective : Function.Injective (@Head.name states symbols) := by
  intro a b h
  cases a <;> cases b
  all_goals simp_all [Head.name, stateName_injective.eq_iff, letterName_injective.eq_iff,
    turnName_injective.eq_iff]
  all_goals simp_all [stateName, letterName, turnName, ← String.toList_inj, String.toList_append]

def heads (states symbols : Nat) : List (Head states symbols) :=
  [.padding, .boundary] ++ List.ofFn Head.state ++ List.ofFn Head.letter ++ List.ofFn Head.turn

@[simp] theorem mem_heads (h : Head states symbols) : h ∈ heads states symbols := by
  cases h <;> simp [heads, List.mem_ofFn]

theorem heads_nodup (states symbols : Nat) : (heads states symbols).Nodup := by
  simp [heads, List.nodup_append, List.nodup_ofFn, Function.Injective, List.mem_ofFn]
  intro a b h
  rcases h with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp

theorem declaration_names (m : Machine states symbols) :
    (declarations m).map Decl.name = (heads states symbols).map Head.name := by
  simp [declarations, heads, Head.name, stateDecl, List.map_ofFn, Function.comp_def]

/-- The generated class table never declares the same name twice. -/
theorem declarations_nodup (m : Machine states symbols) :
    ((declarations m).map Decl.name).Nodup := by
  rw [declaration_names]
  exact List.Nodup.map head_name_injective (heads_nodup states symbols)

theorem head_declared (m : Machine states symbols) (h : Head states symbols) :
    h.name ∈ (declarations m).map Decl.name := by
  rw [declaration_names]
  exact List.mem_map.mpr ⟨h, mem_heads h, rfl⟩

/-- Every generated constructor identifier is legal, regardless of its index. -/
theorem declarations_validName (m : Machine states symbols) :
    ∀ d ∈ declarations m, validName d.name = true := by
  intro d hd
  have h : d.name ∈ (declarations m).map Decl.name := List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [declaration_names] at h
  obtain ⟨head, _, eq⟩ := List.mem_map.mp h
  rw [← eq]
  cases head with
  | padding => change validName "ScanPad" = true; decide
  | boundary => change validName "End" = true; decide
  | state s => exact valid_stateName s
  | letter a => exact valid_letterName a
  | turn s => exact valid_turnName s

@[simp] theorem pad_length (word : List (Fin symbols)) : (pad word).length = 2 * word.length := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
    change (letterName a :: "ScanPad" :: pad rest).length = _
    simp only [List.length_cons, ih]
    omega

/-- All constructors inside a represented word are declared, not only its head. -/
theorem pad_declared (m : Machine states symbols) (word : List (Fin symbols)) :
    ∀ name ∈ pad word, name ∈ (declarations m).map Decl.name := by
  intro name hn
  obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact head_declared m (.letter a)
  · exact head_declared m .padding

theorem tape_declared (m : Machine states symbols) (word : List (Fin symbols)) :
    ∀ name ∈ tape word, name ∈ (declarations m).map Decl.name := by
  intro name hn
  simp only [tape, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hn
  rcases hn with hn | rfl
  · exact pad_declared m word name hn
  · exact head_declared m .boundary

/-- Both sides of every generated query use only declared constructors. -/
theorem query_declared (m : Machine states symbols) (c : Config states symbols) :
    (∀ name ∈ (query c).lhs, name ∈ (declarations m).map Decl.name) ∧
    (∀ name ∈ (query c).rhs, name ∈ (declarations m).map Decl.name) := by
  constructor
  · intro name hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact head_declared m (.state c.control)
    · exact tape_declared m c.left name hn
  · exact tape_declared m c.right

theorem readBase_declared (m : Machine states symbols) (s : Fin states) (a : Fin symbols) :
    ∀ name ∈ (readBase m s a).ctors, name ∈ (declarations m).map Decl.name := by
  intro name hn
  simp only [readBase, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with (rfl | rfl | rfl) | hn
  · exact head_declared m (.letter a)
  · exact head_declared m .padding
  · exact head_declared m (.state (m.transition s a).1)
  · exact pad_declared m _ name hn

theorem readBase_odd (m : Machine states symbols) (s : Fin states) (a : Fin symbols) :
    (readBase m s a).ctors.length % 2 = 1 := by
  simp [readBase, pad_length, Nat.add_mod]


theorem endBase_declared (m : Machine states symbols) (s : Fin states) :
    ∀ name ∈ (endBase m s).ctors, name ∈ (declarations m).map Decl.name := by
  intro name hn
  cases hb : m.boundary s with
  | none =>
    simp [endBase, hb] at hn
    subst name
    exact head_declared m .boundary
  | some next =>
    simp [endBase, hb] at hn
    rcases hn with rfl | rfl | rfl
    · exact head_declared m .boundary
    · exact head_declared m (.turn s)
    · exact head_declared m .padding

theorem endBase_odd (m : Machine states symbols) (s : Fin states)
    (retains : (endBase m s).tail = .var) : (endBase m s).ctors.length % 2 = 1 := by
  cases hb : m.boundary s <;> simp_all [endBase]

/-- Characterize every generated turning superclass, including its control index. -/
theorem mem_turnBases (m : Machine states symbols) (t : Template) :
    t ∈ turnBases m ↔ ∃ s next, m.boundary s = some next ∧
      t = ⟨[turnName s, "ScanPad", stateName next, "End", "End"], .var⟩ := by
  simp only [turnBases, List.mem_filterMap, List.mem_ofFn]
  constructor
  · rintro ⟨x, ⟨s, rfl⟩, hx⟩
    cases hb : m.boundary s with
    | none => simp [hb] at hx
    | some next =>
      refine ⟨s, next, hb, ?_⟩
      simpa [hb] using hx.symm
  · rintro ⟨s, next, hb, rfl⟩
    exact ⟨_, ⟨s, rfl⟩, by simp [hb]⟩

theorem turnBase_declared (m : Machine states symbols) (t : Template) (ht : t ∈ turnBases m) :
    ∀ name ∈ t.ctors, name ∈ (declarations m).map Decl.name := by
  obtain ⟨s, next, _, rfl⟩ := (mem_turnBases m t).mp ht
  intro name hn
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact head_declared m (.turn s)
  · exact head_declared m .padding
  · exact head_declared m (.state next)
  · exact head_declared m .boundary

/-- Every direct superclass has declared arguments and respects contravariance
parity whenever it retains the type parameter. -/
theorem declaration_bases_valid (m : Machine states symbols) (d : Decl) (hd : d ∈ declarations m)
    (t : Template) (ht : t ∈ d.bases) :
    (∀ name ∈ t.ctors, name ∈ (declarations m).map Decl.name) ∧
    (t.tail = .var → t.ctors.length % 2 = 1) := by
  simp only [declarations, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_ofFn] at hd
  rcases hd with (((rfl | rfl) | ⟨s, rfl⟩) | ⟨a, rfl⟩) | ⟨s, rfl⟩
  · simp at ht
  · refine ⟨turnBase_declared m t ht, ?_⟩
    obtain ⟨s, next, _, rfl⟩ := (mem_turnBases m t).mp ht
    simp
  · simp only [stateDecl, List.mem_append, List.mem_ofFn, List.mem_singleton] at ht
    rcases ht with ⟨a, rfl⟩ | rfl
    · exact ⟨readBase_declared m s a, fun _ => readBase_odd m s a⟩
    · exact ⟨endBase_declared m s, endBase_odd m s⟩
  · simp at ht
  · simp at ht


/-- The declaration belonging to one member of the finite head vocabulary. -/
def Head.decl (m : Machine states symbols) : Head states symbols → Decl
  | .padding => ⟨"ScanPad", []⟩
  | .boundary => ⟨"End", turnBases m⟩
  | .state s => stateDecl m s
  | .letter a => ⟨letterName a, []⟩
  | .turn s => ⟨turnName s, []⟩

@[simp] theorem head_decl_name (m : Machine states symbols) (h : Head states symbols) :
    (h.decl m).name = h.name := by cases h <;> rfl

theorem declarations_eq_heads (m : Machine states symbols) :
    declarations m = (heads states symbols).map (Head.decl m) := by
  simp [declarations, heads, Head.decl, List.map_ofFn, Function.comp_def]

/-- Superclass heads, abstracting away the nested type arguments. -/
def directHeads (m : Machine states symbols) : Head states symbols → List (Head states symbols)
  | .boundary => ((List.finRange states).filter (fun s => (m.boundary s).isSome)).map Head.turn
  | .state _ => List.ofFn Head.letter ++ [.boundary]
  | _ => []

theorem turnBases_heads (m : Machine states symbols) :
    (turnBases m).map (fun t => t.ctors.head?) =
      (directHeads m .boundary).map (fun h => some h.name) := by
  simp only [turnBases, directHeads, List.ofFn_eq_map, List.filterMap_map, List.map_map,
    Function.comp_def]
  induction List.finRange states with
  | nil => rfl
  | cons s rest ih =>
    simp only [id_eq, Head.name] at ih
    cases hb : m.boundary s <;> simp [hb, ih, Head.name]

@[simp] theorem endBase_head (m : Machine states symbols) (s : Fin states) :
    (endBase m s).ctors.head? = some "End" := by
  cases hb : m.boundary s <;> simp [endBase, hb]

/-- The abstract edge list is exactly the one traversed by the validator. -/
theorem directHeads_eq (m : Machine states symbols) (h : Head states symbols) :
    ((h.decl m).bases.map (fun t => t.ctors.head?)) =
      (directHeads m h).map (fun k => some k.name) := by
  cases h with
  | boundary => exact turnBases_heads m
  | state s => simp [Head.decl, stateDecl, directHeads, List.map_ofFn, Function.comp_def,
      readBase, Head.name]
  | padding => rfl
  | letter => rfl
  | turn => rfl

theorem directHeads_nodup (m : Machine states symbols) (h : Head states symbols) :
    (directHeads m h).Nodup := by
  cases h with
  | boundary =>
    exact List.Nodup.map (by intro a b h; cases h; rfl)
      ((List.nodup_finRange states).filter _)
  | state s =>
    simp [directHeads, List.nodup_append, List.nodup_ofFn, Function.Injective, List.mem_ofFn]
  | padding => simp [directHeads]
  | letter => simp [directHeads]
  | turn => simp [directHeads]

/-- No generated declaration repeats a direct superclass head. -/
theorem declaration_bases_nodup (m : Machine states symbols) (d : Decl) (hd : d ∈ declarations m) :
    (d.bases.map (fun t => t.ctors.head?)).Nodup := by
  rw [declarations_eq_heads] at hd
  obtain ⟨h, _, rfl⟩ := List.mem_map.mp hd
  rw [directHeads_eq]
  exact List.Nodup.map (fun a b h => head_name_injective (Option.some.inj h)) (directHeads_nodup m h)

/-- A decreasing rank for head inheritance: state → boundary → turn.
Letter and padding heads are also terminal. Type arguments are not traversed. -/
def Head.rank : Head states symbols → Nat
  | .state _ => 2
  | .boundary => 1
  | _ => 0

theorem directHeads_rank (m : Machine states symbols) (h k : Head states symbols)
    (edge : k ∈ directHeads m h) : k.rank < h.rank := by
  cases h with
  | boundary =>
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp edge
    simp [Head.rank]
  | state s =>
    simp only [directHeads, List.mem_append, List.mem_ofFn, List.mem_singleton] at edge
    rcases edge with ⟨a, rfl⟩ | rfl <;> simp [Head.rank]
  | padding => simp [directHeads] at edge
  | letter => simp [directHeads] at edge
  | turn => simp [directHeads] at edge

/-- Generated inheritance is acyclic for every finite machine, independently
of its (possibly infinite) subtype execution. -/
theorem generated_inheritance_wellFounded (m : Machine states symbols) :
    WellFounded (fun k h : Head states symbols => k ∈ directHeads m h) :=
  Subrelation.wf (fun {k h} edge => directHeads_rank m h k edge) (measure Head.rank).wf


/-- The complete inheritance-head order, including reflexivity. -/
def descendants (m : Machine states symbols) : Head states symbols → List (Head states symbols)
  | .state s => .state s :: (List.ofFn Head.letter ++ .boundary :: directHeads m .boundary)
  | .boundary => .boundary :: directHeads m .boundary
  | h => [h]

theorem descendants_unfold (m : Machine states symbols) (h : Head states symbols) :
    descendants m h = h :: (directHeads m h).flatMap (descendants m) := by
  cases h with
  | padding => rfl
  | letter => rfl
  | turn => rfl
  | boundary =>
    simp only [descendants, directHeads, List.flatMap_map]
    simp [← List.map_eq_flatMap]
  | state s =>
    simp only [descendants, directHeads, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    congr 1
    congr 1
    rw [List.ofFn_eq_map, List.flatMap_map]
    simp [descendants, ← List.map_eq_flatMap]

/-- Head lookup in the finite generated vocabulary, used only by proofs. -/
def findHead (states symbols : Nat) (name : String) : Option (Head states symbols) :=
  (heads states symbols).find? (fun h => h.name == name)

@[simp] theorem findHead_name (h : Head states symbols) : findHead states symbols h.name = some h := by
  unfold findHead
  cases found : (heads states symbols).find? (fun k => k.name == h.name) with
  | none =>
    have bad := List.find?_eq_none.mp found h (mem_heads h)
    simp at bad
  | some k =>
    have hk := List.find?_some found
    have eq : k = h := head_name_injective (by simpa using hk)
    simp [eq]

def descendantNames (m : Machine states symbols) (name : Option String) : List (Option String) :=
  match name.bind (findHead states symbols) with
  | none => []
  | some h => (descendants m h).map (fun k => some k.name)

@[simp] theorem descendantNames_name (m : Machine states symbols) (h : Head states symbols) :
    descendantNames m (some h.name) = (descendants m h).map (fun k => some k.name) := by
  simp [descendantNames]


/-- Generated inheritance has no diamonds: each ancestor head occurs once,
so the validator cannot discover incompatible instantiations of that head. -/
theorem descendants_nodup (m : Machine states symbols) (h : Head states symbols) :
    (descendants m h).Nodup := by
  have turns := directHeads_nodup m (Head.boundary : Head states symbols)
  cases h with
  | padding => simp [descendants]
  | letter => simp [descendants]
  | turn => simp [descendants]
  | boundary =>
    simp only [descendants, List.nodup_cons]
    refine ⟨?_, turns⟩
    simp [directHeads]
  | state s =>
    simp only [descendants, List.nodup_cons, List.nodup_append, List.nodup_ofFn]
    refine ⟨?_, ?_, ⟨?_, turns⟩, ?_⟩
    · simp [List.mem_ofFn, directHeads]
    · intro a b h
      cases h
      rfl
    · simp [directHeads]
    · intro a ha b hb eq
      obtain ⟨letter, rfl⟩ := List.mem_ofFn.mp ha
      simp [directHeads] at hb
      rcases hb with rfl | ⟨turn, _, rfl⟩ <;> cases eq

end Langlib.Computability.JavaGen.Sweep
