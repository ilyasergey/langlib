import Langlib.Computability.JavaGen.ValidationTotality
import Langlib.Computability.JavaGen.SweepProof

/-! # Uniform symbolic lookup certification

The actual validator closure has unique heads and contains every direct
superclass. Its ordinary first-match lookup therefore returns exactly the
templates used by the operational sweeping simulation.
-/

namespace Langlib.Computability.JavaGen.Sweep
open Langlib.JavaGen

private theorem find_key {α β : Type} [BEq β] [LawfulBEq β] (key : α → β)
    (xs : List α) (distinct : (xs.map key).Nodup) (a : α) (member : a ∈ xs) :
    xs.find? (fun b => key b == key a) = some a := by
  cases found : xs.find? (fun b => key b == key a) with
  | none =>
    have bad := List.find?_eq_none.mp found a member
    simp at bad
  | some b =>
    have same := List.find?_some found
    have eq : b = a := List.inj_on_of_nodup_map distinct
      (List.mem_of_find?_eq_some found) member (by simpa using same)
    simp [eq]

/-- Resolve a known member of the generated symbolic closure. Distinct heads
ensure that an earlier, different instantiation cannot shadow it. -/
theorem generated_lookup (m : Machine states symbols) (c : Config states symbols)
    (h : Head states symbols) (a : Ancestor) (member : a ∈ generatedRows m h.name)
    (target : String) (head : a.type.ctors.head? = some target) :
    lookup (generatedPrepared m c) h.name target = some a.type := by
  have root := find_key Prod.fst (generatedPrepared m c).closure
    (by simpa [generatedPrepared, List.map_map, Function.comp_def] using declarations_nodup m)
    (h.name, generatedRows m h.name)
    (List.mem_map.mpr ⟨h.name, head_declared m h, rfl⟩)
  have row := find_key (fun a : Ancestor => a.type.ctors.head?) (generatedRows m h.name)
    (generatedRows_nodup m h) a member
  simp only [head] at row
  simp only [lookup, root, bind, Option.bind, row, pure]

/-- Reflexivity is retained with an empty inheritance path. -/
theorem generated_lookup_self (m : Machine states symbols) (c : Config states symbols)
    (h : Head states symbols) :
    lookup (generatedPrepared m c) h.name h.name = some ⟨[h.name], .var⟩ :=
  generated_lookup m c h ⟨⟨[h.name], .var⟩, []⟩ (generatedRows_members m h).1 h.name rfl

/-- Every declared direct superclass has its exact symbolic body in the
prepared table, including the body that erases its argument at a halt. -/
theorem generated_lookup_base (m : Machine states symbols) (c : Config states symbols)
    (h : Head states symbols) (base : Template) (member : base ∈ (h.decl m).bases)
    (target : String) (head : base.ctors.head? = some target) :
    lookup (generatedPrepared m c) h.name target = some base :=
  generated_lookup m c h ⟨base, [base]⟩ ((generatedRows_members m h).2 base member) target head

/-- All five finite operational lookup obligations hold for arbitrary machine
tables. This theorem proves the check; it does not assume that it passes. -/
theorem generated_implements (m : Machine states symbols) (c : Config states symbols) :
    Implements (generatedPrepared m c) m := by
  constructor
  · intro s a
    exact generated_lookup_base m c (.state s) (readBase m s a)
      (by simp [Head.decl, stateDecl]) (letterName a) (by simp [readBase])
  · intro s
    exact generated_lookup_base m c (.state s) (endBase m s)
      (by simp [Head.decl, stateDecl]) "End" (endBase_head m s)
  · exact generated_lookup_self m c .padding
  · exact generated_lookup_self m c .boundary
  · intro s next continuing
    exact generated_lookup_base m c .boundary _
      ((mem_turnBases m _).mpr ⟨s, next, continuing, rfl⟩) (turnName s) rfl

/-- The ordinary validator produces a certified initial query uniformly. -/
theorem generated_ready (m : Machine states symbols) (input : List (Fin symbols)) :
    Ready (generatedPrepared m ⟨m.initial, [], input⟩) m input :=
  ⟨generated_implements m _, rfl, rfl⟩

/-- The executable sweeper compiler, including its finite `Ready` check,
succeeds for every finite machine and every input tape. -/
theorem checkedCompile_generated (m : Machine states symbols) (input : List (Fin symbols)) :
    checkedCompile m input =
      .ok ⟨generatedPrepared m ⟨m.initial, [], input⟩, generated_ready m input⟩ := by
  simp only [checkedCompile, compile, program, prepare_generated_eq]
  simp only [bind, Except.bind, generated_ready, dite_true, pure]
  rfl

end Langlib.Computability.JavaGen.Sweep
