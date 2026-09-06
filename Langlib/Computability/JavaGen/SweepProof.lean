import Langlib.Computability.JavaGen.Sweep
import Langlib.Common.Divergence

/-! # Operational proof interface for the generated sweeping transducer

`Implements` states finite symbolic lookup obligations. The simulation below
uses the actual JavaGen evaluator, with positive costs for reading and turning.
Proving the generated validator result satisfies these obligations uniformly
is a separate compiler-validation theorem, not an assumed TC witness.
-/

namespace Langlib.Computability.JavaGen.Sweep
open Langlib.JavaGen Langlib.Common

/-- Ignore the chosen inheritance path, but retain the exact symbolic substitution. -/
def lookup (p : Prepared) (source target : String) : Option Template := do
  let (_, ancestors) ← p.closure.find? (·.1 == source)
  let a ← ancestors.find? (fun a => a.type.ctors.head? == some target)
  return a.type

structure Implements (p : Prepared) (m : Machine states symbols) : Prop where
  read : ∀ s a, lookup p (stateName s) (letterName a) = some (readBase m s a)
  boundary : ∀ s, lookup p (stateName s) "End" = some (endBase m s)
  padding : lookup p "ScanPad" "ScanPad" = some ⟨["ScanPad"], .var⟩
  endSelf : lookup p "End" "End" = some ⟨["End"], .var⟩
  turn : ∀ s next, m.boundary s = some next →
    lookup p "End" (turnName s) =
      some ⟨[turnName s, "ScanPad", stateName next, "End", "End"], .var⟩

instance (p : Prepared) (m : Machine states symbols) : Decidable (Implements p m) :=
  decidable_of_iff
    ((∀ s a, lookup p (stateName s) (letterName a) = some (readBase m s a)) ∧
     (∀ s, lookup p (stateName s) "End" = some (endBase m s)) ∧
     lookup p "ScanPad" "ScanPad" = some ⟨["ScanPad"], .var⟩ ∧
     lookup p "End" "End" = some ⟨["End"], .var⟩ ∧
     (∀ s next, m.boundary s = some next → lookup p "End" (turnName s) =
       some ⟨[turnName s, "ScanPad", stateName next, "End", "End"], .var⟩))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩,
     fun h => ⟨h.read, h.boundary, h.padding, h.endSelf, h.turn⟩⟩

/-- The certificate covers lookup behavior and the actual runner's initial query. -/
def Ready (p : Prepared) (m : Machine states symbols) (input : List (Fin symbols)) : Prop :=
  Implements p m ∧ p.source.query = query ⟨m.initial, [], input⟩ ∧ p.source.answerSide = none

instance (p : Prepared) (m : Machine states symbols) (input : List (Fin symbols)) :
    Decidable (Ready p m input) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Finite checking certifies the full lower simulation premise for an emitted class table.
A uniform theorem that generation never fails remains a separate obligation. -/
def checkedCompile (m : Machine states symbols) (input : List (Fin symbols)) :
    Except String { p : Prepared // Ready p m input } := do
  let p ← compile m input
  if h : Ready p m input then return ⟨p, h⟩
  else throw "sweeper compiler: generated symbolic lookup or initialization check failed"

private theorem resolve_lookup {p : Prepared} {source target : String} {t : Template}
    (h : lookup p source target = some t) (arg : Ty) :
    ∃ path, p.resolve (source :: arg) (some target) = some (t.instantiate arg, path) := by
  cases hc : p.closure.find? (·.1 == source) with
  | none => simp [lookup, hc] at h
  | some entry =>
    rcases entry with ⟨name, ancestors⟩
    cases ha : ancestors.find? (fun a => a.type.ctors.head? == some target) with
    | none => simp [lookup, hc, ha] at h
    | some ancestor =>
      have ht : ancestor.type = t := by simpa [lookup, hc, ha] using h
      exact ⟨ancestor.path.map (·.instantiate arg), by simp [Prepared.resolve, hc, ha, ht]⟩

/-- An exact sequence of continuing query steps; every constructor consumes fuel. -/
inductive Moves (p : Prepared) : Nat → Query → Query → Prop where
  | refl (q) : Moves p 0 q q
  | next {n q q' q''} (frame) (step : Langlib.JavaGen.step p q = .next frame q')
      (rest : Moves p n q' q'') : Moves p (n + 1) q q''

private theorem next_lookup {p : Prepared} {source target : String} {arg rhs body : Ty}
    {t : Template} (h : lookup p source target = some t)
    (ht : t.instantiate arg = target :: body) :
    ∃ frame, Langlib.JavaGen.step p ⟨source :: arg, target :: rhs⟩ =
      .next frame ⟨rhs, body⟩ := by
  obtain ⟨path, hp⟩ := resolve_lookup h arg
  refine ⟨⟨⟨source :: arg, target :: rhs⟩, path⟩, ?_⟩
  simp only [Langlib.JavaGen.step, List.head?_cons, hp, ht]

/-- Any finite written word, including deletion, costs exactly two query steps. -/
theorem read_moves {m : Machine states symbols} {p : Prepared} (h : Implements p m)
    (s : Fin states) (a : Fin symbols) (left right : List (Fin symbols)) :
    Moves p 2 (query ⟨s, left, a :: right⟩)
      (query ⟨(m.transition s a).1, (m.transition s a).2.reverse ++ left, right⟩) := by
  obtain ⟨f, hf⟩ := next_lookup (h.read s a)
    (arg := tape left) (rhs := "ScanPad" :: tape right)
    (body := "ScanPad" :: stateName (m.transition s a).1 ::
      pad (m.transition s a).2.reverse ++ tape left) (by
        simp [readBase, Template.instantiate])
  obtain ⟨g, hg⟩ := next_lookup h.padding
    (arg := tape right)
    (rhs := stateName (m.transition s a).1 :: pad (m.transition s a).2.reverse ++ tape left)
    (body := tape right) (by simp [Template.instantiate])
  have segment := Moves.next f hf (Moves.next g hg (.refl _))
  simpa [query, tape, pad, List.append_assoc] using segment

/-- Turning swaps the two tape sides in exactly three continuing steps. -/
theorem turn_moves {m : Machine states symbols} {p : Prepared} (h : Implements p m)
    (s next : Fin states) (hb : m.boundary s = some next) (left : List (Fin symbols)) :
    Moves p 3 (query ⟨s, left, []⟩) (query ⟨next, [], left⟩) := by
  obtain ⟨f, hf⟩ := next_lookup (h.boundary s)
    (arg := tape left) (rhs := ["End"])
    (body := turnName s :: "ScanPad" :: tape left)
    (by simp [endBase, hb, Template.instantiate])
  obtain ⟨g, hg⟩ := next_lookup (h.turn s next hb)
    (arg := []) (rhs := "ScanPad" :: tape left)
    (body := ["ScanPad", stateName next, "End", "End"])
    (by simp [Template.instantiate])
  obtain ⟨k, hk⟩ := next_lookup h.padding
    (arg := tape left) (rhs := [stateName next, "End", "End"])
    (body := tape left) (by simp [Template.instantiate])
  apply Moves.next f
  · simpa [query, tape, pad] using hf
  apply Moves.next g hg
  apply Moves.next k
  · simpa [query, tape, pad] using hk
  exact .refl _

/-- The three terminal queries are ordinary evaluator steps, not decoder conventions. -/
theorem halt_exec {m : Machine states symbols} {p : Prepared} (h : Implements p m)
    (s : Fin states) (hb : m.boundary s = none) (left : List (Fin symbols))
    (history : List Frame) :
    (exec p 3 ⟨query ⟨s, left, []⟩, history⟩).2 = .halted := by
  obtain ⟨f, hf⟩ := next_lookup (h.boundary s)
    (arg := tape left) (rhs := ["End"]) (body := ["End"])
    (by simp [endBase, hb, Template.instantiate])
  obtain ⟨g, hg⟩ := next_lookup h.endSelf
    (arg := []) (rhs := []) (body := []) (by simp [Template.instantiate])
  have hf' : Langlib.JavaGen.step p (query ⟨s, left, []⟩) =
      .next f ⟨["End"], ["End"]⟩ := by simpa [query, tape, pad] using hf
  simp only [exec, hf', hg]
  rfl

/-- Query segments lift to the real evaluator, retaining every intervening frame. -/
theorem Moves.exec {p : Prepared} {n : Nat} {q q' : Query} (h : Moves p n q q')
    (history : List Frame) :
    ∃ history', ∀ fuel, Langlib.JavaGen.exec p (n + fuel) ⟨q, history⟩ =
      Langlib.JavaGen.exec p fuel ⟨q', history'⟩ := by
  induction h generalizing history with
  | refl q => exact ⟨history, by intro fuel; simp only [Nat.zero_add]⟩
  | next frame hs _ ih =>
    obtain ⟨history', hh⟩ := ih (frame :: history)
    refine ⟨history', fun fuel => ?_⟩
    rw [Nat.add_right_comm _ 1 fuel, Langlib.JavaGen.exec, hs]
    exact hh fuel

/-- A continuing source transition has strictly positive target cost. -/
theorem advance_moves {m : Machine states symbols} {p : Prepared} (h : Implements p m)
    {c c' : Config states symbols} (hs : advance m c = some c') :
    ∃ n, 0 < n ∧ Moves p n (query c) (query c') := by
  rcases c with ⟨s, left, right⟩
  cases right with
  | cons a rest =>
    simp only [advance, Option.some.injEq] at hs
    subst c'
    exact ⟨2, by omega, read_moves h s a left rest⟩
  | nil =>
    cases hb : m.boundary s with
    | none => simp [advance, hb] at hs
    | some next =>
      simp only [advance, hb, Option.map_some, Option.some.injEq] at hs
      subst c'
      exact ⟨3, by omega, turn_moves h s next hb left⟩

/-- Finite source execution, including its zero-step prefix. -/
inductive Steps (m : Machine states symbols) : Config states symbols → Config states symbols → Prop where
  | refl (c) : Steps m c c
  | next {c c' c''} (step : advance m c = some c') (rest : Steps m c' c'') : Steps m c c''

/-- Every halting source run has a normally halting execution of the actual target. -/
theorem halting_simulation {m : Machine states symbols} {p : Prepared} (h : Implements p m)
    {c final : Config states symbols} (run : Steps m c final)
    (halt : advance m final = none) :
    ∃ fuel, ∀ history, (Langlib.JavaGen.exec p fuel ⟨query c, history⟩).2 = .halted := by
  induction run with
  | refl c =>
    rcases c with ⟨s, left, right⟩
    cases right with
    | cons a rest => simp [advance] at halt
    | nil =>
      have hb : m.boundary s = none := by
        cases hs : m.boundary s <;> simp_all [advance]
      exact ⟨3, halt_exec h s hb left⟩
  | next hs _ ih =>
    obtain ⟨cost, _, hm⟩ := advance_moves h hs
    obtain ⟨fuel, hf⟩ := ih halt
    refine ⟨cost + fuel, fun history => ?_⟩
    obtain ⟨history', hh⟩ := hm.exec history
    rw [hh]
    exact hf history'

/-- Any invariant that keeps the sweeper moving forces target exhaustion at every fuel.
The target invariant permits arbitrary proof history; decoding plays no role. -/
theorem divergence_simulation {m : Machine states symbols} {p : Prepared} (h : Implements p m)
    (I : Config states symbols → Prop)
    (progress : ∀ c, I c → ∃ c', advance m c = some c' ∧ I c')
    (c : Config states symbols) (hc : I c) (fuel : Nat) (history : List Frame) :
    (Langlib.JavaGen.exec p fuel ⟨query c, history⟩).2 = .outOfFuel := by
  let J : State → Prop := fun st => ∃ c, I c ∧ st.query = query c
  apply outOfFuel_of_progress (Langlib.JavaGen.exec p) Prod.snd
    (fun _ => rfl) (exec_stable p) J ?_ fuel ⟨query c, history⟩ ⟨c, hc, rfl⟩
  intro st hs
  obtain ⟨d, hd, hq⟩ := hs
  obtain ⟨d', hstep, hd'⟩ := progress d hd
  obtain ⟨cost, hpos, hm⟩ := advance_moves h hstep
  obtain ⟨history', hh⟩ := hm.exec st.history
  refine ⟨⟨query d', history'⟩, ⟨cost, hpos, ?_⟩, d', hd', rfl⟩
  intro f
  cases st with
  | mk q history =>
    simp only at hq
    subst q
    exact hh f

/-- A successful certifying compilation preserves source halting in the public evaluator. -/
theorem ready_halting {m : Machine states symbols} {input : List (Fin symbols)}
    (compiled : { p : Prepared // Ready p m input }) {final : Config states symbols}
    (run : Steps m ⟨m.initial, [], input⟩ final) (halt : advance m final = none) :
    ∃ fuel, (evalPrepared compiled.val fuel).exit = .halted := by
  obtain ⟨fuel, hf⟩ := halting_simulation compiled.property.1 run halt
  refine ⟨fuel, ?_⟩
  simpa [evalPrepared, evalProg, compiled.property.2.1, compiled.property.2.2, result] using hf []

/-- The same compiled artifact preserves continuing source invariants at every target fuel. -/
theorem ready_divergence {m : Machine states symbols} {input : List (Fin symbols)}
    (compiled : { p : Prepared // Ready p m input }) (I : Config states symbols → Prop)
    (progress : ∀ c, I c → ∃ c', advance m c = some c' ∧ I c')
    (initial : I ⟨m.initial, [], input⟩) (fuel : Nat) :
    (evalPrepared compiled.val fuel).exit = .outOfFuel := by
  have hf := divergence_simulation compiled.property.1 I progress _ initial fuel []
  simpa [evalPrepared, evalProg, compiled.property.2.1, compiled.property.2.2, result] using hf

end Langlib.Computability.JavaGen.Sweep
