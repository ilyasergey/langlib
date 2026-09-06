import Langlib.Computability.JavaGen.ValidationProof

/-! # Total validation of generated sweeping programs

The helpers below expose the ordinary validator's loops for induction.
`prepare_eq` checks their connection to the executable implementation by
reflexivity; they are not a replacement compiler or a second validator.
-/

open private walk checkNames from Langlib.Languages.JavaGen.Validation

namespace Langlib.Computability.JavaGen.Sweep
open Langlib.JavaGen

private def validateBases (index : Std.TreeMap String Decl) (name : String)
    (bases : List Template) (seen : Std.TreeMap (Option String) Unit) : Except String (Std.TreeMap (Option String) Unit) :=
  forIn bases seen fun base direct => do
    checkNames index base.ctors
    if base.tail == .var && base.ctors.length % 2 != 1 then
      throw s!"'{name}': variable superclass must have odd constructor depth"
    let head := base.ctors.head?
    if direct.contains head then throw s!"'{name}': repeated direct superclass"
    pure (.yield (direct.insert head ()))

private def validateClasses (index : Std.TreeMap String Decl) (classes : List Decl)
    (seen : Std.TreeMap String Unit) : Except String (Std.TreeMap String Unit) :=
  forIn classes seen fun d seen => do
    unless validName d.name do throw s!"invalid constructor name '{d.name}'"
    if seen.contains d.name then throw s!"duplicate constructor '{d.name}'"
    let seen := seen.insert d.name ()
    let _ ← validateBases index d.name d.bases {}
    pure (.yield seen)

private def uniquePaths (name : String) (paths : List Ancestor)
    (initial : List Ancestor × Std.TreeMap (Option String) Ancestor) :
    Except String (List Ancestor × Std.TreeMap (Option String) Ancestor) :=
  forIn paths initial fun a (unique, byHead) => do
    match byHead[a.type.ctors.head?]? with
    | none => pure (.yield (a :: unique, byHead.insert a.type.ctors.head? a))
    | some previous =>
      if previous.type != a.type then
        throw s!"'{name}': multiple instantiation of '{a.type.ctors.headD "Z"}'"
      pure (.yield (unique, byHead))

private def closeNames (index : Std.TreeMap String Decl) (budget : Nat) (names : List String)
    (initial : List (String × List Ancestor)) : Except String (List (String × List Ancestor)) :=
  forIn names initial fun name closure => do
    let paths ← walk index budget [] ⟨[name], .var⟩ []
    let (unique, _) ← uniquePaths name paths ([], {})
    pure (.yield ((name, unique.reverse) :: closure))

private theorem prepare_eq (m : Machine states symbols) (c : Config states symbols) :
    prepare (programAt m c) = (do
      let _ ← validateClasses (declarationIndex m) (declarations m) {}
      checkNames (declarationIndex m) (query c).lhs
      checkNames (declarationIndex m) (query c).rhs
      let closure ← closeNames (declarationIndex m)
        (((declarations m).map Decl.name).length + 1) ((declarations m).map Decl.name) []
      return { source := programAt m c, closure := closure.reverse }) := by
  rfl

private theorem ok_bind {α β : Type} (a : α) (f : α → Except String β) :
    (Except.ok a >>= f) = f a := rfl

private theorem validateBases_ok (m : Machine states symbols) (d : Decl)
    (hd : d ∈ declarations m) (bases : List Template) (subset : bases ⊆ d.bases)
    (distinct : (bases.map (fun t => t.ctors.head?)).Nodup)
    (seen : Std.TreeMap (Option String) Unit)
    (fresh : ∀ b ∈ bases, seen.contains b.ctors.head? = false) :
    ∃ final, validateBases (declarationIndex m) d.name bases seen = .ok final := by
  induction bases generalizing seen with
  | nil => exact ⟨seen, rfl⟩
  | cons b rest ih =>
    have valid := declaration_bases_valid m d hd b (subset (by simp))
    have names := checkNames_ok m b.ctors valid.1
    have parity : (b.tail == .var && b.ctors.length % 2 != 1) = false := by
      cases tail : b.tail with
      | zero => rfl
      | var => rw [valid.2 tail]; rfl
    have freshB := fresh b (by simp)
    have noDup := List.nodup_cons.mp distinct
    have freshRest : ∀ t ∈ rest, (seen.insert b.ctors.head? ()).contains t.ctors.head? = false := by
      intro t ht
      have ne : b.ctors.head? ≠ t.ctors.head? := by
        intro eq
        exact noDup.1 (List.mem_map.mpr ⟨t, ht, eq.symm⟩)
      simp [Std.TreeMap.contains_insert, ne, fresh t (by simp [ht])]
    obtain ⟨final, tail⟩ := ih (fun t ht => subset (by simp [ht])) noDup.2 _ freshRest
    refine ⟨final, ?_⟩
    simpa only [validateBases, List.forIn_cons, names, ok_bind, parity, Bool.false_eq_true,
      ite_false, pure_bind, freshB] using tail

private theorem validateClasses_ok (m : Machine states symbols) (classes : List Decl)
    (subset : classes ⊆ declarations m) (distinct : (classes.map Decl.name).Nodup)
    (seen : Std.TreeMap String Unit) (fresh : ∀ d ∈ classes, seen.contains d.name = false) :
    ∃ final, validateClasses (declarationIndex m) classes seen = .ok final := by
  induction classes generalizing seen with
  | nil => exact ⟨seen, rfl⟩
  | cons d rest ih =>
    have member := subset (by simp : d ∈ d :: rest)
    have valid := declarations_validName m d member
    have freshD := fresh d (by simp)
    obtain ⟨direct, bases⟩ := validateBases_ok m d member d.bases (by intro t ht; exact ht)
      (declaration_bases_nodup m d member) {} (by simp)
    have noDup := List.nodup_cons.mp distinct
    have freshRest : ∀ t ∈ rest, (seen.insert d.name ()).contains t.name = false := by
      intro t ht
      have ne : d.name ≠ t.name := by
        intro eq
        exact noDup.1 (List.mem_map.mpr ⟨t, ht, eq.symm⟩)
      simp [Std.TreeMap.contains_insert, ne, fresh t (by simp [ht])]
    obtain ⟨final, tail⟩ := ih (fun t ht => subset (by simp [ht])) noDup.2 _ freshRest
    refine ⟨final, ?_⟩
    simpa only [validateClasses, List.forIn_cons, valid, freshD, ite_true, Bool.false_eq_true,
      ite_false, pure_bind, bases, ok_bind] using tail

/-- Distinct heads make the actual diamond filter retain the whole walk,
in its original order after the validator reverses its accumulator. -/
private theorem uniquePaths_ok (name : String) (paths : List Ancestor)
    (distinct : (paths.map (fun a => a.type.ctors.head?)).Nodup)
    (unique : List Ancestor) (seen : Std.TreeMap (Option String) Ancestor)
    (fresh : ∀ a ∈ paths, seen[a.type.ctors.head?]? = none) :
    ∃ final, uniquePaths name paths (unique, seen) = .ok (paths.reverse ++ unique, final) := by
  induction paths generalizing unique seen with
  | nil => exact ⟨seen, rfl⟩
  | cons a rest ih =>
    have freshA := fresh a (by simp)
    have noDup := List.nodup_cons.mp distinct
    have freshRest : ∀ b ∈ rest, (seen.insert a.type.ctors.head? a)[b.type.ctors.head?]? = none := by
      intro b hb
      have ne : a.type.ctors.head? ≠ b.type.ctors.head? := by
        intro eq
        exact noDup.1 (List.mem_map.mpr ⟨b, hb, eq.symm⟩)
      simp [Std.TreeMap.getElem?_insert, ne, fresh b (by simp [hb])]
    obtain ⟨final, tail⟩ := ih noDup.2 (a :: unique) _ freshRest
    refine ⟨final, ?_⟩
    simpa only [uniquePaths, List.forIn_cons, freshA, pure_bind, List.reverse_cons,
      List.append_assoc, List.singleton_append] using tail

private theorem closeNames_ok (m : Machine states symbols) (names : List String)
    (subset : names ⊆ (declarations m).map Decl.name) (initial : List (String × List Ancestor)) :
    closeNames (declarationIndex m) (((declarations m).map Decl.name).length + 1)
      names initial = .ok ((names.map (fun n => (n, generatedRows m n))).reverse ++ initial) := by
  induction names generalizing initial with
  | nil => rfl
  | cons name rest ih =>
    have member := subset (by simp : name ∈ name :: rest)
    rw [declaration_names] at member
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp member
    have walkOk := generatedRows_walk m h
    obtain ⟨index, unique⟩ := uniquePaths_ok h.name (generatedRows m h.name)
      (generatedRows_nodup m h) [] {} (by simp)
    have tail := ih (fun n hn => subset (by simp [hn])) ((h.name, generatedRows m h.name) :: initial)
    simpa only [closeNames, List.forIn_cons, walkOk, ok_bind, unique, List.append_nil,
      List.reverse_reverse, pure_bind, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append] using tail

/-- An explicit description of the ordinary validator's output. Every row
comes from its own inheritance traversal, retaining the source order. -/
def generatedPrepared (m : Machine states symbols) (c : Config states symbols) : Prepared :=
  { source := programAt m c
    closure := ((declarations m).map Decl.name).map (fun n => (n, generatedRows m n)) }

/-- The ordinary validator returns exactly this generated closure. -/
theorem prepare_generated_eq (m : Machine states symbols) (c : Config states symbols) :
    prepare (programAt m c) = .ok (generatedPrepared m c) := by
  rw [prepare_eq]
  obtain ⟨seen, classes⟩ := validateClasses_ok m (declarations m) (by intro d hd; exact hd)
    (declarations_nodup m) {} (by simp)
  have closed := closeNames_ok m ((declarations m).map Decl.name) (by intro n hn; exact hn) []
  have lhs := checkNames_ok m (query c).lhs (query_declared m c).1
  have rhs := checkNames_ok m (query c).rhs (query_declared m c).2
  rw [classes, ok_bind, lhs, ok_bind, rhs, ok_bind, closed, ok_bind]
  simp only [List.append_nil, List.reverse_reverse]
  rfl

/-- Every generated program passes the ordinary validator, for arbitrary
finite machine tables and tape contents. No halting assumption or subtype
search budget occurs in this theorem. -/
theorem prepare_generated (m : Machine states symbols) (c : Config states symbols) :
    ∃ p, prepare (programAt m c) = .ok p :=
  ⟨generatedPrepared m c, prepare_generated_eq m c⟩

/-- The unchecked sweeper compiler is total; the finite `Ready` check in
`checkedCompile` is proved separately in GeneratedReady. -/
theorem compile_generated (m : Machine states symbols) (input : List (Fin symbols)) :
    ∃ p, compile m input = .ok p :=
  prepare_generated m ⟨m.initial, [], input⟩

end Langlib.Computability.JavaGen.Sweep
