import Langlib.Computability.JavaGen.GeneratedTable
import Batteries.Tactic.OpenPrivate
import Std.Data.TreeMap.Lemmas

/-! # Connecting generated declarations to the executable validator

Use the same indexed lookup and inheritance traversal as `prepare`.
The structural table invariants are independent of the index representation.
-/

open private walk checkNames from Langlib.Languages.JavaGen.Validation

namespace Langlib.Computability.JavaGen.Sweep
open Langlib.JavaGen

def declarationIndex (m : Machine states symbols) : Std.TreeMap String Decl :=
  Std.TreeMap.ofList ((declarations m).map fun d => (d.name, d))

theorem declarationIndex_lookup (m : Machine states symbols) (h : Head states symbols) :
    (declarationIndex m)[h.name]? = some (h.decl m) := by
  apply Std.TreeMap.getElem?_ofList_of_mem (k := h.name) (by simp)
  · simpa [List.pairwise_map, List.Nodup] using declarations_nodup m
  · apply List.mem_map.mpr
    refine ⟨h.decl m, ?_, by simp⟩
    rw [declarations_eq_heads]
    exact List.mem_map.mpr ⟨h, mem_heads h, rfl⟩

theorem declarationIndex_contains (m : Machine states symbols) (name : String)
    (declared : name ∈ (declarations m).map Decl.name) :
    (declarationIndex m).contains name = true := by
  simpa [declarationIndex, Std.TreeMap.contains_ofList, List.map_map, Function.comp_def] using declared

/-- The validator accepts a word consisting of declared constructor names. -/
theorem checkNames_ok (m : Machine states symbols) (word : List String)
    (declared : ∀ name ∈ word, name ∈ (declarations m).map Decl.name) :
    checkNames (declarationIndex m) word = .ok () := by
  unfold checkNames
  induction word with
  | nil => rfl
  | cons name rest ih =>
    have hn := declarationIndex_contains m name (declared name (by simp))
    have tail := ih (by intro n hn; exact declared n (by simp [hn]))
    simpa only [List.forIn_cons, hn, ite_true, pure_bind] using tail

/-- Leaf declarations terminate inheritance traversal immediately, for every
type argument and path, without consuming any subtype-search budget. -/
theorem walk_leaf (m : Machine states symbols) (h : Head states symbols)
    (leaf : (h.decl m).bases = []) (fuel : Nat) (seen : List String)
    (fresh : h.name ∉ seen) (arg : Template) (path : List Template) :
    walk (declarationIndex m) (fuel + 1) seen ⟨h.name :: arg.ctors, arg.tail⟩ path =
      .ok [⟨⟨h.name :: arg.ctors, arg.tail⟩, path⟩] := by
  simp [walk, declarationIndex_lookup, fresh, leaf]
  rfl


/-- The superclass loop in `walk`, with its accumulated prefix explicit. -/
def walkBases (index : Std.TreeMap String Decl) (fuel : Nat) (seen : List String)
    (arg : Template) (path : List Template) (bases : List Template) (initial : List Ancestor) :
    Except String (List Ancestor) :=
  forIn bases initial fun base acc => do
    let next := base.subst arg
    let rows ← walk index fuel seen next (path ++ [next])
    pure (.yield (rows.reverse ++ acc))

theorem walk_node (m : Machine states symbols) (h : Head states symbols)
    (fuel : Nat) (seen : List String) (fresh : h.name ∉ seen)
    (arg : Template) (path : List Template) :
    walk (declarationIndex m) (fuel + 1) seen ⟨h.name :: arg.ctors, arg.tail⟩ path =
      List.reverse <$> walkBases (declarationIndex m) fuel (h.name :: seen) arg path
        (h.decl m).bases [⟨⟨h.name :: arg.ctors, arg.tail⟩, path⟩] := by
  cases arg
  simp [walk, declarationIndex_lookup, fresh, walkBases]

private theorem except_ok_bind {α β : Type} (a : α) (f : α → Except String β) :
    (Except.ok a >>= f) = f a := rfl

/-- Pointwise successful recursive calls make the validator's superclass
loop succeed, retaining exactly the emitted order and inheritance paths. -/
theorem walkBases_ok (index : Std.TreeMap String Decl) (fuel : Nat) (seen : List String)
    (arg : Template) (path : List Template) (bases : List Template) (rows : Template → List Ancestor)
    (success : ∀ base ∈ bases,
      walk index fuel seen (base.subst arg) (path ++ [base.subst arg]) = .ok (rows base))
    (initial : List Ancestor) :
    walkBases index fuel seen arg path bases initial = .ok ((bases.flatMap rows).reverse ++ initial) := by
  induction bases generalizing initial with
  | nil => simp [walkBases]; rfl
  | cons base rest ih =>
    have first := success base (by simp)
    have later := ih (by intro b hb; exact success b (by simp [hb])) ((rows base).reverse ++ initial)
    simpa only [walkBases, List.forIn_cons, first, except_ok_bind, pure_bind,
      List.flatMap_cons, List.reverse_append, List.append_assoc] using later

/-- Every visited name has strictly greater head rank than the next lookup. -/
def Above (seen : List String) (h : Head states symbols) : Prop :=
  ∀ k : Head states symbols, k.name ∈ seen → h.rank < k.rank

theorem Above.fresh {seen : List String} {h : Head states symbols} (above : Above seen h) :
    h.name ∉ seen := by
  intro mem
  have := above h mem
  omega

theorem Above.descend {seen : List String} {h k : Head states symbols}
    (above : Above seen h) (rank : k.rank < h.rank) : Above (h.name :: seen) k := by
  intro j mem
  rcases List.mem_cons.mp mem with eq | mem
  · have : j = h := head_name_injective eq
    simpa [this] using rank
  · have := above j mem
    omega


private theorem directBase_head (m : Machine states symbols) (h : Head states symbols)
    (base : Template) (member : base ∈ (h.decl m).bases) :
    ∃ k, k ∈ directHeads m h ∧ base.ctors.head? = some k.name := by
  have hm : base.ctors.head? ∈ (h.decl m).bases.map (fun t => t.ctors.head?) :=
    List.mem_map.mpr ⟨base, member, rfl⟩
  rw [directHeads_eq] at hm
  obtain ⟨k, hk, eq⟩ := List.mem_map.mp hm
  exact ⟨k, hk, eq.symm⟩

private theorem subst_preserves_head (base arg : Template) (name : String)
    (head : base.ctors.head? = some name) : (base.subst arg).ctors.head? = some name := by
  rcases base with ⟨ctors, tail⟩
  cases ctors with
  | nil => simp at head
  | cons first rest =>
    simp only [List.head?_cons, Option.some.injEq] at head
    subst first
    cases tail <;> simp [Template.subst]

private theorem template_eq_head (t : Template) (name : String) (head : t.ctors.head? = some name) :
    t = ⟨name :: t.ctors.tail, t.tail⟩ := by
  rcases t with ⟨ctors, tail⟩
  cases ctors with
  | nil => simp at head
  | cons first rest =>
    simp only [List.head?_cons, Option.some.injEq] at head
    subst first
    rfl

/-- Every recursive head traversal of a generated table succeeds once the
validator's budget exceeds its rank. The hypothesis concerns inheritance
rank, not whether the simulated machine halts. -/
theorem walk_generated (m : Machine states symbols) (h : Head states symbols)
    (fuel : Nat) (enough : h.rank < fuel) (seen : List String) (above : Above seen h)
    (arg : Template) (path : List Template) :
    ∃ rows, walk (declarationIndex m) fuel seen ⟨h.name :: arg.ctors, arg.tail⟩ path = .ok rows ∧
      rows.map (fun a => a.type.ctors.head?) = (descendants m h).map (fun k => some k.name) ∧
      (⟨⟨h.name :: arg.ctors, arg.tail⟩, path⟩ : Ancestor) ∈ rows ∧
      ∀ base ∈ (h.decl m).bases,
        (⟨base.subst arg, path ++ [base.subst arg]⟩ : Ancestor) ∈ rows := by
  classical
  induction fuel generalizing h seen arg path with
  | zero => omega
  | succ fuel ih =>
    rw [walk_node m h fuel seen above.fresh arg path]
    have children : ∀ base ∈ (h.decl m).bases,
        ∃ rows, walk (declarationIndex m) fuel (h.name :: seen) (base.subst arg)
          (path ++ [base.subst arg]) = .ok rows ∧
          rows.map (fun a => a.type.ctors.head?) = descendantNames m base.ctors.head? ∧
          (⟨base.subst arg, path ++ [base.subst arg]⟩ : Ancestor) ∈ rows := by
      intro base member
      obtain ⟨k, hk, head⟩ := directBase_head m h base member
      have rank := directHeads_rank m h k hk
      have nextHead := subst_preserves_head base arg k.name head
      have shape := template_eq_head (base.subst arg) k.name nextHead
      obtain ⟨rows, success, names, self, _⟩ := ih k (by omega) (h.name :: seen) (above.descend rank)
        ⟨(base.subst arg).ctors.tail, (base.subst arg).tail⟩ (path ++ [base.subst arg])
      refine ⟨rows, ?_, ?_, ?_⟩
      · simpa only [← shape] using success
      · simpa only [head, descendantNames_name] using names
      · simpa only [← shape] using self
    let rows : Template → List Ancestor := fun base =>
      if member : base ∈ (h.decl m).bases then (children base member).choose else []
    have success : ∀ base ∈ (h.decl m).bases,
        walk (declarationIndex m) fuel (h.name :: seen) (base.subst arg)
          (path ++ [base.subst arg]) = .ok (rows base) := by
      intro base member
      simpa only [rows, dif_pos member] using (children base member).choose_spec.1
    rw [walkBases_ok _ _ _ _ _ _ rows success]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.reverse_reverse, List.singleton_append, List.map_cons, List.head?_cons,
        descendants_unfold m h]
      congr 1
      calc
        ((h.decl m).bases.flatMap rows).map (fun a => a.type.ctors.head?) =
            (h.decl m).bases.flatMap (fun base => descendantNames m base.ctors.head?) := by
          rw [List.map_flatMap]
          apply List.flatMap_congr
          intro base member
          simpa only [rows, dif_pos member] using (children base member).choose_spec.2.1
        _ = ((h.decl m).bases.map (fun t => t.ctors.head?)).flatMap (descendantNames m) := by
          rw [List.flatMap_map]
        _ = ((directHeads m h).flatMap (descendants m)).map (fun k => some k.name) := by
          rw [directHeads_eq, List.flatMap_map, List.map_flatMap]
          simp only [descendantNames_name]
    · simp
    · intro base member
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.reverse_reverse, List.singleton_append, List.mem_cons]
      right
      apply List.mem_flatMap.mpr
      refine ⟨base, member, ?_⟩
      simpa only [rows, dif_pos member] using (children base member).choose_spec.2.2

/-- The actual validator budget, number of class names plus one, suffices
uniformly for every generated root declaration. -/
theorem generated_walk_budget (m : Machine states symbols) (h : Head states symbols) :
    ∃ rows, walk (declarationIndex m) (((declarations m).map Decl.name).length + 1) []
      ⟨[h.name], .var⟩ [] = .ok rows := by
  have enough : h.rank < ((declarations m).map Decl.name).length + 1 := by
    cases h <;> simp [Head.rank, declarations]
  obtain ⟨rows, success, _⟩ := walk_generated m h _ enough [] (by intro k hk; simp at hk) ⟨[], .var⟩ []
  exact ⟨rows, success⟩

/-- The actual closure walk succeeds with distinct ancestor heads. Thus its
result cannot contain incompatible symbolic instantiations of one head. -/
theorem generated_walk_coherent (m : Machine states symbols) (h : Head states symbols) :
    ∃ rows, walk (declarationIndex m) (((declarations m).map Decl.name).length + 1) []
      ⟨[h.name], .var⟩ [] = .ok rows ∧
      (rows.map (fun a => a.type.ctors.head?)).Nodup := by
  have enough : h.rank < ((declarations m).map Decl.name).length + 1 := by
    cases h <;> simp [Head.rank, declarations]
  obtain ⟨rows, success, names, _, _⟩ := walk_generated m h _ enough []
    (by intro k hk; simp at hk) ⟨[], .var⟩ []
  refine ⟨rows, success, ?_⟩
  rw [names]
  exact (descendants_nodup m h).map (by
    intro a b eq
    exact head_name_injective (Option.some.inj eq))

/-- Name the actual validator walk's result. The fallback is unreachable for
any declared generated head, as `generatedRows_walk` proves. -/
def generatedRows (m : Machine states symbols) (name : String) : List Ancestor :=
  (walk (declarationIndex m) (((declarations m).map Decl.name).length + 1) []
    ⟨[name], .var⟩ []).toOption.getD []

theorem generatedRows_walk (m : Machine states symbols) (h : Head states symbols) :
    walk (declarationIndex m) (((declarations m).map Decl.name).length + 1) []
      ⟨[h.name], .var⟩ [] = .ok (generatedRows m h.name) := by
  obtain ⟨rows, success⟩ := generated_walk_budget m h
  simp only [generatedRows, success, Except.toOption, Option.getD_some]

theorem generatedRows_nodup (m : Machine states symbols) (h : Head states symbols) :
    ((generatedRows m h.name).map (fun a => a.type.ctors.head?)).Nodup := by
  obtain ⟨rows, success, distinct⟩ := generated_walk_coherent m h
  simpa only [generatedRows, success, Except.toOption, Option.getD_some] using distinct

/-- The symbolic closure retains both reflexivity and every declared direct
superclass, with their actual inheritance paths. -/
theorem generatedRows_members (m : Machine states symbols) (h : Head states symbols) :
    (⟨⟨[h.name], .var⟩, []⟩ : Ancestor) ∈ generatedRows m h.name ∧
    ∀ base ∈ (h.decl m).bases, (⟨base, [base]⟩ : Ancestor) ∈ generatedRows m h.name := by
  have enough : h.rank < ((declarations m).map Decl.name).length + 1 := by
    cases h <;> simp [Head.rank, declarations]
  obtain ⟨rows, success, _, self, direct⟩ := walk_generated m h _ enough []
    (by intro k hk; simp at hk) ⟨[], .var⟩ []
  have identity : ∀ base : Template, base.subst ⟨[], .var⟩ = base := by
    rintro ⟨ctors, tail⟩
    cases tail <;> simp [Template.subst]
  simpa only [generatedRows, success, Except.toOption, Option.getD_some,
    identity, List.nil_append] using And.intro self direct

end Langlib.Computability.JavaGen.Sweep
