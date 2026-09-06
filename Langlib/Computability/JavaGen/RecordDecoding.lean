import Langlib.Computability.JavaGen.CounterCompiler
import Init.Data.List.SplitOn.Lemmas
import Mathlib.Data.List.Count

/-! # Reading the answer from ordinary proof-record bytes

The decoder selects the final control query independently of earlier history.
Whole constructor names are counted, so neighbouring numeric names do not alias.
-/

namespace Langlib.Computability.JavaGen.Record
open Langlib.JavaGen

abbrev countLine := CounterCompiler.countAnswerLine
abbrev decode := CounterCompiler.decodeOutput

theorem valid_char {n : String} (valid : validName n = true) {c : Char} (member : c ∈ n.toList) :
    identRest c = true := by
  unfold validName at valid
  split at valid
  · contradiction
  · rename_i first rest spelling
    simp only [Bool.and_eq_true] at valid
    rw [spelling] at member
    rcases List.mem_cons.mp member with rfl | member
    · simp [identRest, valid.1.1]
    · exact List.all_eq_true.mp valid.1.2 c member

theorem valid_excludes {n : String} (valid : validName n = true) {c : Char} (bad : identRest c = false) :
    c ∉ n.toList := by
  intro member
  have := valid_char valid member
  simp [bad] at this

theorem chain_chars (names : List String) (terminal : String) :
    (renderChain names terminal).toList =
      names.flatMap (fun n => n.toList ++ ['<']) ++ terminal.toList ++ List.replicate names.length '>' := by
  induction names with
  | nil => simp [renderChain]
  | cons n ns ih =>
    change (n ++ "<" ++ renderChain ns terminal ++ ">").toList = _
    simp [String.toList_append, ih, List.append_assoc, List.replicate_succ']

theorem split_heads (names : List String) (clean : ∀ n ∈ names, '<' ∉ n.toList) (tail : List Char) :
    ((names.flatMap (fun n => n.toList ++ ['<'])) ++ tail).splitOn '<' =
      names.map String.toList ++ tail.splitOn '<' := by
  induction names with
  | nil => simp
  | cons n ns ih =>
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append]
    rw [List.splitOn_append_cons_self_of_not_mem (clean n (by simp))]
    simp [ih (by intro m hm; exact clean m (by simp [hm]))]

theorem count_query_tail (k : Nat) :
    countLine (['Z'] ++ List.replicate k '>' ++ " <: End<End<Z>>".toList) = 0 := by
  change ((['Z'] ++ List.replicate k '>' ++ " <: End<End<Z>>".toList).splitOn '<').count _ = 0
  have shape : ['Z'] ++ List.replicate k '>' ++ " <: End<End<Z>>".toList =
      (['Z'] ++ List.replicate k '>' ++ " ".toList) ++ '<' :: ": End<End<Z>>".toList := by
    simp [List.append_assoc]
  rw [shape, List.splitOn_append_cons_self_of_not_mem (by simp)]
  simp [List.splitOn_cons_eq_if_modifyHead, List.splitOn_nil, List.modifyHead]

theorem count_query (names : List String) (valid : ∀ n ∈ names, validName n = true) :
    countLine (Ty.render names ++ " <: End<End<Z>>").toList = names.count "Letter_1" := by
  have clean : ∀ n ∈ names, '<' ∉ n.toList := by
    intro n hn
    exact valid_excludes (valid n hn) (by decide)
  unfold countLine CounterCompiler.countAnswerLine
  rw [String.toList_append, Ty.render, chain_chars]
  simp only [List.append_assoc]
  rw [split_heads names clean]
  rw [List.count_append]
  have tail := count_query_tail names.length
  change _ + countLine (['Z'] ++ List.replicate names.length '>' ++ " <: End<End<Z>>".toList) = _
  rw [tail, Nat.add_zero]
  exact List.count_map_of_injective names String.toList (fun _ _ h => String.toList_inj.mp h) _

theorem utf8_roundTrip (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  unfold String.fromUTF8?
  split
  · rfl
  · rename_i invalid
    exact False.elim (invalid s.isValidUTF8)

theorem chain_no_newline (names : List String) (valid : ∀ n ∈ names, validName n = true) :
    '\n' ∉ (Ty.render names).toList := by
  rw [Ty.render, chain_chars]
  simp only [List.mem_append, List.mem_flatMap, not_or, not_exists]
  refine ⟨⟨?_, by decide⟩, by simp⟩
  intro n hn
  exact (valid_excludes (valid n hn.1) (by decide)) (hn.2.resolve_right (by simp))

theorem query_no_newline (names : List String) (valid : ∀ n ∈ names, validName n = true) :
    '\n' ∉ (Ty.render names ++ " <: End<End<Z>>").toList := by
  simp only [String.toList_append, List.mem_append, not_or]
  exact ⟨chain_no_newline names valid, by decide⟩

theorem frame_ends_newline (frame : Frame) : ∃ before, frame.render = before ++ "\n" := by
  unfold Frame.render
  have paths : ∃ before, "\n" ++ String.join
      (frame.inheritance.map (fun t => "  via " ++ t.render ++ "\n")) = before ++ "\n" := by
    induction frame.inheritance using List.reverseRecOn with
    | nil => exact ⟨"", rfl⟩
    | append_singleton ts t ih =>
      refine ⟨"\n" ++ String.join (ts.map (fun t => "  via " ++ t.render ++ "\n")) ++
        "  via " ++ t.render, ?_⟩
      simp [String.append_assoc]
  obtain ⟨before, eq⟩ := paths
  exact ⟨frame.query.render ++ before, by simp only [String.append_assoc, ← eq]⟩

theorem history_ends_newline (frames : List Frame) :
    ∃ before, "accepted\n" ++ String.join (frames.map Frame.render) = before ++ "\n" := by
  induction frames using List.reverseRecOn with
  | nil => exact ⟨"accepted", rfl⟩
  | append_singleton fs f ih =>
    obtain ⟨before, eq⟩ := frame_ends_newline f
    refine ⟨"accepted\n" ++ String.join (fs.map Frame.render) ++ before, ?_⟩
    simp [eq, String.append_assoc]

/-- A terminal control line is selected independently of all earlier history. -/
theorem find_terminal_line (before query : String) (clean : '\n' ∉ query.toList)
    (state : "State_".toList.isPrefixOf query.toList = true) :
    (((before ++ "\n" ++ query ++
      "\n  via End<End<Z>>\nEnd<Z> <: End<Z>\nZ <: Z\n").toList).splitOn '\n').reverse.find?
      ("State_".toList.isPrefixOf ·) = some query.toList := by
  -- Re-express the fixed literal with `ofList` before normalizing its characters.
  -- Directly unfolding the UTF-8 iterator here produces a very large proof term.
  have chars : "\n  via End<End<Z>>\nEnd<Z> <: End<Z>\nZ <: Z\n".toList =
      ['\n', ' ', ' ', 'v', 'i', 'a', ' ', 'E', 'n', 'd', '<', 'E', 'n', 'd', '<', 'Z', '>', '>',
        '\n', 'E', 'n', 'd', '<', 'Z', '>', ' ', '<', ':', ' ', 'E', 'n', 'd', '<', 'Z', '>',
        '\n', 'Z', ' ', '<', ':', ' ', 'Z', '\n'] := by
    change (String.ofList ['\n', ' ', ' ', 'v', 'i', 'a', ' ', 'E', 'n', 'd', '<', 'E', 'n', 'd', '<', 'Z', '>', '>',
        '\n', 'E', 'n', 'd', '<', 'Z', '>', ' ', '<', ':', ' ', 'E', 'n', 'd', '<', 'Z', '>',
        '\n', 'Z', ' ', '<', ':', ' ', 'Z', '\n']).toList = _
    exact String.toList_ofList
  simp only [String.toList_append, chars, List.append_assoc]
  change ((before.toList ++ '\n' :: (query.toList ++ '\n' :: _)).splitOn '\n').reverse.find? _ = _
  rw [List.splitOn_append_cons_self, List.splitOn_append_cons_self_of_not_mem clean]
  simp only [List.reverse_append, List.reverse_cons, List.find?_append]
  have state' : ['S', 't', 'a', 't', 'e', '_'].isPrefixOf query.toList = true := state
  simp [List.splitOn_cons_eq_if_modifyHead, List.splitOn_nil, List.modifyHead,
    List.isPrefixOf, state']

/-- Decoding is independent of the earlier proof history. -/
theorem decode_terminal (history : List Frame) (names : List String)
    (valid : ∀ n ∈ names, validName n = true)
    (state : "State_".toList.isPrefixOf (Ty.render names ++ " <: End<End<Z>>").toList = true) :
    decode ("accepted\n" ++ String.join (history.reverse.map Frame.render) ++
      (Ty.render names ++ " <: End<End<Z>>") ++
      "\n  via End<End<Z>>\nEnd<Z> <: End<Z>\nZ <: Z\n").toUTF8 = some (names.count "Letter_1") := by
  obtain ⟨before, eq⟩ := history_ends_newline history.reverse
  have accepted : "accepted\n".toList.isPrefixOf
      ("accepted\n" ++ String.join (history.reverse.map Frame.render) ++
        (Ty.render names ++ " <: End<End<Z>>") ++
        "\n  via End<End<Z>>\nEnd<Z> <: End<Z>\nZ <: Z\n").toList = true := by
    simp [String.toList_append, List.append_assoc]
  unfold decode CounterCompiler.decodeOutput
  rw [utf8_roundTrip]
  simp only [bind, Option.bind, accepted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [eq, find_terminal_line before _ (query_no_newline names valid) state]
  simp only [pure, count_query names valid]

end Langlib.Computability.JavaGen.Record
