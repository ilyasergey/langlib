import Langlib.Computability.JavaGen.GeneratedReady
import Batteries.Tactic.OpenPrivate

/-! # Exact terminal frames and their ordinary UTF-8 output

The generated closure carries the actual inheritance paths, beyond the lookup
equations needed for control-state simulation. This fixes every trailing line
after the answer query, which lets the byte decoder identify it unambiguously.
-/

open private find_key from Langlib.Computability.JavaGen.GeneratedReady

namespace Langlib.Computability.JavaGen.Sweep
open Langlib.JavaGen Langlib.Common

theorem generated_resolve (m : Machine states symbols) (c : Config states symbols)
    (h : Head states symbols) (a : Ancestor) (member : a ∈ generatedRows m h.name)
    (target : String) (head : a.type.ctors.head? = some target) (arg : Ty) :
    (generatedPrepared m c).resolve (h.name :: arg) (some target) =
      some (a.type.instantiate arg, a.path.map (·.instantiate arg)) := by
  have root := find_key Prod.fst (generatedPrepared m c).closure
    (by simpa [generatedPrepared, List.map_map, Function.comp_def] using declarations_nodup m)
    (h.name, generatedRows m h.name)
    (List.mem_map.mpr ⟨h.name, head_declared m h, rfl⟩)
  have row := find_key (fun a : Ancestor => a.type.ctors.head?) (generatedRows m h.name)
    (generatedRows_nodup m h) a member
  simp only [head] at row
  simp only [Prepared.resolve, root, bind, Option.bind, row, pure]

def terminalFrames (s : Fin states) (left : List (Fin symbols)) : List Frame :=
  [⟨⟨[], []⟩, []⟩, ⟨⟨["End"], ["End"]⟩, []⟩,
    ⟨query ⟨s, left, []⟩, [["End", "End"]]⟩]

theorem exec_generated_halt (m : Machine states symbols) (c : Config states symbols)
    (s : Fin states) (halt : m.boundary s = none) (left : List (Fin symbols)) (history : List Frame) :
    exec (generatedPrepared m c) 3 ⟨query ⟨s, left, []⟩, history⟩ =
      (⟨⟨[], []⟩, terminalFrames s left ++ history⟩, .halted) := by
  have boundary := generated_resolve m c (.state s) ⟨endBase m s, [endBase m s]⟩
    ((generatedRows_members m (.state s)).2 _ (by simp [Head.decl, stateDecl]))
    "End" (endBase_head m s) (tape left)
  simp only [endBase, halt, Head.name, Template.instantiate, List.append_nil, List.map_cons,
    List.map_nil] at boundary
  have self := generated_resolve m c .boundary ⟨⟨["End"], .var⟩, []⟩
    (generatedRows_members m .boundary).1 "End" rfl []
  simp only [Head.name, Template.instantiate, List.append_nil, List.map_nil] at self
  have tape_nil : tape ([] : List (Fin symbols)) = ["End", "End"] := rfl
  simp only [exec, step, query, tape_nil, List.head?_cons, boundary, self]
  rfl

def terminalText (s : Fin states) (left : List (Fin symbols)) : String :=
  (query ⟨s, left, []⟩).render ++ "\n  via End<End<Z>>\nEnd<Z> <: End<Z>\nZ <: Z\n"

theorem terminalFrames_render (s : Fin states) (left : List (Fin symbols)) :
    String.join ((terminalFrames s left).reverse.map Frame.render) = terminalText s left := by
  simp only [terminalFrames, List.reverse_cons, List.reverse_nil,
    List.map_append, List.map_cons, List.map_nil, String.join_append, String.join_cons,
    String.join_nil, String.append_empty, Frame.render, terminalText]
  simp only [String.append_assoc]
  rfl

theorem generated_halt_output (m : Machine states symbols) (c : Config states symbols)
    (s : Fin states) (halt : m.boundary s = none) (left : List (Fin symbols)) (history : List Frame) :
    (result (exec (generatedPrepared m c) 3 ⟨query ⟨s, left, []⟩, history⟩)).output =
      ("accepted\n" ++ String.join (history.reverse.map Frame.render) ++ terminalText s left).toUTF8 := by
  rw [exec_generated_halt m c s halt left history]
  simp only [result, show (Exit.halted == Exit.halted) = true from rfl, ite_true,
    List.reverse_append, List.map_append, String.join_append, terminalFrames_render,
    String.append_assoc]

end Langlib.Computability.JavaGen.Sweep
