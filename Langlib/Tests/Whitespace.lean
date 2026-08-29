import Langlib.Common.TestHarness
import Langlib.Languages.Whitespace.Semantics

/-!
Golden tests for the Whitespace interpreter: every example program,
arithmetic (including floor division and modulo on negatives), heap access,
`copy`/`slide` edge cases, subroutines, conditional jumps, both I/O
channels, EOF behaviour, runtime errors, parse errors, and divergence.

Most inline programs are built from the AST and rendered with
`Prog.render`, which keeps them readable and exercises the renderer/parser
round trip; the parse-error cases are raw token strings by necessity.
-/

namespace Langlib.Tests.Whitespace

open Langlib.Common
open Langlib.Whitespace (Instr Prog run)

private def ex (f : String) : Source :=
  .file s!"Langlib/Examples/Whitespace/{f}"

/-- Inline program, written as an AST and rendered to concrete syntax. -/
private def ws (is : List Instr) : Source :=
  .inline (Prog.render is.toArray)

/-- Print the top of the stack as a number and halt (a common test tail). -/
private def outHalt : List Instr := [.outNum, .halt]

def suite : Suite where
  name := "whitespace"
  run := run
  cases :=
    [ -- Examples
      { name := "hello example", source := ex "hello.ws",
        expect := .outputs "Hello, World!\n" }
    , { name := "cat example copies then errors at EOF", source := ex "cat.ws",
        input := "meow", expect := .runtimeError "end of input" }
    , { name := "count example", source := ex "count.ws",
        expect := .outputs "1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n" }
    , { name := "add example", source := ex "add.ws", input := "3\n4\n",
        expect := .outputs "7\n" }
    , { name := "add example with negatives", source := ex "add.ws",
        input := "-30\n8\n", expect := .outputs "-22\n" }
    , { name := "fact example on 5", source := ex "fact.ws", input := "5\n",
        expect := .outputs "120\n" }
    , { name := "fact example on 0", source := ex "fact.ws", input := "0\n",
        expect := .outputs "1\n" }
    , { name := "fact example on 20", source := ex "fact.ws", input := "20\n",
        expect := .outputs "2432902008176640000\n" }
    , { name := "greet example", source := ex "greet.ws", input := "Ada\n",
        expect := .outputs "Hello, Ada!\n" }
    , { name := "truth-machine example on 0", source := ex "truth.ws",
        input := "0\n", expect := .outputs "0" }
    , { name := "truth-machine example on 1", source := ex "truth.ws",
        input := "1\n", fuel := 100_000, expect := .diverges }
      -- Number literals and numeric output
    , { name := "push and output a number", source := ws ([.push 42] ++ outHalt),
        expect := .outputs "42" }
    , { name := "negative literal", source := ws ([.push (-5)] ++ outHalt),
        expect := .outputs "-5" }
    , { name := "zero literal, positive sign", source := .inline ("   \n\t\n \t\n\n\n"),
        -- [Space][Space] [Space][LF] push +0; outnum; end
        expect := .outputs "0" }
    , { name := "zero literal, negative sign", source := .inline ("  \t\n\t\n \t\n\n\n"),
        -- push -0 (sign [Tab], no digits) prints as 0
        expect := .outputs "0" }
      -- Character output
    , { name := "output char", source := ws [.push 72, .outChar, .halt],
        expect := .outputs "H" }
    , { name := "output char out of byte range", source := ws [.push 256, .outChar, .halt],
        expect := .runtimeError "outside the byte range" }
    , { name := "output char negative", source := ws [.push (-1), .outChar, .halt],
        expect := .runtimeError "outside the byte range" }
      -- Stack manipulation
    , { name := "dup", source := ws ([.push 7, .dup, .add] ++ outHalt),
        expect := .outputs "14" }
    , { name := "swap", source := ws ([.push 2, .push 9, .swap, .sub] ++ outHalt),
        expect := .outputs "7" }
    , { name := "discard", source := ws ([.push 1, .push 2, .drop] ++ outHalt),
        expect := .outputs "1" }
    , { name := "copy reaches below the top", -- stack [3,2,1]; copy 2 pushes 1
        source := ws ([.push 1, .push 2, .push 3, .copy 2] ++ outHalt),
        expect := .outputs "1" }
    , { name := "copy negative index errors",
        source := ws ([.push 1, .copy (-1)] ++ outHalt),
        expect := .runtimeError "copy with negative index" }
    , { name := "copy out of range errors",
        source := ws ([.push 1, .copy 3] ++ outHalt),
        expect := .runtimeError "out of range" }
    , { name := "slide keeps the top", -- [3,2,1] slide 1 -> [3,1]
        source := ws ([.push 1, .push 2, .push 3, .slide 1, .outNum] ++ outHalt),
        expect := .outputs "31" }
    , { name := "slide with negative count slides nothing",
        source := ws ([.push 1, .push 2, .slide (-4), .outNum] ++ outHalt),
        expect := .outputs "21" }
    , { name := "slide past the bottom clears below the top",
        source := ws [.push 1, .push 2, .slide 99, .outNum, .outNum, .halt],
        expect := .runtimeError "stack underflow in output number" }
      -- Arithmetic
    , { name := "sub is second minus top",
        source := ws ([.push 7, .push 3, .sub] ++ outHalt),
        expect := .outputs "4" }
    , { name := "mul", source := ws ([.push (-6), .push 7, .mul] ++ outHalt),
        expect := .outputs "-42" }
    , { name := "div rounds toward negative infinity",
        source := ws ([.push (-7), .push 2, .div] ++ outHalt),
        expect := .outputs "-4" }
    , { name := "mod sign follows the divisor",
        source := ws ([.push (-7), .push 2, .mod] ++ outHalt),
        expect := .outputs "1" }
    , { name := "mod with negative divisor",
        source := ws ([.push 7, .push (-2), .mod] ++ outHalt),
        expect := .outputs "-1" }
    , { name := "division by zero",
        source := ws ([.push 1, .push 0, .div] ++ outHalt),
        expect := .runtimeError "division by zero" }
    , { name := "modulo by zero",
        source := ws ([.push 1, .push 0, .mod] ++ outHalt),
        expect := .runtimeError "modulo by zero" }
      -- Heap
    , { name := "store and retrieve",
        source := ws ([.push 5, .push 99, .store, .push 5, .retrieve] ++ outHalt),
        expect := .outputs "99" }
    , { name := "retrieve of an unset address is 0",
        source := ws ([.push 12345, .retrieve] ++ outHalt),
        expect := .outputs "0" }
    , { name := "store at negative address errors",
        source := ws [.push (-1), .push 7, .store, .halt],
        expect := .runtimeError "negative address" }
    , { name := "retrieve at negative address errors",
        source := ws ([.push (-3), .retrieve] ++ outHalt),
        expect := .runtimeError "negative address" }
      -- Flow control
    , { name := "unconditional jump skips code",
        source := ws [.jump "T", .push 1, .outNum, .label "T", .push 2, .outNum, .halt],
        expect := .outputs "2" }
    , { name := "call and return",
        source := ws [.call "S", .push 66, .outChar, .halt,
                      .label "S", .push 65, .outChar, .ret],
        expect := .outputs "AB" }
    , { name := "nested calls",
        source := ws [.call "S", .push 67, .outChar, .halt,
                      .label "S", .call "T", .push 66, .outChar, .ret,
                      .label "T", .push 65, .outChar, .ret],
        expect := .outputs "ABC" }
    , { name := "return with empty call stack errors",
        source := ws [.ret],
        expect := .runtimeError "empty call stack" }
    , { name := "jz taken pops the value",
        source := ws ([.push 8, .push 0, .jz "T", .push 1, .outNum,
                       .label "T"] ++ outHalt),
        expect := .outputs "8" }
    , { name := "jz not taken pops the value",
        source := ws ([.push 8, .push 5, .jz "T", .label "T"] ++ outHalt),
        expect := .outputs "8" }
    , { name := "jn taken on negative",
        source := ws ([.push (-1), .jn "T", .push 1, .outNum, .label "T",
                       .push 2] ++ outHalt),
        expect := .outputs "2" }
    , { name := "jn not taken on zero",
        source := ws ([.push 0, .jn "T", .push 1, .outNum, .label "T",
                       .push 2] ++ outHalt),
        expect := .outputs "12" }
    , { name := "undefined label errors at jump time",
        source := ws [.jump "TTT", .halt],
        expect := .runtimeError "undefined label" }
    , { name := "untaken conditional jump to undefined label is fine",
        source := ws ([.push 1, .jz "TTT", .push 3] ++ outHalt),
        expect := .outputs "3" }
    , { name := "duplicate labels: first definition wins",
        source := ws [.jump "S", .label "S", .push 1, .outNum, .halt,
                      .label "S", .push 2, .outNum, .halt],
        expect := .outputs "1" }
    , { name := "labels are token strings, not numbers", -- "S" and "SS" differ
        source := ws [.jump "SS", .label "S", .push 1, .outNum, .halt,
                      .label "SS", .push 2, .outNum, .halt],
        expect := .outputs "2" }
      -- Input
    , { name := "read char stores the byte",
        source := ws [.push 3, .readChar, .push 3, .retrieve, .outChar, .halt],
        input := "A", expect := .outputs "A" }
    , { name := "read char at EOF errors",
        source := ws [.push 0, .readChar, .halt],
        expect := .runtimeError "read char at end of input" }
    , { name := "read number with whitespace and minus",
        source := ws ([.push 0, .readNum, .push 0, .retrieve] ++ outHalt),
        input := "  -42 \n", expect := .outputs "-42" }
    , { name := "read number from a final unterminated line",
        source := ws ([.push 0, .readNum, .push 0, .retrieve] ++ outHalt),
        input := "7", expect := .outputs "7" }
    , { name := "read malformed number errors",
        source := ws [.push 0, .readNum, .halt],
        input := "12abc\n", expect := .runtimeError "as a number" }
    , { name := "read empty line as number errors",
        source := ws [.push 0, .readNum, .halt],
        input := "\n5\n", expect := .runtimeError "as a number" }
    , { name := "read number at EOF errors",
        source := ws [.push 0, .readNum, .halt],
        expect := .runtimeError "read number at end of input" }
      -- Machine-level errors and divergence
    , { name := "pop of an empty stack errors",
        source := ws [.drop, .halt],
        expect := .runtimeError "stack underflow in discard" }
    , { name := "arithmetic on a one-element stack errors",
        source := ws [.push 1, .add, .halt],
        expect := .runtimeError "stack underflow in add" }
    , { name := "running off the end errors",
        source := ws [.push 1, .outNum],
        expect := .runtimeError "ran off the end" }
    , { name := "empty program runs off the end",
        source := .inline "these_characters_are_all_comments",
        expect := .runtimeError "ran off the end" }
    , { name := "infinite loop diverges",
        source := ws [.label "S", .jump "S"],
        fuel := 10_000, expect := .diverges }
      -- Parse errors
    , { name := "unrecognised instruction",
        source := .inline "\t\n\n", -- [Tab][LF] is the I/O IMP; [LF] is no command
        expect := .parseError "unrecognised instruction at 1:1" }
    , { name := "incomplete instruction at end of program",
        source := .inline " ", -- lone stack IMP
        expect := .parseError "unrecognised instruction" }
    , { name := "number missing its sign",
        source := .inline "  \n", -- push terminated before a sign token
        expect := .parseError "missing its sign" }
    , { name := "unterminated number",
        source := .inline "   \t \t", -- push with digits but no [LF]
        expect := .parseError "unterminated" }
    , { name := "unterminated label",
        source := .inline "\n   \t", -- label with tokens but no [LF]
        expect := .parseError "unterminated" }
    ]

def suites : List Suite := [suite]

end Langlib.Tests.Whitespace
