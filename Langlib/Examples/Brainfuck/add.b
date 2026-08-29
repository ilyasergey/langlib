[ Single-digit adder: reads two ASCII digits whose sum is at most 9 and
  prints their sum as one ASCII digit. Original example for langlib.
  Try: echo -n 34 | lake exe brainfuck Langlib/Examples/Brainfuck/add.b ]

,>,                     read a into cell0 and b into cell1
[<+>-]                  add cell1 into cell0
++++++[<-------->-]     subtract 48 from cell0 to undo one ASCII offset
<.                      print the digit
