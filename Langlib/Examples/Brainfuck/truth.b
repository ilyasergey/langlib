[ Truth-machine: reads one character. On input 1 it prints 1 forever; on
  input 0 it prints 0 once and halts. From the esolangs wiki brainfuck
  page at https://esolangs.org/wiki/Brainfuck (CC0).
  Usage: echo -n 0 | lake exe brainfuck Langlib/Examples/Brainfuck/truth.b
  With input 1 it fills your terminal until the fuel runs out; that is
  the point of a truth-machine. ]

+++++++++>>,<<[->+++++<]>+++[>-<-]>>+++++[>++++++++++<-]>-<<[>>.<<]>>-.
