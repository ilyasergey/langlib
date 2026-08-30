[ Conformance suite: count. the numbers 1 to 10, one per line.
  Hand-written, not compiled from Turpentine.

  Tape layout: cell0 rounds left, cell1 the number, cell2 a copy, cell3 onward the printer
  The decimal printer occupies P0 to P8 starting at cell 3; it takes a
  value 0 to 255 in P0, prints it without leading zeros, and leaves the
  whole block at zero. It was checked against every value from 0 to 255
  before it was used here. This header runs in no loop: cell 0 is zero at
  the start, so the bracket pair around it is never entered. ]

++++++++++>+<        cell0 = 10 rounds and cell1 = 1 the first number

[
  >[->+>+<<]>[-<+>]> copy the number into cell2 and the printer slot, restore it
  divide P0 by ten: quotient to P2 remainder to P6
  >++++++++++<                                B = 10 the countdown to the next carry
  [                                           one pass per unit of n
    -                                         n down one
    >-                                        B down one
    [->>>+>+<<<<]                             B into t1 and t2 emptying B
    >>>>[-<<<<+>>>>]                          t2 back into B so B survives the test
    <<+                                       t0 = 1
    >[<->[-]]                                 t1 nonzero? then t0 = 0
    <[<<++++++++++>+>-]                       t0 still set so B hit zero: q up one and B = 10
    <<<                                       back to n
  ]
  >>>>>>++++++++++<<<<<[->>>>>-<<<<<]<        r = 10 minus B left in P6
  >>>>>>[->>+<<]<<<<<<                        P6 is the units digit: park it in P8
  >>[-<<+>>]<<                                the quotient becomes the new n
  divide again: tens digit to P6 hundreds to P2
  >++++++++++<                                B = 10 the countdown to the next carry
  [                                           one pass per unit of n
    -                                         n down one
    >-                                        B down one
    [->>>+>+<<<<]                             B into t1 and t2 emptying B
    >>>>[-<<<<+>>>>]                          t2 back into B so B survives the test
    <<+                                       t0 = 1
    >[<->[-]]                                 t1 nonzero? then t0 = 0
    <[<<++++++++++>+>-]                       t0 still set so B hit zero: q up one and B = 10
    <<<                                       back to n
  ]
  >>>>>>++++++++++<<<<<[->>>>>-<<<<<]<        r = 10 minus B left in P6
  >>>>>>[->+<]<<<<<<                          P6 is the tens digit: park it in P7
  >>[->+>>>+<<<<]>[-<+>]                      copy the hundreds digit into P6 keeping it
  >>>>[-<+<+>>]<<[->>+<<]                     add the tens digit into P6 keeping it
  <<<                                         back to the hundreds digit
  [++++++++++++++++++++++++++++++++++++++++++++++++.[-]] print it only when it is not zero
  >>>>                                        to the sum of the top two digits
  [>++++++++++++++++++++++++++++++++++++++++++++++++.[-]<[-]] print the tens digit only when that sum is not zero
  >>                                          the units digit is always printed
  ++++++++++++++++++++++++++++++++++++++++++++++++.[-]
  <<<<<<<<                                    back to P0 with the block clear
  ++++++++++.[-]     a newline
  <<+                the number goes up by one
  <-                 one round fewer
]
