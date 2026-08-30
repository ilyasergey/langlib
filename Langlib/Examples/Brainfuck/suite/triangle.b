[ Conformance suite: triangle. Five rows of stars, row i holding i of them.
  Hand-written, not compiled from Turpentine.

  Tape layout, fixed for the whole program:
    p0 rows left    p1 row length n    p2 copy of n
    p3 spare        p4 the byte 42     p5 the byte 10
  Nothing here needs arithmetic beyond counting, so there is no decimal
  printer: the only two bytes ever written are held in p4 and p5. ]

setup
+++++            p0 = 5 rows
>+               p1 = 1 stars on the first row
>>+++++++        p3 = 7
[>++++++<-]      p4 = 7*6 = 42, an asterisk
>>++++++++++     p5 = 10, a newline
<<<<<            back to p0

[                one pass per row
  >[->+>+<<]     n into p2 and p3, emptying p1
  >>[-<<+>>]     p3 back into p1, so n survives the row
  <[>>.<<-]      print p4 once per unit of p2
  >>>.           print the newline
  <<<<+          the next row is one star longer
  <-             one row fewer to go
]
