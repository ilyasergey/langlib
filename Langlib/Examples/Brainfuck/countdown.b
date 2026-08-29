[ Prints the digits from 9 down to 0 and a newline.
  Original example for langlib.
  Layout: cell0 is the loop counter; cell1 the digit; cell2 a builder. ]

++++++++++              set cell0 to 10
>>+++++++[<++++++++>-]  build 56 in cell1 using cell2 as a counter
<+                      make cell1 equal 57 which is ASCII digit nine
<[>.-<-]                ten times print cell1 then decrement it
>[-]++++++++++.         clear cell1 then print a newline
