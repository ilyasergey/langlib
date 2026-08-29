[ Prints the uppercase alphabet and a newline.
  Original example for langlib.
  Layout: cell1 holds the letter and cell2 counts 26 iterations. ]

++++++++[>++++++++<-]>+     build 65 in cell1 which is ASCII letter A
>+++++[>+++++<-]>+          build 26 in cell3 as the loop counter
[<<.+>>-]                   print cell1 then increment it 26 times
<<[-]++++++++++.            clear cell1 then print a newline
