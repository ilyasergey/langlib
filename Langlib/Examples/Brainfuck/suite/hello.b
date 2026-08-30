[ Conformance suite: hello.
  Hand-written, not compiled from Turpentine.

  Cell 1 is loaded with 72 by an 8x8 multiply plus 8, and every character
  after that is a delta from the one before it, so the program is one long
  cell and the comments are the message. Deltas beat a fresh multiply per
  character here because the text is short and mostly ascending.
  This header runs in no loop: cell 0 is zero, so the [ ] never enters. ]

++++++++[>++++++++<-]>++++++++

.                                                                H  72
+++++++++++++++++++++++++++++.                                   e 101
+++++++.                                                         l 108
.                                                                l 108
+++.                                                             o 111
-------------------------------------------------------------------.  , 44
------------.                                                 space 32
+++++++++++++++++++++++++++++++++++++++++++++++++++++++.         W  87
++++++++++++++++++++++++.                                        o 111
+++.                                                             r 114
------.                                                          l 108
--------.                                                        d 100
-------------------------------------------------------------------.  ! 33
-----------------------.                                        LF 10
