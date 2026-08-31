/-!
The beer song, as `99bottles.mal` sings it.

Three suites need the same 11459 bytes: Malbolge's example, its Unshackled
port, and `Langlib/Examples/Turpentine/99bottles.turp`, which was written to
reproduce them. Quoting the song in each would be three chances to quote it
differently, so it is rebuilt here, once, and every suite compares against
this. That is also what makes the Turpentine example's golden test say
something: it is checked against exactly the string `99bottles.mal` is
checked against, not against its own output recorded after the fact.

The verse is Iizawa, Sakabe, Sakai, Kusakari and Nishida's: the count and
the noun phrase, then the same again, the refrain, and the next count --
"No more bottles of beer" once the shelf is empty.
-/

namespace Langlib.Tests.BeerSong

/-- `n` bottles of beer, singular at one. -/
def bottles (n : Nat) : String :=
  if n == 1 then "1 bottle of beer" else s!"{n} bottles of beer"

/-- One verse. -/
def verse (n : Nat) : String :=
  let next := if n == 1 then "No more bottles of beer" else bottles (n - 1)
  s!"{bottles n} on the wall,\n{bottles n},\n\
     Take one down, pass it around,\n{next} on the wall.\n\n"

/-- The whole song, 99 verses down to none: 11459 bytes. -/
def song : String :=
  (List.range 99).foldl (fun acc i => acc ++ verse (99 - i)) ""

end Langlib.Tests.BeerSong
