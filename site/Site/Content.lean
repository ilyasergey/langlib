import Site.Page

/-!
# What the site knows that the documentation does not

Two kinds of thing live here. First, the catalogue: which languages exist,
who wrote them and when, and a one-line reason each is in the library. Second,
the manifest of example programs to embed in the playgrounds, with the input
and the flags each one wants.

Everything else on the site is rendered from `docs/` and `CONTRIBUTING.md`.
Prose that would duplicate those files does not belong in this file.
-/

namespace Site

/-- A language in the library. -/
structure Lang where
  /-- Directory under `docs/` and path segment on the site. -/
  slug : String
  /-- What to call it in a heading. -/
  name : String
  /-- Credited author or authors. -/
  author : String
  /-- Year of first release. -/
  year : String
  /-- One line, for the card on the home page. -/
  blurb : String
  /-- The runner, e.g. `lake exe brainfuck`. -/
  runner : String
  /-- The examples directory under `Langlib/Examples/`. -/
  examplesDir : String
  /-- False for languages another pair of hands is still working on. -/
  ready : Bool := true
  deriving Inhabited

def langs : List Lang :=
  [ { slug := "brainfuck", name := "brainfuck"
    , author := "Urban Müller", year := "1993"
    , blurb := "Eight commands and a tape. The fruit fly of esoteric programming, and the library's primary compilation target."
    , runner := "lake exe brainfuck", examplesDir := "Brainfuck" }
  , { slug := "whitespace", name := "whitespace"
    , author := "Edwin Brady and Chris Morris", year := "2003"
    , blurb := "Space, tab and linefeed are the program; every other byte is a comment. It prints as a blank page and it is Turing complete."
    , runner := "lake exe whitespace", examplesDir := "Whitespace" }
  , { slug := "malbolge", name := "malbolge"
    , author := "Ben Olmstead", year := "1998"
    , blurb := "Designed to be impossible to write. Nobody managed for two years, and the first program was found by search rather than written."
    , runner := "lake exe malbolge", examplesDir := "Malbolge" }
  , { slug := "befunge93", name := "Befunge-93"
    , author := "Chris Pressey", year := "1993"
    , blurb := "A two-dimensional grid the instruction pointer wanders around, editing itself as it goes. Built to be hard to compile."
    , runner := "lake exe befunge93", examplesDir := "Befunge93" }
  , { slug := "subleq", name := "subleq"
    , author := "folklore; conventions by Oleg Mazonka", year := "1990s"
    , blurb := "SUBtract and branch if Less than or EQual to zero. That is not the first instruction; that is the instruction set."
    , runner := "lake exe subleq", examplesDir := "Subleq" }
  , { slug := "fractran", name := "FRACTRAN"
    , author := "John H. Conway", year := "1987"
    , blurb := "A program is a list of fractions and the entire state is one integer. Fourteen fractions enumerate the primes."
    , runner := "lake exe fractran", examplesDir := "Fractran" }
  , { slug := "thue", name := "Thue"
    , author := "John Colagioia", year := "2000"
    , blurb := "Nondeterministic string rewriting, descended directly from the 1914 word problem that turned out to be undecidable."
    , runner := "lake exe thue", examplesDir := "Thue" }
  , { slug := "ook", name := "Ook!"
    , author := "David Morgan-Mar", year := "2001"
    , blurb := "Brainfuck for orang-utans. Three syllables, eight commands, one Librarian, and please do not call him a monkey."
    , runner := "lake exe ook", examplesDir := "Ook" }
  , { slug := "deadfish", name := "Deadfish"
    , author := "Jonathan Todd Skinner", year := "2006"
    , blurb := "One accumulator, four commands, no input and no way to stop. Famous for what it cannot do."
    , runner := "lake exe deadfish", examplesDir := "Deadfish" }
  ]

/--
Languages a second pair of hands is still landing. The generator publishes a
full page for one of these the moment `docs/<slug>/spec.md` appears, and shows
a "coming soon" card until then, so the site never depends on files that are
not there yet.
-/
def comingSoon : List Lang :=
  [ { slug := "piet", name := "Piet"
    , author := "David Morgan-Mar", year := "2002"
    , blurb := "Programs are abstract paintings, and the instruction is the colour change from one block to the next."
    , runner := "lake exe piet", examplesDir := "Piet", ready := false }
  , { slug := "brainloller", name := "Brainloller"
    , author := "Lode Vandevenne", year := "2005"
    , blurb := "Brainfuck encoded in pixel colours: the same tape machine, delivered as a PNG."
    , runner := "lake exe brainloller", examplesDir := "Brainloller", ready := false }
  ]

/-! ## Example programs to embed in the playgrounds

`file` is relative to `Langlib/Examples/`; the generator reads it at build
time, so the playground always runs the same bytes as `lake test`.
-/

structure ExampleRef where
  label : String
  file : String
  input : String := ""
  eof : String := "unchanged"
  note : String := ""
  deriving Inhabited

def brainfuckExamples : List ExampleRef :=
  [ { label := "hello.b — Hello World!", file := "Brainfuck/hello.b"
    , note := "The canonical nested-loop hello world. The prose header sits inside a loop that never runs, because cell 0 starts at zero." }
  , { label := "add.b — add two digits", file := "Brainfuck/add.b", input := "34"
    , note := "Reads two ASCII digits whose sum is at most 9 and prints the sum as one digit." }
  , { label := "rev.b — reverse a word", file := "Brainfuck/rev.b"
    , input := "stressed", eof := "zero"
    , note := "stressed in, desserts out. Needs the store-0-at-end-of-input convention, or the read loop never ends." }
  , { label := "countdown.b — 9 down to 0", file := "Brainfuck/countdown.b"
    , note := "Builds ASCII 57 in a cell and walks it down. Watch the builder cell drain into the digit cell." }
  , { label := "alphabet.b — A to Z", file := "Brainfuck/alphabet.b"
    , note := "Twenty-six iterations of print-then-increment." }
  , { label := "cat.b — copy input to output", file := "Brainfuck/cat.b"
    , input := "meow meow\n", eof := "zero"
    , note := "Switch the end-of-input setting to leave the cell and it echoes the last byte forever, which is its own kind of lesson." }
  , { label := "truth.b — truth-machine", file := "Brainfuck/truth.b", input := "0"
    , note := "On 0 it prints 0 and halts. Feed it 1 and it prints 1 until the step budget runs out; that is what a truth-machine is." }
  , { label := "xkcd-random.b — getRandomNumber", file := "Brainfuck/xkcd-random.b"
    , note := "Prints 4. Chosen by fair dice roll, guaranteed to be random." }
  , { label := "quine.b — a 505-byte quine", file := "Brainfuck/quine.b"
    , note := "Erik Bosman's quine prints itself, in about half a million steps. Set the speed to all-at-once unless you have plans for the afternoon." }
  ]

def whitespaceExamples : List ExampleRef :=
  [ { label := "hello.ws — Hello, World!", file := "Whitespace/hello.ws"
    , note := "Push each character's code and print it. The program is blank; the panel to the right is the same bytes with the invisible made visible." }
  , { label := "count.ws — 1 to 10", file := "Whitespace/count.ws"
    , note := "A loop with a heap counter and a conditional jump." }
  , { label := "add.ws — add two numbers", file := "Whitespace/add.ws", input := "17\n25\n"
    , note := "Two readnum instructions, one add. Reads whole lines, so keep the trailing newlines." }
  , { label := "fact.ws — factorial", file := "Whitespace/fact.ws", input := "5\n"
    , note := "A subroutine with call and return; watch the call stack drive the multiply." }
  , { label := "greet.ws — greet a name", file := "Whitespace/greet.ws", input := "Ada\n"
    , note := "Character input into the heap, then back out again." }
  , { label := "truth.ws — truth-machine", file := "Whitespace/truth.ws", input := "0\n"
    , note := "Feed it 1 instead and it never stops, exactly as specified." }
  , { label := "cat.ws — copy input to output", file := "Whitespace/cat.ws", input := "meow\n"
    , note := "Whitespace has no way to test for end of input, so cat copies its input and then fails on the next read. The reference interpreter does the same." }
  ]

def deadfishExamples : List ExampleRef :=
  [ { label := "hello.df — the codes of a greeting", file := "Deadfish/hello.df"
    , note := "Deadfish cannot print letters, so it prints their ASCII codes, one per line." }
  , { label := "powers.df — squaring into the reset", file := "Deadfish/powers.df"
    , note := "2, 4, 16, then 256, which is one of the two values that silently become 0." }
  , { label := "xkcd-random.df — getRandomNumber", file := "Deadfish/xkcd-random.df"
    , note := "iiso." }
  ]

end Site
