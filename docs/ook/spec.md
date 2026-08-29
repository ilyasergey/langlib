# Ook!

* **Author**: David Morgan-Mar
* **Year**: 2001
* **Canonical sources**: Morgan-Mar's page,
  https://www.dangermouse.net/esoteric/ook.html; community page at
  https://esolangs.org/wiki/Ook! (CC0)
* **In LangLib**: `Langlib/Languages/Ook/`, runner `lake exe ook`,
  examples in `Langlib/Examples/Ook/`

## History

Ook! is a programming language designed for orang-utans, and specifically
for one: the Librarian of Unseen University in Terry Pratchett's Discworld
novels, who was transformed into an orangutan by a magical accident, found
the shape convenient for shelving, and since then communicates exclusively
by saying "Ook" with varying inflection. (One does not call him a monkey.
He is an ape. People who get this wrong tend to be helped, briefly, toward
the ceiling.) Morgan-Mar's design principles follow directly: the syntax
should be writable and readable by orang-utans, it must not mention the
word "monkey", and bananas are good.

Beneath the fur, Ook! is exactly brainfuck (Urban Müller, 1993). Its three
words, read in pairs, spell brainfuck's eight commands, which makes Ook! the
founding member of what the esolangs wiki calls the trivial brainfuck
substitution family, and makes its Turing completeness a corollary rather
than a theorem.

## Syntax

The whole vocabulary is three words: `Ook.`, `Ook?`, `Ook!`. A program is a
whitespace-separated sequence of these words, read two at a time; each pair
is one command:

| Pair | brainfuck | Effect |
|------|-----------|--------|
| `Ook. Ook?` | `>` | move the pointer one cell right |
| `Ook? Ook.` | `<` | move the pointer one cell left |
| `Ook. Ook.` | `+` | increment the current cell |
| `Ook! Ook!` | `-` | decrement the current cell |
| `Ook. Ook!` | `,` | read one input byte into the current cell |
| `Ook! Ook.` | `.` | write the current cell to output |
| `Ook! Ook?` | `[` | loop start |
| `Ook? Ook!` | `]` | loop end |
| `Ook? Ook?` | none | "Give the Memory Pointer a banana." |

Morgan-Mar's page states that programs must contain an even number of Ooks
and that line breaks are ignored. It also settles the comment question:
since "ook" can convey entire ideas, emotions, and abstract thoughts
depending on the nuances of inflection, Ook! has no need of comments. The
code itself serves perfectly well to describe what it does. Provided you
are an orang-utan.

## Semantic decisions in LangLib

Parsing (`Langlib/Languages/Ook/Parser.lean`) produces a
`Langlib.Brainfuck.Prog`; there is no separate Ook! AST. Our decisions:

1. **Tokens are whitespace-separated words**, and each word must be exactly
   `Ook.`, `Ook?`, or `Ook!`. Any other word is a parse error, reported
   with its line and column. In particular there are no comments (see
   above, and note that prose would otherwise parse as garbage pairs), and
   we do not implement the folklore punctuation-only shorthand (`. ? !`);
   only classic Ook!.
2. **An odd number of words is a parse error** ("Programs must thus contain
   an even number of Ooks" on the language page), reported at the widowed
   final word.
3. **Pairing is positional**: words 1-2 form the first command, words 3-4
   the second, and so on. Loop pairs `Ook! Ook?` / `Ook? Ook!` nest like
   parentheses; an unmatched one is a parse error with the token's position
   and index.
4. **`Ook? Ook?` is a parse error.** The language page lists it with the
   effect "Give the Memory Pointer a banana", which specifies no machine
   behaviour; the esolangs wiki calls it a no-op. In a language whose
   entire vocabulary is three words, silently accepting a ninth pair mostly
   hides typos, so we reject it (the error message acknowledges the
   banana). Programs that use it as filler must go bananas elsewhere.
5. **Runtime semantics are brainfuck's, by construction**: 8-bit wrapping
   cells, tape unbounded to the right, moving left of cell 0 is a runtime
   error, and the same three EOF conventions behind the same `--eof` flag.
   Every one of those decisions is recorded, with sources, in
   `docs/brainfuck/spec.md`; evaluation is literally a call to
   `Langlib.Brainfuck.evalProg`.

Translation runs both ways: `Langlib.Ook.parse` (Ook! source to brainfuck
program) and `Langlib.Ook.render` (brainfuck program to Ook! source,
sixteen words per line), plus the source-to-source wrappers `ofBrainfuck`
and `toBrainfuck`. Our `.ook` examples are generated with `render` from the
brainfuck examples, and the tests round-trip them.

## Licensing note

Morgan-Mar's page carries a plain copyright notice and no explicit licence
text, but it welcomes independent implementations in the most practical way
available: its resources section happily links third-party Ook!
interpreters, compilers, converters, and even a Palm OS IDE, in Ruby,
Python, .NET, Perl, and Java. The language has been reimplemented dozens of
times since 2001. The specification is a page of ideas (three words and a
pairing table); LangLib implements those ideas in its own words and code
and pastes none of the page's text.

## Trying it

Hello world, spoken entirely in orangutan.

```
$ lake exe ook Langlib/Examples/Ook/hello.ook
Hello World!
```

The alphabet, since Ook! inherits everything brainfuck can do.

```
$ lake exe ook Langlib/Examples/Ook/alphabet.ook
ABCDEFGHIJKLMNOPQRSTUVWXYZ
```

cat, which needs `--eof zero` for the same reason its brainfuck original
does.

```
$ echo -n "Ook-ook" | lake exe ook --eof zero Langlib/Examples/Ook/cat.ook
Ook-ook
```

## Compilation from Turpentine

Planned (see `docs/PLAN.md`, Stage 4): Turpentine compiles to brainfuck, and
`Langlib.Ook.render` turns the result into Ook! for free.
