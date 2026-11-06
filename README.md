# ChatLLaMbda - a Lambek calculus chat interface

CSE301 project, 2026. Andrei Stirbu.

A natural language interface in Haskell, with the product-free Lambek calculus (decided with a
focused sequent calculus) as the grammar. The lexicon file gives each word one or more types and a
Python meaning, and the world file is a Python file with the facts. For a sentence typed by the
user, the program checks whether it's grammatical, finds all its derivations, turns them into
lambda terms and evaluates those in the world to get an answer.

Done:

- stage 1: the decision procedure (`dec_rinv`, `dec_lfoc`, `isGrammatical` in `Lambek.hs`)
- stage 2: all derivations as trees, converted to lambda terms (`Lambek.hs`, `Deriv.hs`)
- stage 3: evaluating the terms in Python (`Eval.hs`)
- going beyond:
  - a second domain about students, teachers and courses (`courses.elx`, `uniworld.py`)
  - questions - who / what / which, yes/no, and "who does X fear"
  - explanations of answers with `:why`
  - merging readings that only differ by associativity of "and" (`Ambiguity.hs`)
- extras: printing proof trees (`:tree`), some feedback when a sentence is rejected, and a test file

## Building and running

You need GHC (I used 9.10.3) and `python3`. There's no cabal project, everything is in this
folder:

```sh
ghc ChatLLaMbda.hs
./ChatLLaMbda
```

It asks for a lexicon and a world, either `animals.elx` + `aniworld.py` or `courses.elx` +
`uniworld.py`. Input is case-insensitive. Apart from sentences you can type:

```
:tree      proof trees of the last sentence, with their lambda terms
:why       explain the last answer
:lexicon   list the words and their types
:help
:quit      (Ctrl-D works too)
```

Tests:

```sh
runghc Tests.hs
```

Should end with `91/91 checks passed`. Run it from this folder since it loads both lexicons and
both worlds. The tests include the grammaticality results and lambda terms from the spec's
transcripts, a check that `isGrammatical` and the derivation search always agree, the number of
readings with and without `ASSOC`, and the answers and explanations in both worlds. Adding a test
is just adding a row to one of the tables at the top of the file.

## Example

Animals:

```
> Seamus is hungry and
That is not a well-formed sentence.
   I got as far as "Seamus is hungry"; the rest does not fit.
> Conor flies
That is not a well-formed sentence.
   I do not know the word(s): Flies
> Conor sleeps
False
> :why
no; the ones who sleep are Seamus
> every grey cat sleeps
True
> every cat fears a dog
That sentence is ambiguous
Sense [Every_1 Cat_2 (\a. A_4 Dog_5 (\b. Fears_3 a b))]: True
Sense [A_4 Dog_5 (\a. Every_1 Cat_2 (\b. Fears_3 b a))]: False
> :why
Sense 1: yes, all of Conor, Seamus
Sense 2: no, none of Dara, Fiona
> Seamus sleeps and Seamus is grey and Seamus fears Dara
True
> who is hungry
Conor, Dara, Ronan
> who does Tara fear
Conor, Seamus
> does Conor chase Tara
Yes
> Conor sleeps
False
> :tree
Derivation 1 of 1:
              -----------  X
               [np] --> np
       -----------------  F Conor_1   ---------  X
            Conor_1:np --> np          [s] --> s
      -------------------------------------------  L
                Conor_1:np [np \ s] --> s
----------------------------------------------  F Sleeps_2
            Conor_1:np, Sleeps_2:np \ s --> s
   as a lambda expression: Sleeps_2 Conor_1
```

Courses:

```
> every student that passes takes logic
False
> :why
no, not Chen
> what does Ana take
algebra, logic
> who teaches algebra
Nadia
> every teacher teaches a course
That sentence is ambiguous
Sense [Every_1 Teacher_2 (\a. A_4 Course_5 (\b. Teaches_3 a b))]: True
Sense [A_4 Course_5 (\a. Every_1 Teacher_2 (\b. Teaches_3 b a))]: False
> is algebra hard
No
```

The chat doesn't print the stage 1 / stage 2 messages anymore since it always evaluates, but
those outputs are still checked in `Tests.hs`.

## How it works

### Deciding and deriving

`dec_rinv` and `dec_lfoc` are a direct translation of the six rules. R and R' break down the goal
until it's an atom, then F tries every position of the context, and L / L' try every split of the
context with `take` and `drop`. `isGrammatical` uses `sequence` on the list of possible types of
each word to try every choice of entries.

For stage 2 the spec suggests returning `[LExp]`, but I return derivation trees instead (`Deriv`
in `Deriv.hs`) and get the terms with `toLExp`. I wanted to print the proof trees, and from a
lambda term alone you can't tell which position F focused on or how L split the context. In
`toLExp`, R and R' become lambdas and F becomes the focused variable applied to the arguments from
the L/L' spine.

Variables are `Word_position` like in the spec (`Sleeps_2`). The R/R' variables are single
lowercase letters so they can't clash with words. Each parse also stores which lexicon entry it
used for each position - `Hungry_3` alone doesn't say if it's the `adj` or the `n / n` entry, and
you need the right one to evaluate.

### Evaluating

`Eval.pyExpr` replaces each word variable by its Python value and turns lambdas into Python
lambdas, so the whole term becomes one Python expression that is sent to a `python3` process
(Python does the beta-reduction, `LExp.normalize` isn't used).

`runPythonCode` reads exactly one line of output. If a query prints nothing it
hangs, and if Python raises an error the traceback goes to stderr and it hangs too. So every query
goes through a helper `_ans` that always prints one line - errors included. It also formats the
answer: lists are joined (for "who" questions), strings are printed as they are (Yes/No), other
values with `repr` (True/False). The world file is loaded with one `exec` of the whole file,
because sending it line by line breaks as soon as there's an indented block.

If all readings give the same answer only the answer is printed.

### Ambiguity

"Seamus sleeps and Seamus is grey and Seamus fears Dara" has two derivations, one for each way of
bracketing the two "and"s. The terms are different (even the head is `And_3` in one and `And_7` in
the other), they're only equal because "and" is associative. The calculus has no way of knowing
that, so the lexicon says it with a line `ASSOC : And.`

`Ambiguity.canonical` computes a normal form. First each word variable is renamed to the word plus
the meaning of the entry it used, so both "and"s become the same thing (but the sentence "and" and
the adjective "and" stay different). Then nested applications of an associative word are flattened
and rebuilt to the right. Two parses with the same normal form are the same reading. With this the
sentence above has 1 reading and "every cat fears a dog" still has 2.

I didn't do commutativity. Word order already fixes the order of the arguments so it wouldn't
merge much, and sorting the arguments by how they print isn't stable under renaming bound
variables.

### Questions

A lexicon can have a line `QUESTION : q.` after `SENTENCE`. The input is tried as `s` first and
then as `q`, so "Conor sleeps" gives `False` and "who sleeps" gives `Seamus`. Types used:

```
Who   : q / (np \ s)                  who sleeps
Who   : (s / np) \ q                  Conor chases who
Which : (q / (np \ s)) / n            which cat sleeps
Does  : (q / (np \ s)) / np           does Conor sleep   (with Sleep, Chase, ... as extra verb forms)
Is    : (q / adj) / np                is Conor hungry
Does  : (qo / (np \ (s / np))) / np   who does Conor fear
Who   : q / qo
```

The last two took a while. My first version typed "does Conor fear" as `s / np`, but then "does
Conor chase Tara" also parsed as a normal sentence and since `s` is tried first it answered `True`
instead of `Yes`. Using a separate atom `qo` fixed it. (Also `(q / np) \ q` for object questions
never matches anything, a transitive verb leaves `s / np` on its left.)

### Explanations

An entry can have a second Python value after a `?`:

```
Every : (s / (np \ s)) / n = lambda q : lambda p : all (...)
                           ? lambda q : lambda p : 'yes, all of ' + names(...) if ... else 'no, not ' + names(...).
```

`:why` evaluates the same term again but with the explaining value for the head word of the term
(the quantifier in "every cat sleeps", the "and" in "A and B"), and the normal values for all the
other words. Only the head is replaced, since the head's explanation needs its arguments to be
normal meanings and not strings. When the head has no `?` value the chat just says it can't
explain, e.g. for who-questions. `names(xs)` is a small helper I added to print lists of names.

### Second domain

`courses.elx` / `uniworld.py`. Here there are two kinds of individuals, people and courses
(`things = people + courses`), so "who" only looks at people, "what" only at courses, and
"every" / "a" at everything. There's also a relative pronoun `That : (n \ n) / (np \ s)` for
things like "every student that passes takes logic".

### Rejected sentences

If some words aren't in the lexicon they get listed, otherwise it prints the longest grammatical
beginning of the sentence.

## Changes to the template

- `Lambek.hs` - written from the stub.
- `ChatLLaMbda.hs` - the REPL was mostly rewritten (evaluation, ambiguity, error messages, the
  `:` commands). Python is started empty and the world is loaded by `Eval.startEval`.
- `Parser.hs` - only the lexicon syntax changed: `QUESTION` lines, `ASSOC` lines, the optional
  `? <python>` part, and `lexicon` now returns `(Lexicon Sem, Laws, [LTp])` where `Sem` is the
  meaning plus the optional explanation.
- `animals.elx` - added the new declarations, explanations, question words and bare verb forms.
  The original entries have the same types and meanings.
- `LTypes.hs`, `LExp.hs`, `PySupport.hs`, `aniworld.py` - not changed.

New files: `Deriv.hs`, `Eval.hs`, `Ambiguity.hs`, `Tests.hs`, `courses.elx`, `uniworld.py`, and
`hie.yaml` for the language server.

Lexicon format, in this order:

```
SENTENCE : s.
QUESTION : q.                                   (optional)
ASSOC : And.                                    (optional)
Word : <type> = <python>.
Word : <type> = <python> ? <python explanation>.
```

## Limitations

- no `.` or `?` inside the Python values (so no `', '.join(...)`, hence `names`)
- no comments in `.elx` files
- punctuation isn't removed, `who sleeps?` doesn't work
- only associativity, no other laws
- no imperatives, the world can't be changed from the chat
- n "and"s in a row give Catalan(n) derivations (42 for 5), ASSOC turns them into one reading
- long sentences with words that have several entries are slow, because every choice of entries
  gets searched completely. "Seamus is grey and Tara is grey and Tara is grey and Tara is grey"
  takes about 14s, one more "and" takes minutes. "Seamus sleeps and ..." chains are fine

## AI usage

Most of the code was written by me by hand. AI (Claude) was used in the following ways:

- Mainly to help with the connection between Haskell and Python, i.e. starting the interpreter,
  loading the world and keeping the input/output in sync. For example, this part of
  `ChatLLaMbda.hs`:

  ```haskell
  main :: IO ()
  main = chat `catch` \e -> if isEOFError e then putStrLn "\nBye." else ioError e

  chat :: IO ()
  chat = do
    ...
    phandle <- launchPython (PCode "")
    startEval phandle db
    ...
  ```

  The fix that skips what Python prints on startup (in `Eval.startEval`) and the Ctrl-D handling
  above were written by AI.
- In 2-3 places where I had trouble with the implementation, I asked for a rough overview of how
  it should work instead of having it write the code for me: the normal form for telling real
  ambiguity from bracketing (`Ambiguity.canonical`), keeping the Haskell-Python protocol in sync,
  and how `:why` should decide which word gives the explanation.
- To suggest improvements. Sometimes the code I wrote was primitive and it suggested a more
  professional way of writing it. For example, I handled capitalization separately in the chat
  loop and in the tests, and it suggested one shared `stdize` so they can't get out of sync. It
  also pointed out that naming a parameter `lex` shadows `Prelude.lex`, so I renamed it to `elx`.
  And my first version removed duplicate readings with a plain `nub`, which it suggested replacing
  with a comparison on the normal form from `Ambiguity.canonical` and the entries each reading
  used.
- Some code comments were written with AI, to make sure the important parts are highlighted and
  nothing is over- or under-explained.
- I drafted this README with AI under strict instructions, as I would not have been as proficient
  at writing it.

## References

- J. Lambek, "The Mathematics of Sentence Structure", The American Mathematical Monthly 65(3),
  1958, pp. 154-170.
- J. Lambek, "On the calculus of syntactic types", Structure of language and its mathematical
  aspects 12, 1961, pp. 166-178.
- CSE301 project specification, N. Zeilberger, 2026.
