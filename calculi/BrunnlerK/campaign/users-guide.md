# Brünnler's system K in Lean: a user's guide

For someone who knows the calculus (K. Brünnler, *Nested Sequents*,
arXiv:1004.1845 v1, Chapter 2, §2.1) and wants to use it here. The
tutorial, `Play/BrunnlerKTutorial.lean`, shows each thing below at work.

To begin: `lake build` in `calculi/BrunnlerK/`, then in a file

    import BrunnlerK.Explore
    open ProofTools ProofTools.Explore BrunnlerK
    abbrev a : Form := .atom 4      -- a name for each proposition used

## A sequent

`seq[A, B, [C, [D]], []]`: formulas, and boxes in square brackets. A
proposition is a number, `Form.atom n`; the printer names the first
eight `p q r s a b c d`.

| typed | abbreviation | meaning |
|---|---|---|
| `A ⋎ B` | `\curlyvee` | `A ∨ B` |
| `A ⋏ B` | `\curlywedge` | `A ∧ B` |
| `◇A`, `□A` | `\Diamond`, `\Box` | |
| `∼A` | `\sim` | the negation `Ā`: a function, `∼(a ⋏ b)` is `∼a ⋎ ∼b` |
| `A ⊃ B` | `\ssup` | `∼A ⋎ B` |

A place in a sequent is a **path**: `[]` the root, `[0]` its first box,
`[0, 1]` the second box of its first box. Boxes are counted from 0 in
the order shown. `Γ.show` is the sequent as the source displays it;
`Γ.tree` draws it as its tree.

## A goal

A goal is an attempt at a sequent. The infoview shows it as `Att S` and
the sequent: `Att S   ◇(ā ∧ b̄), ◇b, [a]`. Begin with
`example : Att S true seq[…] := by`, or `def d : Der S seq[…] := by`
for a proof that is to be finished.

## The moves

Each move is a rule of Figure 2.3, read upwards, at the node at the path
`a`.

| move | the node has | premises |
|---|---|---|
| `ax a n` | the proposition numbered `n` and its negation | none |
| `and a A B` | `A ∧ B` | two: `A` in its place; `B` in its place |
| `or a A B` | `A ∨ B` | one: `A, B` in its place |
| `box a A` | `□A` | one: a new box `[A]` in its place, after the node's boxes |
| `dia a i A` | `◇A`, and a box at position `i` | one: `A` put into that box; `◇A` stays |

What a rule adds is put in front of the node's formulas. There is no move
for `cut`.

## The lines of `kmove`

| line | what it does |
|---|---|
| `kmove box [] a` | the move, at goal 0 |
| `kmove … at 1` | at goal 1 |
| `kmove` | lists the moves that apply at goal 0; makes none |
| `kmove an` | lists those whose names begin with `an` |
| `kmove and` | the move with its arguments left out: made if one such applies, else each is offered |
| `kmove dia _ _ b` | `_` for any argument |
| `kmove where` | draws the attempt, goal 0 marked `>` |
| `apply_script ls` | runs a script, a closed term of type `Script S` |
| `leave_open` | leaves a goal open, with no error; `all_goals leave_open` for all |

A `◇k_c` that would put into a box a formula the box has is set aside:
it is offered only where nothing else applies.

## The messages

When a move does not apply: `the move does not apply to goal 0:` and one
of

    the sequent has no node at this path
    the proposition is not in the node
    the negated proposition is not in the node
    the conjunction is not in the node
    the disjunction is not in the node
    the formula □A is not in the node
    the formula ◇A is not in the node
    the node has no box at this position

A query where nothing applies: `kmove: no move applies at goal 0`. A
pattern that several moves fit makes none and offers each.

## A derivation as data

For `d : Der S Γ` (or an attempt):

| | |
|---|---|
| `d.script` | its lines; `apply_script d.script` rebuilds it |
| `d.cert` | its tree of moves |
| `#walk d`, `#walk d down 0 …` | drawn, with the motions offered |
| a block with goal `Walk d` | a line for each motion: `down i`, `up`, `left`, `right`, `top`, `goal k` |
| `famOfDer d : K Γ` | the proof in system K as the source states it |

## Tactics of the calculus, and the search

| | |
|---|---|
| `routine n Γ` | a script for the steps that need no choice: the axiom, `∨`, `∧`, `□` |
| `found Γ` | the script of the proof the search finds, or `none` |
| `auto n Γ` | a blind search: the first move that adds something, never taken back |
| `prove? Γ` | the search's proof as a tree of moves, or `none` |
| `refute? Γ` | the search's countermodel, a finite tree, or `none` |

Use one at a goal by `apply_script (routine 20 seq[…]).getD []`: the
sequent is written out again. A finite tree is
`Tree.node [propositions true here] [children]`.

## Facts, checked by the kernel

    example : Valid seq[…] := by decide +kernel          -- the kernel runs the search
    example : ¬ Valid seq[…] := by decide +kernel
    def d : K seq[…] := treeCert.verdict _ c             -- c a tree of moves
    theorem t : ¬ Valid seq[…] := noValid.verdict _ t    -- t a finite tree

`ksearch` (`lake build ksearch`) is the search compiled; `ksearch facts`
writes such facts for the corpus.

## From the command line

`ksearch prove '<sequent>'` answers for a sequent typed at a shell, with
no Lean file written first (`lake build ksearch`; the program is
`.lake/build/bin/ksearch`):

    ksearch prove '[](a -> b) -> ([]a -> []b)'
    ksearch prove '<>(~a & ~b), []a, <>b'
    ksearch prove --short '<>~a, [a, []], []'

| | the signs of a keyboard | also read |
|---|---|---|
| a proposition | `p q r s a b c d`, then `p8`, `p9`, … | `p0` … `p7`, `Form.atom n` |
| `Ā` | `~A`, `!A` | `¬A`, `∼A`; `p̄` as it is printed; `Form.natom n` |
| `A ∧ B`, `A ∨ B` | `A & B`, `A \| B`; `/\`, `\/` | `∧ ⋏`, `∨ ⋎` |
| `A ⊃ B` | `A -> B` | `⊃`, `→` |
| `◇A`, `□A` | `<>A`, `[]A` | `◇ ⋄`, `□` |
| a sequent | members separated by commas | `seq[ … ]` around the whole |
| a box | `[ … ]`; the empty box `[]` | `[∅]` |
| the empty sequent | nothing, or `seq[]` | `∅` |

`&` binds tighter than `|`, and `|` tighter than `->`; `&` and `|` group
to the left, `->` to the right; `~`, `<>`, `[]` take the formula that
follows them: as in a Lean file. **`[]` is two things**: before a formula
it is `□`, before a comma, a closing bracket or the end it is the empty
box. So `[]a` is `□a`, `[[]a]` is the box `[□a]`, and `[], a` is the
sequent `a, [∅]`. Formulas and boxes may be mixed; the formulas keep
their order and the boxes theirs, as in `seq[…]`. Quote the text: most
of these signs mean something to a shell.

Negation and `->` are functions, as in a Lean file: the sequent read is
in negation normal form, and that is what the first line shows.
`[](a -> b) -> ([]a -> []b)` is answered `-- derivable: ◇(a ∧ b̄) ∨ (◇ā ∨ □b)`.
Look at the first line: a text misread is another question.

| the answer | exit code | what is printed after the first line |
|---|---|---|
| `derivable` | 0 | a Lean file: `def moves`, the tree of moves; `theorem checked : treeCert.check sequent moves = true`; `def proof : K sequent := treeCert.verdict _ moves checked`; `theorem derivable : Derivable sequent` |
| `not derivable` | 1 | a Lean file: `def countermodel : Tree`, a finite tree; `theorem checked : noValid.check sequent countermodel = true`; `theorem notValid : ¬ Valid sequent` and `theorem notDerivable : ¬ Derivable sequent`, each `verdict` with `checked` |
| `flag` | 3 | one line: no answer within the deadline |
| the text is not a sequent | 2 | nothing; on the error stream, what is wrong, the text, and a mark under the place (characters are counted from 1) |

The program is not trusted, and neither is its first line. The Lean file
is what the kernel checks: `ksearch prove '…' > Fact.lean`, then `lake
env lean Fact.lean` from `calculi/BrunnlerK/`, is silent where the answer
holds. The file ends with the bound `[propext, Quot.sound]` on its
axioms. Every sequent is derivable or has a finite countermodel
(`decided`), and the search finds which: a `flag` is a search cut off,
not a third answer of the logic. (It would also be printed if what the
search returned did not pass the check, a defect.)

`--short` prints the first line only; `--ascii` writes the sequent in
it with the signs of a keyboard; `--deadline=N` is the number of seconds
the answer may take (10 where it is not given).

Every file lifts Lean's limits on recursion and on its own work
(`maxRecDepth`, `maxHeartbeats`), and states its check once, as the
theorem `checked`, which each fact is then given. **A large answer may be
beyond what Lean checks**, though the search prints it in a second. With
8 GB of memory and 240 s, the largest seen checked were a tree of 2 335
moves (`boxAnd 64`, 12 s), a derivable sequent nested 385 deep
(`nest 384`, 27 s) and a countermodel of 131 071 nodes (`tree 16`, 50 s);
`boxAnd 96` (5 039 moves) was cut off at 240 s and `nest 512` stopped at
8 GB. For an answer larger than those seen checked the first line says
what it rests on:

    -- derivable, on the program's check (a certificate larger than any Lean was seen to check): …

The file is printed all the same, and the exit code is the same; the
answer is then the program's, by the check it compiled, and not the
kernel's until a machine with more memory or time has elaborated the
file. The table: `campaign/measurements-2026-11-23.md`, "`ksearch prove`
beyond the corpus".

`ksearch corpus` prints the corpus as texts, and `ksearch show <family>
<n>` a member of a family: `ksearch prove "$(ksearch show boxAnd 8)"`.
`python3 Corpus/prove_corpus.py --elaborate` runs the command on every
entry of the corpus and elaborates what it prints;
`python3 Corpus/prove_families.py <family>:<n> …` does the same for
members of the families, with the times. The text is taken from the
command line only: one longer than the operating system gives a command
line (about a megabyte here) cannot be asked.

## The theorems

For `K` (proofs in system K) and `Kcut` (with `cut`); all within
`[propext, Quot.sound]`. The statements: `campaign/statements.md`.

| | |
|---|---|
| `soundness`, `soundnessCut` | a provable sequent is valid |
| `complete`, `completeness` | a valid sequent has a proof: the search's |
| `search`, `proofOrRefutation` | a proof, or a finite tree that refutes |
| `validDecidable` | validity is decidable |
| `finiteModelProperty` | not valid: refuted in a finite two-valued model |
| `cutElim`, `cutElimination` | from a proof with `cut`, a proof without |
| `nec`, `wk`, `ctr`, `exchange` | the structural rules, each no deeper |
| `inv_andL_C`, `inv_andR_C`, `inv_or_C`, `inv_box_C` | the inverse rules, each no deeper |
| `Fam.gaxC` | `Γ{A, Ā}` for every formula |
| `Fam.axC`, `Fam.andC`, `Fam.orC`, `Fam.boxC`, `Fam.diaC`, `Fam.cutC` | the rules as the figures print them, for a context |

## What is not there

* `ksearch prove` gives the proof the search finds, and the countermodel
  as a term. It does not draw either, and takes no proof from the user.
* A goal is shown in brackets; as a tree only by `Γ.tree`, on request.
* No tactic applies a tactic of the calculus, or the search, to the goal
  in front of it: the sequent is written out again.
* No move for `cut`, and no rule in the figure's shape among the moves.
* System K° is transcribed (`FamO`) and nothing is proved of it.
* Nothing for the other systems of the source (`d`, `t`, `b`, `4`, `5`).
