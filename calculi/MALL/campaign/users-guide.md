# MALL: a user's guide

How to use the linear sequent calculus of `calculi/MALL/` in the Lean
editor: how a goal reads, the moves, the lines of the tactic, the
messages, and what can be asked of the searches. A tour with every step
worked is `Play/MALLTutorial.lean`; exercises are `Play/MALL.lean`.

    (cd ~/Lean/Sources/proof-tools/calculi/MALL && lake build)

## How a goal reads

A goal `Att S true Γ`, or `Der S Γ`, is shown as

    Att S   ⊢ p⊥, q ⊗ r, ⊤

a sequent of Girard's calculus: a list of formulas, read as a multiset.
The order never matters and there is no move for exchange. Every formula
must be used exactly once: there is no weakening and no contraction.

| you type | it is printed | the source writes |
|---|---|---|
| `p`, `q`, `r`, `s` (declared in the file as `.atom 0` …) | `p` | a, b, c |
| `pᗮ` | `p⊥` | a^⊥ |
| `𝟏`, `⊥`, `⊤`, `𝟎` (or `.one`, `.bot`, `.top`, `.zero`) | `1`, `⊥`, `⊤`, `0` | **1**, ⊥, ⊤, **0** |
| `A ⊗ B`, `A ⅋ B`, `A & B`, `A ⊕ B` | the same | the same |
| `Aᗮ` on any formula | its negation, worked out: `(p ⊗ q)ᗮ` is `p⊥ ⅋ q⊥` | A^⊥ |

Two things to know when typing a formula:

* put a compound formula inside another in parentheses. The notations
  have precedences (⊗ and & bind tighter than ⅋ and ⊕), but the printer
  always parenthesises, and the source gives none;
* `⊕` is also Lean's sign for a sum of types, which binds more loosely.
  Inside `[…]` and in the arguments of a move it reads as the formula.
  Directly before `::` or `∈` it does not: write `(A ⊕ B) :: Γ`. The
  error, when it comes, names `Sum`.

## The moves

| move | applies to | leaves |
|---|---|---|
| `ax A` | `⊢ A, A⊥` and nothing else, in either order | nothing |
| `cut A [Γ]` | any sequent `⊢ Γ, Δ` of which `Γ` is a part | `⊢ A, Γ` and `⊢ A⊥, Δ` |
| `top` | a sequent with `⊤` | nothing |
| `wth A B` | a sequent with `A & B` | `⊢ A, Γ` and `⊢ B, Γ` |
| `plus₁ A B` | a sequent with `A ⊕ B` | `⊢ A, Γ` |
| `plus₂ A B` | a sequent with `A ⊕ B` | `⊢ B, Γ` |
| `one` | `⊢ 1` and nothing else | nothing |
| `bot` | a sequent with `⊥` | `⊢ Γ` |
| `tensor A B [Γ]` | a sequent `⊢ A ⊗ B, Γ, Δ` of whose context `Γ` is a part | `⊢ A, Γ` and `⊢ B, Δ` |
| `par A B` | a sequent with `A ⅋ B` | `⊢ A, B, Γ` |

`Γ` in `tensor` and `cut` is a list, `[pᗮ, q]` or `[]`: what goes to the
first premise. The rest goes to the second. There is no rule for `0`.
The connective & is "with"; its move is `wth` because `with` is a
keyword of Lean.

## The lines of the tactic

    mallmove               the moves that apply at goal 0; none is made
    mallmove te            those whose names begin with `te`
    mallmove par           a move with its arguments left out: made if only
                           one move of that form applies, else each is offered
    mallmove tensor p _ _  `_` or `?_` for any argument
    mallmove … at 1        the same at goal 1
    mallmove where         the attempt so far, drawn, with goal 0 marked `>`
    apply_script ls        the lines of a stored script
    leave_open             leaves the first goal open (`all_goals leave_open`)

A query lists every split of each ⊗ of the sequent (2ⁿ for a context of
n formulas, less the repetitions). It lists no cut: the cut formula is
yours to choose. Put a comment on a line of its own, never after a
pattern.

## The messages

| message | what it says |
|---|---|
| `mallmove: no move applies at goal 0` | the sequent is the conclusion of no rule: for instance `⊢ p`, `⊢ 1, 1`, `⊢ 0, p`, the empty sequent |
| `ax: the sequent is not ⊢ A, A⊥` | something is left over, or missing |
| `1: the sequent is not ⊢ 1` | the rule 1 takes no context (no weakening) |
| `⊤: ⊤ is not in the sequent`, and the same for `⊥`, `&`, `1⊕`, `2⊕`, `⅋` | the principal formula is not there |
| `⊗: the formula is not in the sequent, or the context named for the first premise is not part of the rest` | a formula of `[Γ]` is not in the sequent, or is there fewer times than you named it (no contraction) |
| `cut: the context named for the first premise is not part of the sequent` | the same, for cut |

## Looking at a derivation

`#walk d` draws a derivation at its root and offers the motions (`down
i`, `up`, `left`, `right`, `top`, `goal k`); a block `example : Walk d
:= by` takes one motion to a line and shows the view in the infoview.
`d.script` is the list of its lines, `d.cert` its tree of moves,
`d.render` the whole derivation as text.

## Asking the searches

| | what it gives | trusted? |
|---|---|---|
| `routine n Γ` | a script of the steps that lose nothing (the axioms, ⅋, ⊥, &), at every goal they leave; what remains has only ⊗ and ⊕ to try | no: `apply_script` checks it |
| `found Γ` | the script of the derivation the search by lazy splitting finds | no: checked |
| `explain Γ` (with `#eval IO.println`) | the derivation drawn, or "not derivable", with a small phase structure that refutes the sequent where the enumeration has one | no: to be read |
| `by decide +kernel` on `Derivable Γ`, `¬ Derivable Γ`, `Valid Γ`, `¬ Valid Γ` | a theorem | yes: the kernel runs the proved search. Practical to between 6 and 12 formulas where ⊗ must split (`measurements.md`) |
| `treeCert.verdict Γ c` | a derivation `Fam Γ`, from a tree of moves `c` | yes: the kernel checks the tree |
| `refuteBy Γ` | a phase structure on a small cyclic group that refutes `Γ`, where it finds one among those it tries | no: checked by the next line |
| `noDerivableBy.verdict Γ z`, `noValidBy.verdict Γ z` | `¬ Derivable Γ`, `¬ Valid Γ`, from a structure `z = ⟨k, bot, val⟩` on ℤ/(k+1): the antiphases and a set for each letter, as lists of Booleans | yes: the kernel computes the interpretation |
| `refuteSet Γ` | a saturated set of sequents of which `Γ` is a member, for every `Γ` with no derivation (it always ends; the set can be large where ⊗ divides a context many ways) | no: checked by the next line |
| `noDerivableBySet.verdict Γ D`, `noValidBySet.verdict Γ D` | `¬ Derivable Γ`, `¬ Valid Γ`, from a set `D` written as lists of formulas: the kernel checks that `Γ` is in it and that every rule that could conclude a member has a premise in it | yes; for a set of a few tens of sequents (the kernel's memory doubles with each formula beside a ⊗: `measurements.md`) |
| `Encode.encode D Γ` | the set `D` written in numbers, a `CodeCert`: a table of its formulas, a search tree of numbers, one for each sequent | no: checked by the next line |
| `noDerivableByCode.verdict Γ C`, `noValidByCode.verdict Γ C`, `countermodel_of_code` | the same two facts, and the finite phase structure, from a set written in numbers; `C.sequents` is the set of sequents it stands for, and `refutedBy_of_code` says that set passes the check of the line above | yes: this is the form to use, and the one `mallrun prove` writes |
| `describeCountermodel Γ` (with `#eval IO.println`) | the set, and the finite phase structure it presents: how many phases, and that the sequent, computed in it, does not hold | no: to be read |
| `(craigInterpolation Γ Δ d).C` | the interpolant of `⊢ Γ, Δ` computed from a derivation without cut `d : CF (Γ ++ Δ)`; the fields `.left`, `.right` are the two derivations | yes: a function proved by its type |
| `forallP p A`, `existsP p A`, `ui p Γ` | the uniform interpolants for the letter numbered `p`: the weakest formula without it that implies `A`, the strongest that `A` implies | yes: `ui_spec`. The kernel computes them (`by decide +kernel`) |

## A sequent typed at a shell

With no Lean file open:

    (cd ~/Lean/Sources/proof-tools/calculi/MALL && lake build mallrun)
    (cd ~/Lean/Sources/proof-tools/calculi/MALL && .lake/build/bin/mallrun prove 'p * q -o q * p')

The first line of the answer is a comment: the verdict, `derivable`,
`not derivable` or `flag`, and the sequent as it was read. After it comes
a Lean file that states the fact with its certificate; saved in
`calculi/MALL` and given to `lake env lean`, it is checked by the kernel.

| you type | it is |
|---|---|
| `p q r s`, `a4`, `a5`, … | the letters (`a0` is `p`) |
| `A^`, `A⊥`, `Aᗮ` after a formula; `~A` before one | the dual of `A` |
| `1`, `bot`, `top` (or `T`), `0` | the units 1, ⊥, ⊤, 0 |
| `A * B`, `A \| B` (or `A par B`), `A & B`, `A + B` | ⊗, ⅋, &, ⊕ |
| `A -o B` | `A ⊸ B`, which is `A⊥ ⅋ B` |
| `A, B` or `\|- A, B` | the sequent `⊢ A, B` |
| `A, B \|- C, D` | two-sided: read as `⊢ A⊥, B⊥, C, D` |

The signs the calculus prints (`⊗ ⅋ ⊕ ⊸ ⊤ ⊥ 𝟏 𝟎 ⊢`) and Lean's list
`[A, B]` are read as well. ⊗ binds tighter than &, & than ⅋, ⅋ than ⊕,
and ⊸ least; each groups to the right, as in Lean.

Three things to know:

* **The first line shows what was computed, not what was typed.** The
  dual and ⊸ are functions: `~(p * q)` is shown as `p⊥ ⅋ q⊥`, and
  `p * q -o q * p` as `(p⊥ ⅋ q⊥) ⅋ (q ⊗ p)`. A two-sided text is shown
  one-sided, its left formulas negated.
* **`⊥` is the unit where a formula is expected and the dual after
  one**: `⊥ ⅋ p` has the unit, `p⊥` is the dual of `p`, `⊥⊥` is 1. On a
  keyboard `bot` is the unit only and `^` the dual only.
* **The "no" side** is a phase structure on a small cyclic group where
  one is found, and otherwise a saturated set of sequents. Either gives
  `¬ Derivable` and `¬ Valid`.
* **A saturated set is written in numbers** (`MALL/Coded.lean`): a table
  of its formulas, and one number for each sequent, whose digit at a
  formula's place is how many times the formula occurs. The printed
  file names the check (`refuted`), and from it states that the set of
  sequents the numbers stand for passes the check of saturated sets
  (`refutedAsSequents`), `notDerivable`, `notValid` and `countermodel`.
  To read the sequents: `#eval refutation.sequents` at the end of the
  file.
* **A "not derivable" that the kernel may not check says so in its first
  line.** A saturated set can be large. Above 600 sequents its check is
  stated in several theorems, so that the kernel's memory stays that of
  one part. Under a cap of 4 GB of memory the kernel checked the printed
  file for every set tried, up to 11 110 sequents (a sequent of eight
  formulas; 102 s); its time grows with the set, about 9 ms a sequent
  there. Above 11 110 the first line reads

      -- not derivable, by the compiled check only (a set of N sequents; the kernel has checked sets of up to 11110): ⊢ …

  and the exit code is still 1. A plain `-- not derivable:` is an answer
  of a size the kernel has been seen to check: a cyclic phase structure,
  or a set of at most 11 110 sequents. In every case the fact is the file's, once
  it is elaborated; the first line is the program's, which is not
  trusted. (Until 2026-11-27 the set was written as lists of formulas,
  and the bound was 102 sequents under 8 GB: `measurements.md`.)

Options: `--short`, the first line only; `--ascii`, the sequent in it
with the signs of a keyboard; `--deadline=N`, seconds, 10 if not given.
The exit code is 0 for derivable, 1 for not derivable, 3 for a flag and
2 for a text that is not a sequent, which is refused on the error stream
with the place of the fault. The logic is decidable, so a flag is a
search cut off at the deadline: a sequent with no derivation, many ⊗,
and no small countermodel. `mallrun corpus` lists the corpus as texts.

## Out to the mathematics

`famOfDer d : Fam Γ` is the derivation of the calculus as the source
states it. From there: `soundness`, `completeness`, `cutElimination _ d`
(a derivation without cut, `CF Γ`), `disjunctionProperty`,
`finite_countermodel` (`statements.md` has each).
