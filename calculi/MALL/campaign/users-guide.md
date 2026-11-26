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
| `by decide +kernel` on `Derivable Γ`, `¬ Derivable Γ`, `Valid Γ`, `¬ Valid Γ` | a theorem | yes: the kernel runs the proved search. Practical to about eight formulas with ⊗ (`measurements.md`) |
| `treeCert.verdict Γ c` | a derivation `Fam Γ`, from a tree of moves `c` | yes: the kernel checks the tree |

## Out to the mathematics

`famOfDer d : Fam Γ` is the derivation of the calculus as the source
states it. From there: `soundness`, `completeness`, `cutElimination _ d`
(a derivation without cut, `CF Γ`), `disjunctionProperty`,
`finite_countermodel` (`statements.md` has each).
