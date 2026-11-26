# DILL: a user's guide

How to use the two-zone sequent calculus of `calculi/DILL/` in the Lean
editor: how a goal reads, the twenty moves, the lines of the tactic, the
messages, and which certificate answers what. A tour with every step
worked is `Play/DILLTutorial.lean`; the graded exercises of the tutorial
page (`tutorial.md`) are `Play/DILLExercises.lean`; a shorter file of
exercises is `Play/DILL.lean`. Everything this guide says about a
particular sequent or message is pinned in `DILL/TutorialTest.lean`.

    (cd ~/Lean/Sources/proof-tools/calculi/DILL && lake build)

## How a goal reads

A goal `Att S true j`, or `Der S j` after its first move, is shown as

    Att S   p ⊸ q, p ; !p, q ⊕ r ⟹ !p ⊗ 1

a sequent `Γ ; Δ ⟹ C` of Chang, Chaudhuri and Pfenning's calculus
(CMU-CS-03-131R, Figure 2).

* `Γ`, before the `;`, is the **unrestricted zone**: valid hypotheses,
  each usable any number of times, or not at all. Only copy uses one.
* `Δ`, after the `;`, is the **linear zone**: each hypothesis is used
  exactly once. There is no weakening and no contraction here.
* `C` is the one conclusion. `·` is an empty zone.

The order within a zone never matters and there is no move for
exchange. A goal stated as `Der S j` is printed by Lean as a term,
`Der S ([] ⨾ [p] ⟹ p)`, until the first move is made.

| you type | it is printed | the source writes |
|---|---|---|
| `Γ ⨾ Δ ⟹ C`, each zone a list: `([p] ⨾ [!p, q] ⟹ r)` | `p ; !p, q ⟹ r` | `Γ ; Δ ⟹ C ; ·` |
| `[]` | `·` | `·` |
| `p`, `q`, `r`, `s` (declared in the file as `.atom 0` …) | `p` | atomic propositions |
| `𝟏`, `⊤`, `𝟎` (or `.one`, `.top`, `.zero`) | `1`, `⊤`, `0` | **1**, ⊤, **0** |
| `A ⊗ B`, `A ⊸ B`, `A & B`, `A ⊕ B`, `!A` | the same | the same |

## The sign `⨾`, and the two notation traps

* **`⨾` is not `;`.** Lean's `;` separates tactics, so the sign between
  the zones is `⨾` (U+2A3E). The editor has no abbreviation for it: copy
  it from a line of the file. `⟹` is `\==>`. A move never needs either
  sign: only a sequent that you state does.
* **`(!A)`.** `!` is also Lean's negation of a Boolean, and Lean's takes
  everything that follows. `[!p, q]`, `⟹ !p`, `!(p & q)` and `!(!p)` are
  read as formulas. `!p ⊗ q` is an error: `The argument p ⊗ q has type
  Form but is expected to have type Bool`. Write `(!p) ⊗ q`,
  `(!p) ⊸ q`, `(!A) :: Δ`, and `dillmove bangR (!p)`: a `!` formula
  inside a formula, before `::`, or as the argument of a move, goes in
  parentheses. The lines that the tactic offers are written so.
* **`(A ⊕ B)`.** `⊕` is also Lean's sum of two types, which binds
  loosely. `[p ⊕ q]` and `p ⊗ q ⊕ r` are read as formulas. `p ⊕ q ⊸ r`
  and `p ⊕ q :: Δ` are errors that name `Sum`. Write `(p ⊕ q) ⊸ r`,
  `(A ⊕ B) :: Δ`, `(A ⊕ B) ∈ Δ`.
* **What Lean prints is not always what you type.** In a statement
  printed by Lean (`#check`, an error, the tutorial page's pins),
  `!A :: Δ` and `A ⊕ B :: Δ` appear without the parentheses they need.
* Put every compound formula that is a move's argument in parentheses:
  `dillmove tensorL p (q ⊕ r)`.
* Lean prints the type of sequents as `DILL.Seq`, because core Lean has
  a `Seq` of its own; `Seq` alone is accepted where `DILL` is open.

## The twenty moves

The conclusion is the goal; what a move leaves are the new goals. `Δ` in
brackets is a list, `[p, q]` or `[]`.

| move | rule | applies to | asks | leaves |
|---|---|---|---|---|
| `init` | init | `Γ ; A ⟹ A` | the linear zone is exactly the conclusion | nothing |
| `copy A` | copy | `Γ ; Δ ⟹ C` | `A` is in `Γ` | `Γ ; A, Δ ⟹ C` |
| `tensorL A B` | ⊗L | `Γ ; Δ, A ⊗ B ⟹ C` | `A ⊗ B` is in the linear zone | `Γ ; A, B, Δ ⟹ C` |
| `tensorR A B [Δ]` | ⊗R | `Γ ; Δ, Δ′ ⟹ A ⊗ B` | the conclusion is `A ⊗ B`; `Δ` is part of the linear zone | `Γ ; Δ ⟹ A` and `Γ ; Δ′ ⟹ B` |
| `oneL` | 1L | `Γ ; Δ, 1 ⟹ C` | `1` is in the linear zone | `Γ ; Δ ⟹ C` |
| `oneR` | 1R | `Γ ; · ⟹ 1` | the conclusion is `1`; the linear zone is empty | nothing |
| `lolliL A B [Δ]` | ⊸L | `Γ ; Δ, Δ′, A ⊸ B ⟹ C` | `A ⊸ B` is in the linear zone; `Δ` is part of the rest | `Γ ; Δ ⟹ A` and `Γ ; B, Δ′ ⟹ C` |
| `lolliR A B` | ⊸R | `Γ ; Δ ⟹ A ⊸ B` | the conclusion is `A ⊸ B` | `Γ ; A, Δ ⟹ B` |
| `withL₁ A B` | &L₁ | `Γ ; Δ, A & B ⟹ C` | `A & B` is in the linear zone | `Γ ; A, Δ ⟹ C` |
| `withL₂ A B` | &L₂ | `Γ ; Δ, A & B ⟹ C` | the same | `Γ ; B, Δ ⟹ C` |
| `withR A B` | &R | `Γ ; Δ ⟹ A & B` | the conclusion is `A & B` | `Γ ; Δ ⟹ A` and `Γ ; Δ ⟹ B` |
| `topR` | ⊤R | `Γ ; Δ ⟹ ⊤` | the conclusion is `⊤` | nothing |
| `zeroL` | 0L | `Γ ; Δ, 0 ⟹ C` | `0` is in the linear zone | nothing |
| `plusL A B` | ⊕L | `Γ ; Δ, A ⊕ B ⟹ C` | `A ⊕ B` is in the linear zone | `Γ ; A, Δ ⟹ C` and `Γ ; B, Δ ⟹ C` |
| `plusR₁ A B` | ⊕R₁ | `Γ ; Δ ⟹ A ⊕ B` | the conclusion is `A ⊕ B` | `Γ ; Δ ⟹ A` |
| `plusR₂ A B` | ⊕R₂ | `Γ ; Δ ⟹ A ⊕ B` | the same | `Γ ; Δ ⟹ B` |
| `bangL A` | !L | `Γ ; Δ, !A ⟹ C` | `!A` is in the linear zone | `A, Γ ; Δ ⟹ C` |
| `bangR A` | !R | `Γ ; · ⟹ !A` | the conclusion is `!A`; the linear zone is empty | `Γ ; · ⟹ A` |
| `cut A [Δ]` | cut | `Γ ; Δ, Δ′ ⟹ C` | `Δ` is part of the linear zone | `Γ ; Δ ⟹ A` and `Γ ; A, Δ′ ⟹ C` |
| `cutU A` | cut! | `Γ ; Δ ⟹ C` | nothing: it always applies | `Γ ; · ⟹ A` and `A, Γ ; Δ ⟹ C` |

* The argument of `bangL` and `bangR` is the formula under the `!`:
  `dillmove bangL p` is !L on `!p`, and `dillmove bangR (!p)` is !R at
  the conclusion `!!p`.
* `tensorR`, `lolliL` and `cut` divide the linear zone. You name what
  goes to the first premise; the rest goes to the second. A formula
  named twice must be there twice.
* The subscripts of `withL₁`, `plusR₂` are typed `\1`, `\2`, or clicked
  from a query.
* The rules that lose nothing, read upwards, are ⊗L, 1L, ⊸R, &R, ⊕L, !L,
  and !R where it applies. Make them first. The others are choices.
* copy applies whenever `Γ` is not empty, and again after it: nothing in
  the tactic stops an attempt that only copies.

## The lines of the tactic

    dillmove                   the moves that apply at goal 0; none is made
    dillmove te                those whose names begin with `te`
    dillmove bangL             a move with its arguments left out: made if only
                               one move of that form applies, else each is offered
    dillmove tensorR _ _ [p]   `_` or `?_` for any argument
    dillmove … at 1            the same at goal 1
    dillmove where             the attempt so far, drawn, with goal 0 marked `>`
    apply_script ls            the lines of a stored script
    leave_open                 leaves the first goal open (`all_goals leave_open`)

A query lists the rules that lose nothing first (init, 1R, ⊤R, 0L, 1L;
⊸R, &R; ⊗L, ⊕L, !L), then the choices (⊕R₁, ⊕R₂, !R, the divisions of
⊗R; &L₁, &L₂, the divisions of ⊸L), then a copy of each valid
hypothesis. Nothing in the list marks where the choices begin. It lists
every division of ⊗R and ⊸L (2ⁿ for a zone of n formulas, less the
repetitions), and the first division offered gives the first premise
nothing. It lists no cut: the cut formula is yours to choose. A filled
pattern is shown as "Try this", in full. Put a comment on a line of its
own, never after a pattern.

## The messages

A refusal reads `the move does not apply to goal 0:` and then one of
these.

| message | what it says |
|---|---|
| `dillmove: no move applies at goal 0` | a query, where the sequent is the conclusion of no rule but a cut: for instance `· ; · ⟹ p`, `· ; p ⟹ 1`, `· ; p ⟹ !p`, `· ; p, q ⟹ p` |
| `init: the linear zone is not exactly the conclusion` | something is left over in the linear zone, or the hypothesis is valid and not linear (copy it first) |
| `copy: the formula is not in the unrestricted zone` | |
| `⊗L`, `&L₁`, `&L₂`, `⊕L`, `!L`: `the formula is not in the linear zone`; `1L: 1 is not in the linear zone`; `0L: 0 is not in the linear zone` | the principal formula is not there; a valid hypothesis must be copied before a left rule acts on it |
| `⊗R: the conclusion is not this tensor` | |
| `⊗R: the zone named for the first premise is not part of the linear zone` | a formula of `[Δ]` is not in the linear zone, or is there fewer times than you named it (no contraction) |
| `1R: the conclusion is not 1` | |
| `1R: the linear zone is not empty` | a linear hypothesis would be dropped (no weakening) |
| `⊸L: the formula is not in the linear zone` | |
| `⊸L: the zone named for the first premise is not part of the rest of the linear zone` | as for ⊗R, in what is left without `A ⊸ B` |
| `⊸R: the conclusion is not this implication`; `&R`, `⊕R₁`, `⊕R₂`: `the conclusion is not this formula`; `⊤R: the conclusion is not ⊤` | |
| `!R: the conclusion is not this formula` | |
| `!R: the linear zone is not empty` | `!A` is derived from valid hypotheses only: make the !L first |
| `cut: the zone named for the first premise is not part of the linear zone` | |

## Looking at a derivation

`#walk d` draws a derivation at its root and offers the motions (`down
i`, `up`, `left`, `right`, `top`, `goal k`); a block `example : Walk d
:= by` takes one motion to a line and shows the view in the infoview.
`d.script` is the list of its lines, `d.cert` its tree of moves,
`d.render` the whole derivation as text (`#eval IO.println d.render`).

## Which certificate answers what

| the question | what to use | what it gives | trusted? |
|---|---|---|---|
| is this a derivation? | `treeCert.verdict j c`, with `c` a tree of moves `.mk move [subtrees]`; or `scriptCert.verdict j ls` | a derivation `Fam true j` | yes: the kernel runs the moves |
| is there a derivation? | `Run.proveLazy j n` | a tree of moves, found with at most `n` copies along a branch; `none` is "nothing at this budget", never "no" | no: checked by the line above |
| is there one, where `!` does not occur and `Γ` is empty? | `by decide` on `Nonempty (CF ([] ⨾ Δ ⟹ C))` or its negation, after `open DILL.Dec in`; `Sem.derivable_iff_cf` for `Derivable` | a theorem | yes: the kernel runs the search that is proved complete. Slow where ⊗R or ⊸L divides a long zone |
| is there none? | `noDerivableBySet.verdict j D`, `noCFBySet.verdict j D`, with `D` a saturated set of sequents of which `j` is a member | `¬ Derivable j`, `¬ Nonempty (CF j)` | yes: the kernel checks the saturation. Only for an empty `Γ` and a search that never meets `!` on the left |
| the set for it | `refuteSet j`; `Refute.outcome j` says why where there is none | a saturated set, or nothing | no: checked by the line above |
| is there none, with a valid hypothesis or a `!` on the left? | no producer. A phase model in which the sequent is not satisfied, and `soundness` (the counting model of the tutorial, 7.1) | `¬ Derivable j` | yes, once the model is written and the proof made by hand |
| either answer | `produce j n`, the producer of `dillEngine` | `pass` with a script, `fail` with a saturated set, or `flag` | no: each answer is checked. `flag` is neither |

With `!` derivability is undecidable (Lincoln, Mitchell, Scedrov and
Shankar 1992, Corollary 3.8), so there is no line of this table that
always answers. Measured sizes and times are in `measurements.md` and
`measurements-sat.md`.

## From the command line

`dillrun prove '<sequent>'` answers for a sequent typed at a shell, with
no Lean file written first (build it with `lake build dillrun`; the
program is `.lake/build/bin/dillrun`):

    dillrun prove '. ; p, p -o q => q'
    dillrun prove '!p, !(p -o q) => !q'
    dillrun prove --short 'p => p * p'

The text has the signs of a keyboard: `*` for ⊗, `-o` for ⊸, `+` for ⊕,
`&`, `!`, `1`, `0`, `T` for ⊤, `=>` for ⟹, `.` for an empty zone, and
`;` between the zones (with no `;` the zone given is the linear one).
The atoms are `p q r s`, then `a4`, `a5`, … The signs of the source are
read too. The connectives bind as in a Lean file: `!` closest, then `*`,
`&`, `+`, `-o`, each to the right. Quote the text: `;`, `&`, `*`, `!`
and the parentheses mean something to a shell. The grammar is at the
head of `DILL/Parse.lean`.

| the answer | exit code | what is printed after the first line |
|---|---|---|
| `derivable` | 0 | a Lean file with the derivation: `treeCert.verdict _ <tree>` |
| `not derivable` | 1 | a Lean file with a saturated set: `noDerivableBySet.verdict _ <set>` |
| `flag` | 3 | what the search did, and why there is no set |
| the text is not a sequent | 2 | what is wrong and at which character (on the error stream) |

The program is not trusted, and neither is its first line. The Lean file
is what the kernel checks: `dillrun prove '…' > Fact.lean`, then `lake
env lean Fact.lean` from this folder, is silent where the answer holds.
`--short` prints the first line only; `--ascii` writes the sequent in it
with the signs of a keyboard (the Lean file keeps the notations of
`DILL/Form.lean`); `--budget=<n>` is the number of copies allowed along
a branch (4 where it is not given). The first line names the sequent
that was read: look at it, since a text misread is another question.

## Out to the mathematics

`famOfDer d : Fam true j` is the derivation of the calculus as the
source states it. From there: `soundness`, `completeness`,
`cutElimination _ d` (a derivation without cut, `CF j`), the inversions
(`lolliRInv`, `bangLInv`, …), `toILL` and `ofILL` (the one-zone
calculus), `disjunctionProperty` (`statements.md` has each; the tutorial
page explains each proof).
