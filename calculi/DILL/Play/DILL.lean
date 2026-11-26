/-
# `Play/DILL.lean`: dual intuitionistic linear logic, a move at a time

A file for a person who wants to try the calculus.  The operator prepared
it (2026-11-26) and runs every exercise in the tests (`DILL/Test.lean`,
section 10); a change to it after its first commit is recorded
(`campaign/decisions.md`).  It is in no library: no `lake build` builds it
and nothing imports it.  Build the instance first (`lake build DILL.Tactic`
in `calculi/DILL/`), then open this file in the editor and type.

`dillmove` is `apply_move` of proof-tools, fixed to DILL (declared in
`DILL/Tactic.lean`).  A goal is an attempt `Att S true j`, shown as
`Att S   Γ ; Δ ⟹ C`: a sequent of Chang, Chaudhuri and Pfenning's calculus
(CMU-CS-03-131R, Figure 2, p. 12).  `Γ` is the unrestricted zone: its
hypotheses are valid, and each may be used as often as you like, or not at
all.  `Δ` is the linear zone: each of its hypotheses must be used exactly
once (no weakening, no contraction), and their order never matters.  `C`
is the one conclusion.  An empty zone is shown as `·`.

**How to type a sequent.**  `Γ ⨾ Δ ⟹ C` in parentheses, with a list for
each zone: `([] ⨾ [p, p ⊸ q] ⟹ q)` is `· ; p, p ⊸ q ⟹ q`.  The sign
between the zones is `⨾` (U+2A3E; copy it from here), because `;` is
Lean's own; the arrow is `⟹` (`\Longrightarrow`).

**How to type a formula.**  Letters `p q r s`; the constants `𝟏 ⊤ 𝟎` (or
`.one .top .zero`); `A ⊗ B`, `A ⊸ B`, `A & B`, `A ⊕ B`, `!A`.  Two traps,
both of core Lean:

* `!` is also Lean's Boolean "not", and takes all that follows.  Write
  `(!p)` wherever an operator comes after it, and as a move's argument, as
  the lines offered do: `(!p) ⊗ (!q)`, `(!p) ⊸ q`, `dillmove bangR (!p)`.
  (`!p ⊗ q` is an error, "expected to have type Bool".)  Between the
  commas of a list, and last in a sequent, `!p` alone is read rightly:
  `[!p, q]`, `⟹ !p`, `⟹ !(p & q)`.
* `⊕` is also Lean's sum of types, which binds loosely.  Write `(p ⊕ q)`
  in parentheses wherever `⊸` comes after it: `(p ⊕ q) ⊸ r`.  (`p ⊕ q ⊸ r`
  is an error that names `Sum`.)

Put every compound formula that is a move's argument in parentheses:
`dillmove tensorL p (q ⊕ r)`.

**How to type a line.**

    dillmove                 the moves that apply at goal 0; none is made
    dillmove te              those whose names begin with `te`
    dillmove tensorL         `tensorL` with its arguments left out: made if
                             only one move of that form applies, else each
                             is offered
    dillmove tensorR _ _ [p] `_` or `?_` for any argument
    dillmove … at 1          the same at goal 1
    dillmove where           the attempt so far, drawn, with goal 0 marked
                             `>`; no move is made

Click an offered line to write it in place of yours.  A line that offers
makes no move.  A line that nothing completes is an error, and so is a
query where no move applies.  The first line offered is not the one to
prefer: the rules that lose nothing (⊸R, &R, ⊗L, 1L, ⊕L, !L) are safe to
make at once, and ⊗R, ⊸L, ⊕R, &L, !R and copy are choices.

**The rules** (each is a constructor of `Fam` in `DILL/System.lean`, with
its place in the source; keep the source's Figure 2 beside this file).
The conclusion is on the left, what the move leaves on the right.

    init            Γ ; A ⟹ A, the linear zone exactly A   no premise
    copy A          Γ ; Δ ⟹ C, with A in Γ                 Γ ; A, Δ ⟹ C
    tensorL A B     Γ ; Δ, A ⊗ B ⟹ C                       Γ ; A, B, Δ ⟹ C
    tensorR A B [Δ] Γ ; Δ, Δ′ ⟹ A ⊗ B                      Γ ; Δ ⟹ A   and   Γ ; Δ′ ⟹ B
    oneL            Γ ; Δ, 1 ⟹ C                           Γ ; Δ ⟹ C
    oneR            Γ ; · ⟹ 1, the linear zone empty       no premise
    lolliL A B [Δ]  Γ ; Δ, Δ′, A ⊸ B ⟹ C                   Γ ; Δ ⟹ A   and   Γ ; B, Δ′ ⟹ C
    lolliR A B      Γ ; Δ ⟹ A ⊸ B                          Γ ; A, Δ ⟹ B
    withL₁ A B      Γ ; Δ, A & B ⟹ C                       Γ ; A, Δ ⟹ C
    withL₂ A B      Γ ; Δ, A & B ⟹ C                       Γ ; B, Δ ⟹ C
    withR A B       Γ ; Δ ⟹ A & B                          Γ ; Δ ⟹ A   and   Γ ; Δ ⟹ B
    topR            Γ ; Δ ⟹ ⊤                              no premise
    zeroL           Γ ; Δ, 0 ⟹ C                           no premise
    plusL A B       Γ ; Δ, A ⊕ B ⟹ C                       Γ ; A, Δ ⟹ C   and   Γ ; B, Δ ⟹ C
    plusR₁ A B      Γ ; Δ ⟹ A ⊕ B                          Γ ; Δ ⟹ A
    plusR₂ A B      Γ ; Δ ⟹ A ⊕ B                          Γ ; Δ ⟹ B
    bangL A         Γ ; Δ, !A ⟹ C                          Γ, A ; Δ ⟹ C
    bangR A         Γ ; · ⟹ !A, the linear zone empty      Γ ; · ⟹ A
    cut A [Δ]       Γ ; Δ, Δ′ ⟹ C                          Γ ; Δ ⟹ A   and   Γ ; A, Δ′ ⟹ C
    cutU A          Γ ; Δ ⟹ C                              Γ ; · ⟹ A   and   Γ, A ; Δ ⟹ C

`tensorR`, `lolliL` and `cut` divide the linear zone: you name `Δ`, what
goes to the first premise, as a list, and the rest goes to the second.  A
query offers every division of `tensorR` and `lolliL`.  No cut is offered:
you choose its formula.  The subscripts of `withL₁`, `plusR₂` are typed
`\1`, `\2`, or clicked from a query.

`all_goals leave_open` at the end of an exercise leaves what is not yet
proved open, without an error.  When a proof is done, delete that line and
change `Att S true` to `Der S`: a derivation, which `famOfDer` carries to a
derivation of the calculus as the source states it (`Fam true`).

Reference derivations: `DILL/Test.lean`.  They are not in this file on
purpose.
-/
import DILL.Tactic

open ProofTools ProofTools.Explore DILL

-- The lines the tactic suggests write a letter by a name (`p`).  Declare
-- each letter under that name here, so that a suggested line can be
-- clicked and still parses.
abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2
abbrev s : Form := .atom 3

/-! ## 1. `· ; p ⟹ p`, and `p ; · ⟹ p` (CCP p. 16: init, then copy)

The first is init.  In the second `p` is valid and not linear: init is
refused until `p` is copied into the linear zone. -/

example : Att S true ([] ⨾ [p] ⟹ p) := by
  dillmove
  all_goals leave_open

example : Att S true ([p] ⨾ [] ⟹ p) := by
  dillmove
  all_goals leave_open

/-! ## 2. `· ; p, p ⊸ q ⟹ q` (CCP p. 16: init twice, and ⊸L)

⊸L divides the linear zone: what do you give to the premise that proves
`p`?  The query offers both divisions; one of them stops. -/

example : Att S true ([] ⨾ [p, p ⊸ q] ⟹ q) := by
  dillmove
  all_goals leave_open

/-! ## 3. `· ; p & q ⟹ p` (CCP p. 17), and `· ; p ⊗ q ⟹ q ⊗ p`

In the second, make ⊗L before ⊗R: while `p ⊗ q` is one formula it can go
to one premise only. -/

example : Att S true ([] ⨾ [p & q] ⟹ p) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [p ⊗ q] ⟹ q ⊗ p) := by
  dillmove
  all_goals leave_open

/-! ## 4. Uncurrying: `· ; p ⊸ (q ⊸ r) ⟹ (p ⊗ q) ⊸ r`

⊸R and ⊗L first; then ⊸L twice, each with its division. -/

example : Att S true ([] ⨾ [p ⊸ (q ⊸ r)] ⟹ (p ⊗ q) ⊸ r) := by
  dillmove
  all_goals leave_open

/-! ## 5. ⊗ distributes over ⊕: `· ; p ⊗ (q ⊕ r) ⟹ (p ⊗ q) ⊕ (p ⊗ r)`

Make ⊕L before you choose between ⊕R₁ and ⊕R₂: the choice is not the same
in its two premises. -/

example : Att S true ([] ⨾ [p ⊗ (q ⊕ r)] ⟹ (p ⊗ q) ⊕ (p ⊗ r)) := by
  dillmove
  all_goals leave_open

/-! ## 6. A cut: the inversion of ⊸R (CCP p. 18)

`· ; (p ⊸ q) & r ⟹ p ⊸ q` is derivable.  The source inverts ⊸R by a cut:
from it, `· ; p, (p ⊸ q) & r ⟹ q`, by a cut on `p ⊸ q` against
`· ; p ⊸ q, p ⟹ q`.  The first line makes that cut; finish both premises.
Then derive the same sequent again without cut (delete the first line). -/

example : Att S true ([] ⨾ [p, (p ⊸ q) & r] ⟹ q) := by
  dillmove cut (p ⊸ q) [(p ⊸ q) & r]
  all_goals leave_open

/-! ## 7. Not derivable: `· ; p, q ⟹ p` (no weakening) and
`· ; p ⟹ p ⊗ p` (no contraction)

No move applies to the first as it stands, so a query there is an error
and the file has none: type `dillmove` yourself on a line before
`all_goals`; the message will be "dillmove: no move applies at goal 0".
Then type `dillmove init`: "the move does not apply to goal 0: init: the
linear zone is not exactly the conclusion".

For the second, go as far as the moves go.  What should happen: ⊗R has
two divisions, and each leaves a premise `· ; · ⟹ p`, where a query
answers "no move applies at goal 0". -/

example : Att S true ([] ⨾ [p, q] ⟹ p) := by
  all_goals leave_open

example : Att S true ([] ⨾ [p] ⟹ p ⊗ p) := by
  dillmove
  all_goals leave_open

/-! ## 8. The first laws of `!`: `· ; !p ⟹ p`, `· ; !p ⟹ 1`,
`· ; !p ⟹ !p ⊗ !p`

!L moves `p` to the unrestricted zone.  From there it is copied when it is
wanted: once in the first, never in the second, twice in the third.  In
the third the query offers ⊗R first: make !L before it, or `!p` goes to
one premise only. -/

example : Att S true ([] ⨾ [!p] ⟹ p) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [!p] ⟹ 𝟏) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
  dillmove
  all_goals leave_open

/-! ## 9. `· ; !p ⟹ !!p`, and not derivable: `· ; p ⟹ !p`

!R asks for an empty linear zone.  In the first, !L empties it.  In the
second nothing can: no move applies to it as it stands, so the file has no
query there.  Type `dillmove bangR p` yourself: "the move does not apply
to goal 0: !R: the conclusion is not this formula, or the linear zone is
not empty". -/

example : Att S true ([] ⨾ [!p] ⟹ !(!p)) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [p] ⟹ !p) := by
  all_goals leave_open

/-! ## 10. `!` turns & into ⊗: `· ; !(p & q) ⟹ !p ⊗ !q`, and back,
`· ; !p ⊗ !q ⟹ !(p & q)` -/

example : Att S true ([] ⨾ [!(p & q)] ⟹ (!p) ⊗ (!q)) := by
  dillmove
  all_goals leave_open

example : Att S true ([] ⨾ [(!p) ⊗ (!q)] ⟹ !(p & q)) := by
  dillmove
  all_goals leave_open

/-! ## 11. `· ; !p, !(p ⊸ q) ⟹ !q`

Both !L, then !R; then a valid `p ⊸ q` is of no use until it is copied. -/

example : Att S true ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q) := by
  dillmove
  all_goals leave_open

/-! ## 12. Not derivable: `· ; p ⊸ (q ⊗ r) ⟹ (p ⊸ q) ⊗ (p ⊸ r)`
(Pfenning's notes, p. 60)

Go as far as the moves go.  What should happen: three first moves apply.
Whichever you make, and whatever you make after it, some branch ends at a
sequent where a query answers "no move applies at goal 0": `· ; q, r ⟹ q`
if the implication goes to the first premise of ⊗R, `· ; p ⟹ q` if it goes
to the second, `· ; · ⟹ p` if ⊸L is first.  `dillmove where` draws the
attempt with what is open. -/

example : Att S true ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r)) := by
  dillmove
  all_goals leave_open

/-! ## To look at a derivation that is built

Name one and walk it.  With `#walk`, a click on an offered motion writes
it.  In a block whose goal is `Walk d`, each line is a motion (`down i`,
`up`, `left`, `right`, `top`, `goal k`) and the goal shows the view there. -/

def d : Der S ([] ⨾ [p, p ⊸ q] ⟹ q) := by
  dillmove lolliL p q [p]
  dillmove init
  dillmove init

#walk d
#walk d down 0

example : Walk d := by
  down 0
