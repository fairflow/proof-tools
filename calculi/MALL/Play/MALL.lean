/-
# `Play/MALL.lean`: the linear sequent calculus (MALL), a move at a time

A file for a person who wants to try the calculus.  The operator prepared
it (2026-11-26) and runs every exercise in the tests
(`MALL/Test.lean`, section 10); a change to it after its first commit is
recorded (`campaign/decisions.md`).  It is in no library: no `lake build`
builds it and nothing imports it.  Build the instance first (`lake build`
in `calculi/MALL/`), then open this file in the editor and type.

`mallmove` is `apply_move` of proof-tools, fixed to MALL (declared in
`MALL/Tactic.lean`).  A goal is an attempt `Att S true j`, shown as
`Att S   ⊢ A₁, …, Aₙ`: a sequent of Girard's calculus (*Linear logic*,
1987, Definition 1.15), read as a multiset.  The order of the formulas
never matters, so there is no move for exchange; but every formula must be
used exactly once: there is no weakening and no contraction.

**How to type a formula.**  Letters `p q r` and their duals `pᗮ qᗮ rᗮ`
(type `\perp`-like `ᗮ` by copying it; it is printed `p⊥`); the constants
`𝟏 ⊥ ⊤ 𝟎` (or `.one .bot .top .zero`); `A ⊗ B`, `A ⅋ B`, `A & B`,
`A ⊕ B`.  `Aᗮ` is linear negation, a function: `(p ⊗ q)ᗮ` is `pᗮ ⅋ qᗮ`.
Put a compound formula in parentheses.

**How to type a line.**

    mallmove               the moves that apply at goal 0; none is made
    mallmove te            those whose names begin with `te`
    mallmove par           `par` with its arguments left out: made if only one
                           move of that form applies, else each is offered
    mallmove tensor p _ _  `_` or `?_` for any argument
    mallmove … at 1        the same at goal 1
    mallmove where         the attempt so far, drawn, with goal 0 marked `>`;
                           no move is made

Click an offered line to write it in place of yours.  A line that offers
makes no move.  A line that nothing completes is an error, and so is a
query where no move applies.

**The rules** (the table, with each rule's place in the source, is
`campaign/rule-table.md`; keep it and the source's p. 22 beside this file):

    ax A            ⊢ A, A⊥ and nothing else              no premise
    cut A [Γ]       ⊢ Γ, Δ                                ⊢ A, Γ   and   ⊢ A⊥, Δ
    top             ⊢ ⊤, Γ                                no premise
    wth A B         ⊢ A & B, Γ                            ⊢ A, Γ   and   ⊢ B, Γ
    plus₁ A B       ⊢ A ⊕ B, Γ                            ⊢ A, Γ
    plus₂ A B       ⊢ A ⊕ B, Γ                            ⊢ B, Γ
    one             ⊢ 1 and nothing else                  no premise
    bot             ⊢ ⊥, Γ                                ⊢ Γ
    tensor A B [Γ]  ⊢ A ⊗ B, Γ, Δ                         ⊢ A, Γ   and   ⊢ B, Δ
    par A B         ⊢ A ⅋ B, Γ                            ⊢ A, B, Γ

`tensor` and `cut` split the context: you name `Γ`, what goes to the first
premise, as a list, and the rest goes to the second.  A query offers every
split of `tensor`.  No `cut` is offered: you choose its formula.

`all_goals leave_open` at the end of an exercise leaves what is not yet
proved open, without an error.  When a proof is done, delete that line and
change `Att S true` to `Der S`: a derivation, which `famOfDer` carries to a
derivation of the calculus as Girard states it.

Reference derivations: `MALL/Test.lean`.  They are not in this file on
purpose.
-/
import MALL.Tactic

open ProofTools ProofTools.Explore MALL

-- The lines the tactic suggests write a letter by a name (`p`).  Declare
-- each letter under that name here, so that a suggested line can be
-- clicked and still parses.
abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2
abbrev s : Form := .atom 3

/-! ## 1. `A ⊸ A & A` (Girard, p. 5: it "is" derivable)

`A ⊸ B` is `A⊥ ⅋ B`.  The context `p⊥` is used in both premises of &. -/

example : Att S true [pᗮ ⅋ (p & p)] := by
  mallmove
  all_goals leave_open

/-! ## 2. The axiom at a compound formula, from axioms at letters
(the remark of p. 22)

`(p ⊗ q)ᗮ` is `pᗮ ⅋ qᗮ`.  Do not use `ax (p ⊗ q)`: use ⅋, then ⊗, and
choose the split. -/

example : Att S true [(p ⊗ q)ᗮ, p ⊗ q] := by
  mallmove
  all_goals leave_open

/-! ## 3. `1 ⊗ G = G` (1.9(ii)), as two sequents

The first uses the rule ⊥, the second the rule 1 and an empty split. -/

example : Att S true [(𝟏 ⊗ p)ᗮ, p] := by
  mallmove
  all_goals leave_open

example : Att S true [pᗮ, 𝟏 ⊗ p] := by
  mallmove
  all_goals leave_open

/-! ## 4. ⊗ distributes over ⊕ (1.13(i)), one half -/

example : Att S true [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
  mallmove
  all_goals leave_open

/-! ## 5. Half-distributivity (1.13(ii)): `G ⊗ (H & K) ⊂ (G ⊗ H) & (G ⊗ K)` -/

example : Att S true [(p ⊗ (q & r))ᗮ, (p ⊗ q) & (p ⊗ r)] := by
  mallmove
  all_goals leave_open

/-! ## 6. A cut

Derive `⊢ p⊥, q⊥, q ⊗ p` with a cut on `p ⊗ q`: the first premise is
`⊢ p ⊗ q, p⊥, q⊥`, the second `⊢ (p ⊗ q)⊥, q ⊗ p`.  Then derive it again
without cut. -/

example : Att S true [pᗮ, qᗮ, q ⊗ p] := by
  mallmove cut (p ⊗ q) [pᗮ, qᗮ]
  all_goals leave_open

/-! ## 7. Not derivable: `A ⊸ A ⊗ A` (Girard, p. 5)

Go as far as the moves go.  What should happen: after ⅋, every split of
the context at ⊗ leaves a premise `⊢ p`, where a query answers
"no move applies at goal 0" (an error). -/

example : Att S true [pᗮ ⅋ (p ⊗ p)] := by
  mallmove
  all_goals leave_open

/-! ## 8. Not derivable: `⊢ 1, 1` (no weakening)

No move applies to this sequent as it stands, so a query here is an error
and the file has none: type `mallmove` yourself on a line before
`all_goals`; the message will be "mallmove: no move applies at goal 0".
Then type `mallmove one`: "the move does not apply to goal 0: 1: the
sequent is not ⊢ 1". -/

example : Att S true [𝟏, 𝟏] := by
  all_goals leave_open

/-! ## 9. No contraction: `⊢ p ⊕ p⊥, p ⊕ p⊥` is derivable, `⊢ p ⊕ p⊥` is not -/

example : Att S true [p ⊕ pᗮ, p ⊕ pᗮ] := by
  mallmove
  all_goals leave_open

example : Att S true [p ⊕ pᗮ] := by
  mallmove
  all_goals leave_open

/-! ## 10. Not derivable: the converse of half-distributivity

`(G ⊗ H) & (G ⊗ K) ⊂ G ⊗ (H & K)` fails.  What should happen: the left
formula is `(p⊥ ⅋ q⊥) ⊕ (p⊥ ⅋ r⊥)`, so one of its two halves must be
chosen, and the right formula needs both `q` and `r`: whichever rule you
start with, some branch ends in a sequent of letters that is no axiom,
where a query answers "no move applies at goal 0". -/

example : Att S true [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)] := by
  mallmove
  all_goals leave_open

/-! ## To look at a derivation that is built

Name one and walk it.  With `#walk`, a click on an offered motion writes
it.  In a block whose goal is `Walk d`, each line is a motion (`down i`,
`up`, `left`, `right`, `top`, `goal k`) and the goal shows the view there. -/

def d : Der S [pᗮ, 𝟏 ⊗ p] := by
  mallmove tensor 𝟏 p []
  mallmove one
  mallmove ax p

#walk d
#walk d down 0

example : Walk d := by
  down 0
