/-
# `Play/GLS.lean`: the sequent calculus GLS for provability logic, a move at a time

A file for a person who wants to try the calculus.  The operator prepared
it (2026-11-25) and runs every exercise in the tests (`GLS/Test.lean`,
section 10); a change to it after its first commit is recorded
(`campaign/decisions.md`).  It is in no library: no `lake build` builds it
and nothing imports it.  Build the instance first (`lake build`, in
`calculi/GLS/`), then open this file in the editor and type.

`glsmove` is `apply_move` of proof-tools, fixed to GLS (declared in
`GLS/Tactic.lean`).  A goal is an attempt `Att S true j`, shown as
`Att S   Γ ⇒ Δ`: the sequent still to be derived, its antecedent and its
succedent as lists of formulas, read as multisets.  In this file formulas
are typed with `⟶` for the source's `→`, `□` and `⊥`; a goal is shown with
`→`.

**How to type a line.**

    glsmove              the moves that apply at goal 0; none is made
    glsmove im           those whose names begin with `im`
    glsmove impR         `impR` with its arguments left out: made if only one
                         move of that form applies, else each is offered
    glsmove impL p _     `_` or `?_` for any argument
    glsmove … at 1       the same at goal 1
    glsmove where        the attempt so far, drawn, with goal 0 marked `>`;
                         no move is made

Click an offered line to write it in place of yours.  A line that offers
makes no move.  A line that nothing completes is an error, and so is a
query where no move applies.

**The rules** (the table, with each rule's place in the source, is
`campaign/rule-table.md`):

    idP n      IdP: asks the variable numbered n on both sides (p is 0, q is 1); closes the goal
    botL       BotL: asks ⊥ in the antecedent; closes the goal
    impR A B   ImpR: asks A ⟶ B in the succedent; leaves  A, Γ ⇒ B, Δ'   (Δ' is Δ less one A ⟶ B)
    impL A B   ImpL: asks A ⟶ B in the antecedent; leaves  Γ' ⇒ A, Δ  and  B, Γ' ⇒ Δ
    glr A      GLR: asks □A in the succedent; leaves  B₁, □B₁, …, Bₙ, □Bₙ, □A ⇒ A
               where □B₁, …, □Bₙ are the boxed formulas of Γ.  Everything else is dropped.

`all_goals leave_open` at the end of an exercise leaves what is not yet
proved open, without an error.  When a proof is done, delete that line and
change `Att S true` to `Der S`: a derivation, which `famOfDer` carries to a
derivation of GLS as the source states it (`GLS.Fam`).

Reference derivations: `GLS/Test.lean`.  They are not in this file on
purpose.
-/
import GLS.Tactic

open ProofTools ProofTools.Explore GLS

-- The lines the tactic suggests write a variable by a name (`p`).
abbrev p : Form := .var 0
abbrev q : Form := .var 1

/-! ## 1. The identity on a formula that is not a variable

The source's own derivation (`Id_all_form`, l. 331 of the Coq file): IdP
is for variables only, and the identity on any formula is derived. -/

example : Att S true ([□p ⟶ q] ⇒ [□p ⟶ q]) := by
  glsmove
  all_goals leave_open

/-! ## 2. The axiom K -/

example : Att S true ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  glsmove
  all_goals leave_open

/-! ## 3. The axiom 4 -/

example : Att S true ([] ⇒ [□p ⟶ □□p]) := by
  glsmove
  all_goals leave_open

/-! ## 4. Löb's axiom

GLR is used twice, the second time on a box that is by then on both
sides. -/

example : Att S true ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := by
  glsmove
  all_goals leave_open

/-! ## 5. A sequent that is not derivable: `⇒ □p ⟶ p`

GL does not prove reflexivity.  Go as far as the moves go.  What should
happen: after `impR` the goal is `□p ⇒ p`, and no move applies to it.  A
query there is an error, `glsmove: no move applies at goal 0`, so the
query is not written below: type `glsmove` on a line after `glsmove impR`
to see it. -/

example : Att S true ([] ⇒ [□p ⟶ p]) := by
  glsmove impR
  all_goals leave_open

/-! ## 6. A sequent that is not derivable: the converse of K

`⇒ (□p ⟶ □q) ⟶ □(p ⟶ q)`.  What should happen: ImpL leaves two goals;
the second closes; the first, `⇒ □p, □(p ⟶ q)`, has two boxes for GLR,
and after either the goal that is left has no move. -/

example : Att S true ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) := by
  glsmove
  all_goals leave_open

/-! ## To look at a derivation that is built

Name one and walk it.  With `#walk`, a click on an offered motion writes
it.  In a block whose goal is `Walk d`, each line is a motion (`down i`,
`up`, `left`, `right`, `top`, `goal k`) and the goal shows the view there. -/

def d : Der S ([□p] ⇒ [□p]) := by
  glsmove glr p
  glsmove idP 0

#walk d
#walk d down 0

example : Walk d := by
  down 0
