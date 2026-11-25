/-
# `Play/GLSTutorial.lean`: the sequent calculus GLS, a tour

A file to read in the editor, with the infoview open, a line at a time.
Unlike `Play/GLS.lean` (the exercises) it explains each step and shows the
answers.  It is in no library: build the instance first (`lake build`, in
`calculi/GLS/`).  Every line is elaborated, and what each step is said to
show is pinned in `GLS/ExploreTest.lean`.

GLS is a sequent calculus for the provability logic GL, here as its
authors formalised it in Coq (Goré, Ramanayake and Shillito, TABLEAUX
2021; `campaign/rule-table.md` has each rule beside its source).  A
sequent `Γ ⇒ Δ` is two lists of formulas, read as multisets.  Formulas:
variables, `⊥`, `A ⟶ B` (the source's `→`; a goal is shown with `→`), `□A`.

    idP n      IdP: the variable numbered n is on both sides
    botL       BotL: ⊥ is on the left
    impR A B   ImpR: from  A, Γ ⇒ B, Δ'           to  Γ ⇒ Δ    (A ⟶ B in Δ; Δ' is Δ less it)
    impL A B   ImpL: from  Γ' ⇒ A, Δ  and  B, Γ' ⇒ Δ    to  Γ ⇒ Δ    (A ⟶ B in Γ)
    glr A      GLR:  from  B₁, □B₁, …, Bₙ, □Bₙ, □A ⇒ A  to  Γ ⇒ Δ    (□A in Δ; the □Bᵢ are the boxed formulas of Γ)
-/
import GLS.Explore

open ProofTools ProofTools.Explore GLS

abbrev p : Form := .var 0
abbrev q : Form := .var 1

/-! ## 1. Building a derivation

A goal is a sequent still to be derived.  `glsmove m` makes the move `m`
at the first goal, and the premises of the rule are the new goals.  When
none is left the derivation is done.  Here, Löb's axiom. -/

def lob : Der S ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := by
  -- ImpR: the goal becomes  □(□p → p) ⇒ □p
  glsmove impR □(□p ⟶ p) □p
  -- GLR on □p.  The boxed formula on the left is unboxed and kept, and □p
  -- itself comes to the left:  □p → p, □(□p → p), □p ⇒ p
  glsmove glr p
  -- ImpL on □p → p: two goals,  □(□p → p), □p ⇒ □p, p   and   p, □(□p → p), □p ⇒ p
  glsmove impL □p p
  -- the first: GLR again, on the □p that is by now on both sides
  glsmove glr p
  -- its premise has p on both sides
  glsmove idP 0
  -- the second goal has p on both sides too
  glsmove idP 0

/-! ## 2. Asking what applies

`glsmove` alone makes no move: it lists the moves that apply at goal 0.
Click one in the infoview to write it.  `glsmove where` draws the attempt
so far, with goal 0 marked `>`. -/

example : Att S true ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  -- one move applies: ImpR on the whole formula
  glsmove
  glsmove impR □(p ⟶ q) (□p ⟶ □q)
  glsmove impR □p □q
  -- one move applies: GLR on □q
  glsmove
  glsmove glr q
  -- the attempt, drawn; one goal is open:  p, □p, p → q, □(p → q), □q ⇒ q
  glsmove where
  -- leave it open, without an error
  all_goals leave_open

/-! ## 3. Patterns

A move's arguments may be left out.  `glsmove impR` is made if one ImpR
applies.  `_` stands for any argument.  `glsmove idP` finds the variable. -/

def axK : Der S ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  glsmove impR
  glsmove impR
  glsmove glr
  glsmove impL _ q
  glsmove idP
  glsmove idP

/-! ## 4. A script

A derivation built by `glsmove` is data.  Its script is the list of its
lines: the goal each acted at, and the move.  `apply_script` runs a
script; what it leaves can be continued by hand. -/

-- 6 lines
#eval axK.script.length
-- true: the script runs to the end
#eval derives S ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) axK.script

example : Der S ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  -- the first three lines: to  p, □p, p → q, □(p → q), □q ⇒ q
  apply_script axK.script.take 3
  glsmove impL p q
  glsmove idP 0
  glsmove idP 1

/-! ## 5. Tactics of the calculus

A tactic of the calculus is a program that gives a script for a sequent.

* `routine n` does the steps that lose nothing (the axioms, ImpR, ImpL)
  wherever they apply.  What it leaves has only GLR to try.
* `found` is the search of `GLS/Search.lean`: the script of a derivation,
  where there is one.

`apply_script` takes the script as a closed term, so the sequent is
written out again for the tactic. -/

example : Der S ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by
  apply_script (routine 20 ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q])).getD []
  -- one goal is left:  □p, □(p → q) ⇒ □q
  glsmove glr q
  apply_script (routine 20 ([p, □p, p ⟶ q, □(p ⟶ q), □q] ⇒ [q])).getD []

-- The whole derivation, from the search.
def lobByTheSearch : Der S ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := by
  apply_script (found ([] ⇒ [□(□p ⟶ p) ⟶ □p])).getD []

-- 6 lines, and they are the lines of section 1: the search finds that derivation
#eval lobByTheSearch.script.length
#eval lobByTheSearch.script == lob.script

/-! ## 6. A walk

`#walk d` draws a derivation at its root and offers the motions from
there; `#walk d down 0 down 0` goes on from it.  In a block whose goal is
`Walk d`, each line is a motion (`down i`, `up`, `left`, `right`, `top`)
and the infoview shows the view there. -/

#walk lob
#walk lob down 0 down 0

example : Walk lob := by
  -- the premise of ImpR, where the rule is GLR
  down 0
  -- the premise of GLR, where the rule is ImpL: it has two premises
  down 0
  -- the second premise of ImpL:  p, □(□p → p), □p ⇒ p
  down 1
  up

/-! ## 7. A sequent with no derivation

`□p → p` is not a theorem of GL.  The moves go so far and stop. -/

example : Att S true ([] ⇒ [□p ⟶ p]) := by
  -- to  □p ⇒ p
  glsmove impR □p p
  -- no move applies here: a query would be the error
  --   glsmove: no move applies at goal 0
  -- so the goal is left open
  leave_open

-- The search says why: the sequent is false at a world that sees nothing,
-- where p is false and □p is true for want of a world to look at.
#eval IO.println (explain ([] ⇒ [□p ⟶ p]))

-- The converse of K needs three worlds: a root, a child where p is false
-- (so that □p fails at the root), and a child where p is true and q false.
#eval IO.println (explain ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]))

-- And of a sequent that has a derivation:
#eval IO.println (explain ([] ⇒ [□(□p ⟶ p) ⟶ □p]))

-- As theorems, checked by the kernel.  The first runs the search in the
-- kernel; the second checks the tree given.
instance (s : Seq) : Decidable (Valid s) := validDecidable s
example : ¬ Valid ([] ⇒ [□p ⟶ p]) := by decide +kernel
example : ¬ Derivable ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) :=
  noDerivable.verdict _ (.node [] [.node [] [], .node [0] []])

/-! ## 8. Out to the mathematics

What `glsmove` builds is a derivation of the proof system `S`.  `famOfDer`
carries it to a derivation in GLS as the source states it, the family
`Fam`; the theorems of the campaign are about that family. -/

-- A derivation in GLS, as data.
def lobFam : Fam ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := famOfDer lob

-- its height: 5
#eval lobFam.height

-- So the sequent is valid (soundness) …
example : Valid ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := soundness _ lobFam

-- … and a valid sequent has a derivation (completeness), found by the search.
example : Nonempty (Fam ([] ⇒ [□(□p ⟶ p) ⟶ □p])) := completeness _ (soundness _ lobFam)

-- Cut.  From  □p ⇒ □□p, □□□p  and  □□p, □p ⇒ □□□p  (two derivations, here
-- from the search), a derivation of  □p ⇒ □□□p.
def cutLeft : Der S ([□p] ⇒ [□□p, □□□p]) := by
  apply_script (found ([□p] ⇒ [□□p, □□□p])).getD []

def cutRight : Der S ([□□p, □p] ⇒ [□□□p]) := by
  apply_script (found ([□□p, □p] ⇒ [□□□p])).getD []

def cutResult : Fam ([□p] ⇒ [□□□p]) :=
  cutAdmissible (□□p) [] [□p] [] [□□□p] (famOfDer cutLeft) (famOfDer cutRight)

-- the heights of the two given derivations and of the one returned: 3, 4, 4
#eval ((famOfDer cutLeft).height, (famOfDer cutRight).height, cutResult.height)
