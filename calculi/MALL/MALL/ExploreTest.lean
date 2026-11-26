/-
Tests of the Explore stage: what each step of the tutorial
(`Play/MALLTutorial.lean`) is said to show, pinned.  Each message was
pasted from Lean's output after reading it.

Code, not theory.
-/
import MALL.Explore

namespace MALL.ExploreTest

open ProofTools ProofTools.Explore MALL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

/-! ## 1. Building -/

def distrib : Der S [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
  mallmove par pᗮ (qᗮ & rᗮ)
  mallmove wth qᗮ rᗮ
  mallmove plus₁ (p ⊗ q) (p ⊗ r)
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q
  mallmove plus₂ (p ⊗ q) (p ⊗ r)
  mallmove tensor p r [pᗮ]
  mallmove ax p
  mallmove ax r

/-! ## 2. Asking what applies -/

/--
info: mallmove: at goal 0, 3 moves apply; no move is made. Try these:
  [apply] mallmove par pᗮ qᗮ
  [apply] mallmove tensor q p []
  [apply] mallmove tensor q p [pᗮ ⅋ qᗮ]
---
info: mallmove: at goal 0, 4 moves apply; no move is made. Try these:
  [apply] mallmove tensor q p []
  [apply] mallmove tensor q p [qᗮ]
  [apply] mallmove tensor q p [pᗮ]
  [apply] mallmove tensor q p [pᗮ, qᗮ]
---
info:   ⊢ p⊥ ⅋ q⊥, q ⊗ p   by ⅋ p⊥ ⅋ q⊥
    ⊢ p⊥, q⊥, q ⊗ p   by ⊗ q ⊗ p [q⊥]
>     ? ⊢ q, q⊥
      ? ⊢ p, p⊥
  at 0.0: open goal 0; 2 open in all
-/
#guard_msgs in
example : Att S true [(p ⊗ q)ᗮ, q ⊗ p] := by
  mallmove
  mallmove par pᗮ qᗮ
  mallmove
  mallmove tensor q p [qᗮ]
  mallmove where
  all_goals leave_open

/-! ## 3. Patterns -/

/--
info: Try this:
  [apply] mallmove par pᗮ qᗮ
---
info: Try this:
  [apply] mallmove tensor q p [qᗮ]
---
info: Try this:
  [apply] mallmove ax q
---
info: Try this:
  [apply] mallmove ax p
-/
#guard_msgs in
def tensorComm : Der S [(p ⊗ q)ᗮ, q ⊗ p] := by
  mallmove par
  mallmove tensor _ _ [qᗮ]
  mallmove ax
  mallmove ax

/-! ## 4. A script -/

#guard distrib.script.length == 10
#guard derives S [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] distrib.script

example : Der S [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
  apply_script distrib.script.take 2
  mallmove plus₁ (p ⊗ q) (p ⊗ r)
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q
  mallmove plus₂ (p ⊗ q) (p ⊗ r)
  mallmove tensor p r [pᗮ]
  mallmove ax p
  mallmove ax r

/-! ## 5. Tactics of the calculus -/

-- the routine steps leave the two premises of &
/--
info:   ⊢ p⊥ ⅋ (q⊥ & r⊥), (p ⊗ q) ⊕ (p ⊗ r)   by ⅋ p⊥ ⅋ (q⊥ & r⊥)
    ⊢ p⊥, q⊥ & r⊥, (p ⊗ q) ⊕ (p ⊗ r)   by & q⊥ & r⊥
>     ? ⊢ q⊥, p⊥, (p ⊗ q) ⊕ (p ⊗ r)
      ? ⊢ r⊥, p⊥, (p ⊗ q) ⊕ (p ⊗ r)
  at 0.0: open goal 0; 2 open in all
-/
#guard_msgs in
example : Att S true [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
  apply_script (routine 20 [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)]).getD []
  mallmove where
  all_goals leave_open

def distribByTheSearch : Der S [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := by
  apply_script (found [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)]).getD []

#guard distribByTheSearch.script.length == 10
-- the search finds the derivation of section 1
#guard distribByTheSearch.script == distrib.script

-- the routine steps alone close a sequent that needs no choice
#guard derives S [pᗮ ⅋ (p & p)] ((routine 20 [pᗮ ⅋ (p & p)]).getD [])
-- and do not close one that needs a split
#guard !derives S [(p ⊗ q)ᗮ, q ⊗ p] ((routine 20 [(p ⊗ q)ᗮ, q ⊗ p]).getD [])

/-! ## 6. A walk -/

set_option walk.offer false in
/--
info:   ⊢ p⊥ ⅋ (q⊥ & r⊥), (p ⊗ q) ⊕ (p ⊗ r)   by ⅋ p⊥ ⅋ (q⊥ & r⊥)
    ⊢ p⊥, q⊥ & r⊥, (p ⊗ q) ⊕ (p ⊗ r)   by & q⊥ & r⊥
>     ⊢ r⊥, p⊥, (p ⊗ q) ⊕ (p ⊗ r)   by 2⊕ (p ⊗ q) ⊕ (p ⊗ r)
        0: ⊢ p ⊗ r, r⊥, p⊥   by ⊗ p ⊗ r [p⊥]   [closed]
  at 0.1: 1 premise; no open goals
-/
#guard_msgs in
#walk distrib down 0 down 1

example : Walk distrib := by
  down 0
  down 1
  down 0
  up

/-! ## 7. Sequents with no derivation -/

/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [𝟏, 𝟏] := by
  mallmove

/-- error: the move does not apply to goal 0: 1: the sequent is not ⊢ 1 -/
#guard_msgs in
example : Att S true [𝟏, 𝟏] := by
  mallmove one

/-- error: mallmove: no move applies at goal 0 -/
#guard_msgs in
example : Att S true [pᗮ ⅋ (p ⊗ p)] := by
  mallmove par pᗮ (p ⊗ p)
  mallmove tensor p p [pᗮ]
  mallmove ax p
  mallmove

/--
info: ⊢ 1, 1
  is not derivable (decided by the proved search)
  refuted in ℤ/2 with antiphases {1}, p = {0, 1}, q = {0, 1}
-/
#guard_msgs in
#eval IO.println (explain [𝟏, 𝟏])

/--
info: ⊢ p⊥ ⅋ (p ⊗ p)
  is not derivable (decided by the proved search)
  refuted in ℤ/2 with antiphases {1}, p = {1}, q = {0, 1}
-/
#guard_msgs in
#eval IO.println (explain [pᗮ ⅋ (p ⊗ p)])

/--
info: ⊢ p ⊕ p⊥
  is not derivable (decided by the proved search)
  refuted in ℤ/2 with antiphases {0}, p = {1}, q = {0, 1}
-/
#guard_msgs in
#eval IO.println (explain [p ⊕ pᗮ])

/--
info: ⊢ p⊥ ⅋ (p & p)
  is derivable:
⊢ p⊥ ⅋ (p & p)   by ⅋ p⊥ ⅋ (p & p)
  ⊢ p⊥, p & p   by & p & p
    ⊢ p, p⊥   by ax p
    ⊢ p, p⊥   by ax p
-/
#guard_msgs in
#eval IO.println (explain [pᗮ ⅋ (p & p)])

example : ¬ Derivable [𝟏, 𝟏] := by decide +kernel
example : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] := by decide +kernel
example : Derivable [pᗮ ⅋ (p & p)] := by decide +kernel
example : ¬ Valid [𝟏, 𝟏] := by decide +kernel

/-! ## 8. Out to the mathematics -/

def distribFam : Fam [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := famOfDer distrib

example : distribFam.height = 5 := by decide

example : Valid [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] := soundness _ ⟨distribFam⟩

example : Nonempty (CF [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)]) :=
  completeness _ (soundness _ ⟨distribFam⟩)

def withCut : Der S [pᗮ, qᗮ, q ⊗ p] := by
  mallmove cut (p ⊗ q) [pᗮ, qᗮ]
  mallmove tensor p q [pᗮ]
  mallmove ax p
  mallmove ax q
  apply_script tensorComm.script

def withoutCut : CF [pᗮ, qᗮ, q ⊗ p] := cutElimination _ (famOfDer withCut)

example : (famOfDer withCut).height = 4 := by decide
example : withoutCut.height = 2 := by decide

example : Derivable [𝟏 ⊕ p] → Derivable [𝟏] ∨ Derivable [p] := disjunctionProperty 𝟏 p

example : ∃ M : PhaseStructure, M.Finite ∧ ¬ M.Sat [𝟏, 𝟏] :=
  finite_countermodel _ (by decide +kernel)

end MALL.ExploreTest
