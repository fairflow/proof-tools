/-
For the full exploration: tactics of the calculus, and what the searches
say of a sequent.

Code for the editor: nothing here is trusted, and the file has no bound
on axioms.  A tactic of the calculus (`Tac S`) is a program that gives a
script for a sequent, or nothing; whether a script it gives closes its
goal is for the checker to say.  The library proves that a tactic built
with its combinators never gives a script with a failing line.
-/
import MALL.Run
import MALL.Cut
import MALL.FiniteModel
import MALL.Tactic
import MALL.Screen

namespace MALL

open ProofTools ProofTools.Explore

/-! ## Tactics of the calculus -/

/-- A move of a rule that loses nothing, read upwards: the three axioms
and the invertible rules ⅋, ⊥, &.  (⊗ asks how to split, ⊕ which side,
cut which formula.) -/
def Move.routine : Move → Bool
  | .ax _ | .one | .top | .bot | .par _ _ | .wth _ _ => true
  | _ => false

/-- One routine step: the first of the axioms and ⅋, ⊥, & that applies. -/
def routineStep : Tac S := fun j =>
  Tac.first (((candidates j).filter Move.routine).map Tac.move) j

/-- **The routine steps, done at once**: the axioms and the invertible
rules, at every goal they leave, at most `n` deep.  What is left has only
⊗ and ⊕ to try. -/
def routine (n : Nat) : Tac S := Tac.iterate n routineStep

theorem routine_valid (n : Nat) : (routine n).Valid := Tac.valid_iterate routineStep n

/-- **The search by lazy splitting, as a tactic of the calculus**: the
script of the derivation it finds, where there is one. -/
def found : Tac S := fun j =>
  match produce j 0 with
  | .pass ls => some ls
  | _ => none

/-! ## What the searches say -/

/-- A set of phases of ℤ/n as text: `{0, 2}`. -/
def showPhases (G : List Bool) : String :=
  "{" ++ ", ".intercalate (((List.range G.length).filter fun i => G.getD i false).map toString) ++ "}"

/-- **What the searches say of a sequent**: the derivation that the lazy
search finds, drawn; or that the decision procedure finds none, with a
small phase structure that refutes it where the screen's enumeration has
one (cyclic groups of order at most 4, letters `p` and `q` only: that part
is not proved, and is there to be read). -/
def explain (Γ : List Form) : String :=
  match proveLazy Γ with
  | some c =>
    if h : Cert.check Γ c = true then
      showSeq Γ ++ "\n  is derivable:\n" ++ (Der.ofCert Γ c h).render
    else showSeq Γ ++ "\n  flag: the tree found does not check"
  | none =>
    if decide (Derivable Γ) then showSeq Γ ++ "\n  flag: the searches disagree"
    else
      showSeq Γ ++ "\n  is not derivable (decided by the proved search)" ++
      match Screen.countermodel Γ with
      | some (n, bot, val) =>
        s!"\n  refuted in ℤ/{n} with antiphases {showPhases bot}, p = {showPhases (val.getD 0 [])}, q = {showPhases (val.getD 1 [])}"
      | none => ""

end MALL
