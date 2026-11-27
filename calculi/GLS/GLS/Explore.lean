/-
For the full exploration: a countermodel drawn, and tactics of the
calculus.

Code for the editor: nothing here is trusted, and the file has no bound
on axioms.  A tactic of the calculus (`Tac S`) is a program that gives a
script for a sequent, or nothing; whether a script it gives closes its
goal is for the checker to say.  The library proves that a tactic built
with its combinators never gives a script with a failing line.
-/
import GLS.Run
import GLS.Tactic

namespace GLS

open ProofTools ProofTools.Explore

/-! ## A countermodel, drawn -/

/-- The variables true at a world, as text: `{p, q}`, or `{}`. -/
def showVal (v : List Nat) : String := "{" ++ ", ".intercalate (v.map varName) ++ "}"

mutual
  /-- The lines of a tree: at each world the variables true there, its
  children below it and one step in. -/
  def Tree.lines (indent : String) : Tree → List String
    | .node v ks => (indent ++ showVal v) :: Tree.linesL (indent ++ "  ") ks
  /-- The lines of the trees of a list. -/
  def Tree.linesL (indent : String) : List Tree → List String
    | [] => []
    | t :: ts => t.lines indent ++ Tree.linesL indent ts
end

/-- A tree drawn: a world on each line with the variables true there, the
worlds it sees directly below it and one step in.  A world sees every
world below it, at any depth. -/
def Tree.draw (t : Tree) : String := "\n".intercalate (t.lines "")

mutual
  /-- The height of the derivation that a tree of moves is: 1 for a move
  with no premise (as `Fam.height`). -/
  def certHeight : Cert S → Nat
    | .node _ cs => certHeightL cs + 1
  /-- The greatest height in a list. -/
  def certHeightL : List (Unit × Cert S) → Nat
    | [] => 0
    | (_, c) :: cs => max (certHeight c) (certHeightL cs)
end

/-- **What the search says of a sequent**: that it is derivable, with the
height of the derivation found; or the countermodel, drawn. -/
def explain (s : Seq) : String :=
  match certOrRef s with
  | .inl c => s.show ++ "\n  is derivable in GLS: the search found a derivation of height " ++
      toString (certHeight c.1)
  | .inr r => s.show ++ "\n  is not derivable in GLS: it is false at the root of\n" ++ r.1.draw

/-! ## Tactics of the calculus -/

/-- A move of a rule that loses nothing: the axioms and the two
implication rules.  (GLR asks for a choice, and drops formulas.) -/
def Move.routine : Move → Bool
  | .glr _ => false
  | _ => true

/-- One routine step: the first of IdP, BotL, ImpR, ImpL that applies. -/
def routineStep : Tac S := fun j =>
  Tac.first (((candidates j).filter Move.routine).map Tac.move) j

/-- **The routine steps, done at once**: the axioms and the implication
rules, at every goal they leave, at most `n` deep.  What is left has only
GLR to try. -/
def routine (n : Nat) : Tac S := Tac.iterate n routineStep

theorem routine_valid (n : Nat) : (routine n).Valid := Tac.valid_iterate routineStep n

/-- **The search, as a tactic of the calculus**: the script of the
derivation that the search of `GLS/Search.lean` finds, where there is
one. -/
def found : Tac S := fun j =>
  match produce j 0 with
  | .pass ls => some ls
  | _ => none

end GLS
