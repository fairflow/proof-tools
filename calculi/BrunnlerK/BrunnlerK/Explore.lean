/-
For the full exploration: a sequent drawn as its tree, and tactics of the
calculus.

Code for the editor: nothing here is trusted, and the file has no bound
on axioms.  A tactic of the calculus (`Tac S`) is a program that gives a
script for a sequent, or nothing; whether a script it gives closes its
goal is for the checker to say.  The library proves that a tactic built
with its combinators never gives a script with a failing line.
-/
import BrunnlerK.Run
import BrunnlerK.Tactic

namespace BrunnlerK

open ProofTools ProofTools.Explore

/-! ## A sequent as its tree (the source's "corresponding tree", p. 7) -/

/-- The lines of the tree of a sequent: at each node its formulas (`∅`
where there are none), then its boxes as children, each one step in. -/
def NSeq.treeLines (indent : String) : NSeq → List String
  | .leaf fs =>
    [indent ++ (if fs.isEmpty then "∅" else ", ".intercalate (fs.map Form.show))]
  | .cons Δ r =>
    match treeLines indent r with
    | [] => []
    | l :: ls => l :: (treeLines (indent ++ "  ") Δ ++ ls)

/-- A sequent drawn as its tree: a node on each line, the nodes of its
boxes below it and one step in, in the order of the boxes. -/
def NSeq.tree (Γ : NSeq) : String := "\n".intercalate (Γ.treeLines "")

/-! ## Tactics of the calculus -/

/-- A move of a rule that has one way to go on: the axiom, `∨`, `∧`, `□`.
(`◇k_c` asks for a choice: which diamond, into which box.) -/
def Move.routine : Move → Bool
  | .ax .. => true
  | .or .. => true
  | .and .. => true
  | .box .. => true
  | .dia .. => false

/-- One routine step: the first of the axiom, `∨`, `∧`, `□` that applies
anywhere in the sequent. -/
def routineStep : Tac S := fun Γ =>
  Tac.first (((candidates Γ).filter Move.routine).map Tac.move) Γ

/-- **The routine steps, done at once**: the axiom, `∨`, `∧` and `□`,
wherever they apply, at every goal they leave, at most `n` deep.  What is
left has only `◇k_c` to try. -/
def routine (n : Nat) : Tac S := Tac.iterate n routineStep

theorem routine_valid (n : Nat) : (routine n).Valid := Tac.valid_iterate routineStep n

/-- One move: the first candidate that applies and adds something. -/
def firstMove : Tac S := fun Γ =>
  Tac.first ((candidates Γ).filter (fun m =>
    match S.step m Γ with
    | .ok ps => !ps.any (within · Γ)
    | .error _ => false) |>.map Tac.move) Γ

/-- **A blind search**: `firstMove` at every goal it leaves, at most `n`
deep.  It never goes back on a choice, so it can fail where there is a
proof. -/
def auto (n : Nat) : Tac S := Tac.iterate n firstMove

theorem auto_valid (n : Nat) : (auto n).Valid := Tac.valid_iterate firstMove n

/-- **The search, as a tactic of the calculus**: the script of the proof
that the search of `BrunnlerK/Search.lean` finds, where there is one. -/
def found : Tac S := fun Γ =>
  match produce Γ 0 with
  | .pass ls => some ls
  | _ => none

end BrunnlerK
