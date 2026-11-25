/-
Tests of the search and of what follows from it: its answers on the
plan's theorems and non-theorems, and the kernel running it.
-/
import GLS.Completeness
import GLS.Tactic

namespace GLS.SearchTest

open GLS

abbrev p : Form := .var 0
abbrev q : Form := .var 1

/-- What the search answers: `true` for a derivation. -/
def proves (s : Seq) : Bool := (proofOrRef s).isLeft

/-- The tree the search returns, if it refutes the sequent. -/
def counter (s : Seq) : Option Tree :=
  match proofOrRef s with
  | .inl _ => none
  | .inr r => some r.1

#guard proves ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q])
#guard proves ([] ⇒ [□p ⟶ □□p])
#guard proves ([] ⇒ [□(□p ⟶ p) ⟶ □p])
#guard proves ([□(p ⟶ q)] ⇒ [□(p ⟶ q)])
#guard !proves ([] ⇒ [□p ⟶ p])
#guard !proves ([] ⇒ [p])
#guard !proves ([] ⇒ [□⊥ ⟶ ⊥])
#guard !proves ([] ⇒ [□(□p ⟶ p)])
#guard !proves ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)])

/-- info: some (Tree.node [] []) -/
#guard_msgs in
#eval counter ([] ⇒ [□p ⟶ p])

/-- info: some (Tree.node [] [Tree.node [] [], Tree.node [0] []]) -/
#guard_msgs in
#eval counter ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)])

-- the kernel runs the search: validity decided with no certificate
instance (s : Seq) : Decidable (Valid s) := validDecidable s

example : Valid ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := by decide +kernel
example : Valid ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) := by decide +kernel
example : ¬ Valid ([] ⇒ [□p ⟶ p]) := by decide +kernel
example : ¬ Valid ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) := by decide +kernel

-- the steps allowed for Löb's axiom, and the derivation's height
/-- info: (82, 5) -/
#guard_msgs in
#eval (fuel ([] ⇒ [□(□p ⟶ p) ⟶ □p]),
  match proofOrRef ([] ⇒ [□(□p ⟶ p) ⟶ □p]) with | .inl d => d.height | .inr _ => 0)

end GLS.SearchTest
