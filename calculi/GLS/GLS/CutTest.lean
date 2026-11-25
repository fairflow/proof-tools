/-
Tests of goals 4 to 6: the structural functions and the cut by the
source's induction, run on small derivations; their axioms.
-/
import GLS.CutRule
import GLS.PS
import GLS.Completeness
import GLS.Tactic

namespace GLS.CutTest

open ProofTools ProofTools.Explore GLS

abbrev p : Form := .var 0
abbrev q : Form := .var 1

/-- A derivation from the search, or none. -/
def byTheSearch (s : Seq) : Option (Fam s) :=
  match proofOrRef s with
  | .inl d => some d
  | .inr _ => none

/-- The cut of the tutorial, `□p ⇒ □□p, □□□p` and `□□p, □p ⇒ □□□p` to
`□p ⇒ □□□p`, by the source's construction and by the semantic route: the
heights of the two given derivations and of the two results. -/
def cutHeights : Option (Nat × Nat × Nat × Nat) :=
  match byTheSearch ([□p] ⇒ [□□p, □□□p]), byTheSearch ([□□p, □p] ⇒ [□□□p]) with
  | some d₁, some d₂ =>
    some (d₁.height, d₂.height,
      (cutBySource (□□p) [] [□p] [] [□□□p] d₁ d₂).height,
      (cutAdmissible (□□p) [] [□p] [] [□□□p] d₁ d₂).height)
  | _, _ => none

#guard cutHeights == some (3, 4, 4, 4)

/-- A cut on an implication, and one on a variable. -/
def cutImp : Option Nat :=
  match byTheSearch ([p] ⇒ [q ⟶ p, □q, p]), byTheSearch ([p, q ⟶ p] ⇒ [□q, p]) with
  | some d₁, some d₂ => some (cutBySource (q ⟶ p) [p] [] [] [□q, p] d₁ d₂).height
  | _, _ => none

#guard cutImp == some 1

/-- Löb's axiom cut against its own use: from `⇒ L` and `L ⇒ □(□p → p) → □p`
with `L` Löb's axiom. -/
def cutLob : Option (Nat × Nat) :=
  let L : Form := □(□p ⟶ p) ⟶ □p
  match byTheSearch ([] ⇒ [L, L]), byTheSearch ([L] ⇒ [L]) with
  | some d₁, some d₂ =>
    some ((cutBySource L [] [] [] [L] d₁ d₂).height, (cutAdmissible L [] [] [] [L] d₁ d₂).height)
  | _, _ => none

#guard cutLob == some (5, 5)

/-- Weakening, contraction and an inversion on the derivation of Löb's
axiom: each result no higher (the heights, then the height given). -/
def structural : Option (List Nat) :=
  match byTheSearch ([] ⇒ [□(□p ⟶ p) ⟶ □p]), byTheSearch ([q, q] ⇒ [□(□p ⟶ p) ⟶ □p]) with
  | some d, some e =>
    some [(weakeningL q (Γ0 := []) (Γ1 := []) d).1.height,
      (weakeningR q (Δ0 := []) (Δ1 := [□(□p ⟶ p) ⟶ □p]) d).1.height,
      (inversionImpR (□(□p ⟶ p)) (□p) d (by decide)).1.height,
      (contractionL q (Γ0 := []) (Γ1 := []) (Γ2 := []) e).1.height,
      d.height, e.height]
  | _, _ => none

#guard structural == some [5, 5, 4, 5, 5, 5]

/-- The two systems: a derivation of GLS carried to PSGLS and back has the
same height here. -/
def psRound : Option (Nat × Nat) :=
  match byTheSearch ([□p] ⇒ [□p, □□p]) with
  | some d => some (d.height, ((psEquivalent _).2 ((psEquivalent _).1 d)).height)
  | none => none

#guard psRound == some (2, 2)

/-- info: 'GLS.cutBySource' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cutBySource

-- the kernel evaluates the cut: principal on both sides
example : (match byTheSearch ([□p] ⇒ [□p, □□p]), byTheSearch ([□p, □p] ⇒ [□□p]) with
    | some d₁, some d₂ => (cutBySource (□p) [] [□p] [] [□□p] d₁ d₂).height
    | _, _ => 0) = 3 := by decide +kernel

/-! ## Cut elimination (the thesis, Theorem 12.7.2) -/

/-- A derivation in GLS + (cut) with two cuts, one above the other:
`□p ⇒ □□□p` by a cut on `□□p`, whose left premise `□p ⇒ □□p, □□□p` is
itself got by a cut on `□p`. -/
def withCuts : Option (FamCut ([□p] ⇒ [□□□p])) :=
  match byTheSearch ([□p] ⇒ [□p, □□p, □□□p]), byTheSearch ([□p, □p] ⇒ [□□p, □□□p]),
      byTheSearch ([□□p, □p] ⇒ [□□□p]) with
  | some a, some b, some c => some (.cut (□□p) (.cut (□p) a.toCut b.toCut) c.toCut)
  | _, _, _ => none

-- the heights of the derivations in GLS that the two eliminations return
#guard (withCuts.map fun d => ((cutElimination _ d).height, (cutEliminationBySearch _ d).height))
  == some (4, 4)

/-- info: 'GLS.cutElimination' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cutElimination

end GLS.CutTest
