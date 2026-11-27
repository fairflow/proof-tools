/-
Uniform interpolation for GL, the condition on variables.

`GLS/Interpolation.lean` proves that the interpolant has no `p`
(`uiSeq_free`).  The usual statement of uniform interpolation asks more:
every variable of `∃p.A` is a variable of `A`.  (On paper the two are
equivalent, by substituting `⊥` for the other variables; substitution is
not in this development.)  This file states the condition and proves it,
by the induction of `itpIn_free` carried for any variable `q` that occurs
nowhere in the sequent.

The statements are the two types below, written before their proofs.
Theory file: it ends with its bound on axioms.
-/
import GLS.Interpolation

namespace GLS

/-! ## The statements -/

/-- **The variables of the interpolant of a sequent are variables of the
sequent**: a variable `q` that occurs in no formula of `Γ ⇒ Δ` does not
occur in `uiSeq p Γ Δ`. -/
abbrev UiSeqVars : Prop :=
  ∀ (p q : Nat) (Γ Δ : List Form),
    (∀ A ∈ Γ ++ Δ, A.occ q = false) → (uiSeq p Γ Δ).occ q = false

/-- **Uniform interpolation for GL, with the condition on variables**: for
every `p` and `A`, the formulas `∃p.A` and `∀p.A` of `UIFor p A` (without
`p`, with their four derivations), and every variable of either is a
variable of `A`. -/
abbrev UniformInterpolationVars : Type :=
  (p : Nat) → (A : Form) →
    { u : UIFor p A //
      ∀ q, (u.ex.occ q = true → A.occ q = true) ∧ (u.all.occ q = true → A.occ q = true) }

end GLS
