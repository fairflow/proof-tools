/-
The goals that are joined from the others: consistency, the disjunction
property, decidability without `!`, and the refutations (weakening and
contraction of the linear zone; the rules that are not invertible).

Each rests on cut elimination as a proposition (`cutEliminationProp`,
from soundness and completeness), which carries a statement about the
calculus with cut to the calculus without, where the decision procedure
of `DILL/Decide.lean` or a case analysis of `DILL/Results.lean` settles
it.  Theory file: it ends with its bound on axioms.
-/
import DILL.Completeness
import DILL.Results
import DILL.Decide

namespace DILL

open DILL.Dec

/-- **Consistency** (Pfenning 3.11): `· ; · ⟹ 0` is not derivable. -/
theorem consistency : Consistency := Res.consistency cutEliminationProp

/-- **The disjunction property** (Pfenning 3.12). -/
theorem disjunctionProperty : DisjunctionProperty := Res.disjunctionProperty cutEliminationProp

/-- **Derivability is decidable where `!` does not occur and the
unrestricted zone is empty**: the search without cut of
`DILL/Decide.lean`, and cut elimination. -/
def bangFreeDecidable : BangFreeDecidable := fun Δ C h =>
  @decidable_of_iff _ _ (Sem.derivable_iff_cf _).symm (decideCF Δ C h)

/-! ## Refuted -/

/-- **Weakening of the linear zone is refuted**: `· ; · ⟹ 1` is
derivable, `· ; a ⟹ 1` is not. -/
theorem not_weakeningL : ¬ WeakeningL := Res.not_weakeningL cutEliminationProp

/-- **Contraction of the linear zone is refuted**: `· ; a, a ⟹ a ⊗ a` is
derivable, `· ; a ⟹ a ⊗ a` is not. -/
theorem not_contractionL : ¬ ContractionL := Res.not_contractionL cutEliminationProp

private abbrev a : Form := .atom 0
private abbrev b : Form := .atom 1

/-- From a derivation with cut to one without. -/
private theorem cf_of {j : Seq} (h : Derivable j) : Nonempty (CF j) := cutEliminationProp j h

/-- From a derivation without cut to one with. -/
private theorem der_of {j : Seq} (h : Nonempty (CF j)) : Derivable j :=
  (Sem.derivable_iff_cf j).2 h

/-- **⊗R is not invertible** (CCP Lemma 6): `· ; a ⊗ b ⟹ a ⊗ b` is
derivable, and of its premises under ⊗R at the division `a ⊗ b | ·`, the
second, `· ; · ⟹ b`, is not. -/
theorem not_tensorRInv : ¬ TensorRInv := fun h =>
  have hd : Nonempty (CF ([] ⨾ [a ⊗ b] ⟹ a ⊗ b)) := by decide
  absurd (cf_of (h [] [a ⊗ b] [] a b (der_of hd)).2) (by decide)

/-- **⊸L is not invertible** (CCP Lemma 6, p. 18: "Consider
`· ; A ⊸ B ⟹ A ⊸ B`, which is initial.  However, the premisses of ⊸L for
this sequent, viz. `· ; · ⟹ A` and `· ; B ⟹ A ⊸ B`, are not derivable in
general"). -/
theorem not_lolliLInv : ¬ LolliLInv := fun h =>
  have hd : Nonempty (CF ([] ⨾ [a ⊸ b] ⟹ a ⊸ b)) := by decide
  absurd (cf_of (h [] [] [] a b (a ⊸ b) (der_of hd)).1) (by decide)

/-- **&L₁ is not invertible**: `· ; a & b ⟹ a & b` is derivable,
`· ; a ⟹ a & b` is not. -/
theorem not_withL₁Inv : ¬ WithL₁Inv := fun h =>
  have hd : Nonempty (CF ([] ⨾ [a & b] ⟹ a & b)) := by decide
  absurd (cf_of (h [] [] a b (a & b) (der_of hd))) (by decide)

/-- **&L₂ is not invertible**: `· ; a & b ⟹ a & b` is derivable,
`· ; b ⟹ a & b` is not. -/
theorem not_withL₂Inv : ¬ WithL₂Inv := fun h =>
  have hd : Nonempty (CF ([] ⨾ [a & b] ⟹ a & b)) := by decide
  absurd (cf_of (h [] [] a b (a & b) (der_of hd))) (by decide)

/-- **⊕R₁ is not invertible**: `· ; a ⊕ b ⟹ a ⊕ b` is derivable,
`· ; a ⊕ b ⟹ a` is not. -/
theorem not_plusR₁Inv : ¬ PlusR₁Inv := fun h =>
  have hd : Nonempty (CF ([] ⨾ [a ⊕ b] ⟹ a ⊕ b)) := by decide
  absurd (cf_of (h [] [a ⊕ b] a b (der_of hd))) (by decide)

/-- **⊕R₂ is not invertible**: `· ; a ⊕ b ⟹ a ⊕ b` is derivable,
`· ; a ⊕ b ⟹ b` is not. -/
theorem not_plusR₂Inv : ¬ PlusR₂Inv := fun h =>
  have hd : Nonempty (CF ([] ⨾ [a ⊕ b] ⟹ a ⊕ b)) := by decide
  absurd (cf_of (h [] [a ⊕ b] a b (der_of hd))) (by decide)

/-! ## Validity does not depend on the order of the hypotheses -/

/-- A sequent is valid exactly when the same sequent with its zones
reordered is: the formula of a sequent is written through an order of
its hypotheses, and this says that the order does not matter. -/
theorem valid_perm {Γ Γ' Δ Δ' : List Form} {C : Form} (eΓ : Γ.Perm Γ') (eΔ : Δ.Perm Δ') :
    Valid (Γ ⨾ Δ ⟹ C) ↔ Valid (Γ' ⨾ Δ' ⟹ C) := by
  rw [Sem.valid_iff_derivable, Sem.valid_iff_derivable]
  exact ⟨fun ⟨d⟩ => ⟨(d.exch eΔ).mono fun _ h => eΓ.mem_iff.1 h⟩,
    fun ⟨d⟩ => ⟨(d.exch eΔ.symm).mono fun _ h => eΓ.mem_iff.2 h⟩⟩

end DILL

#axioms_within_file [propext, Quot.sound]
