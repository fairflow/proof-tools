/-
Goal 2 and goal 3: completeness, decidability, the finite model property,
and the admissibility of cut by the semantic route, each from soundness
(`GLS/Soundness.lean`) and the search (`GLS/Search.lean`).  Theory file:
it ends with its bound on axioms.
-/
import GLS.Soundness
import GLS.Search

namespace GLS

/-- **Completeness**: what is valid is derivable in GLS. -/
theorem completeness : Completeness := fun s hv =>
  match proofOrRefutation s with
  | .inl d => ⟨d⟩
  | .inr r => absurd hv r.not_valid

/-- **Validity is decidable.** -/
@[reducible] def validDecidable : ValidDecidable := fun s =>
  match proofOrRefutation s with
  | .inl d => isTrue (soundness s d)
  | .inr r => isFalse r.not_valid

/-- **Derivability in GLS is decidable.** -/
@[reducible] def derivableDecidable : DerivableDecidable := fun s =>
  match proofOrRefutation s with
  | .inl d => isTrue ⟨d⟩
  | .inr r => isFalse (fun ⟨d⟩ => r.not_valid (soundness s d))

/-- **The finite model property**: a sequent true at every world of every
finite two-valued model of GL is valid. -/
theorem finiteModelProperty : FiniteModelProperty := fun s h =>
  match proofOrRefutation s with
  | .inl d => soundness s d
  | .inr r => by
    obtain ⟨M, hGL, h2, hfin, w, hw⟩ := r.finite
    exact absurd (h M hGL h2 hfin w) hw

/-- A sequent that GLS does not derive is false at a world of a finite
two-valued model of GL. -/
theorem finite_countermodel (s : Seq) (h : ¬ Nonempty (Fam s)) :
    ∃ M : Model, M.GL ∧ M.TwoValued ∧ M.Finite ∧ ∃ w : M.W, ¬ M.satSeq w s :=
  match proofOrRefutation s with
  | .inl d => absurd ⟨d⟩ h
  | .inr r => r.finite

/-- Cut preserves validity. -/
theorem valid_cut {A : Form} {Γ0 Γ1 Δ0 Δ1 : List Form}
    (h1 : Valid (Γ0 ++ Γ1 ⇒ Δ0 ++ A :: Δ1)) (h2 : Valid (Γ0 ++ A :: Γ1 ⇒ Δ0 ++ Δ1)) :
    Valid (Γ0 ++ Γ1 ⇒ Δ0 ++ Δ1) := by
  intro M hGL hTV w hw
  obtain ⟨B, hB, hsat⟩ := h1 M hGL hTV w hw
  rcases List.mem_append.1 hB with hB | hB
  · exact ⟨B, List.mem_append_left _ hB, hsat⟩
  · rcases List.mem_cons.1 hB with rfl | hB
    · apply h2 M hGL hTV w
      intro C hC
      rcases List.mem_append.1 hC with hC | hC
      · exact hw C (List.mem_append_left _ hC)
      · rcases List.mem_cons.1 hC with rfl | hC
        · exact hsat
        · exact hw C (List.mem_append_right _ hC)
    · exact ⟨B, List.mem_append_right _ hB, hsat⟩

/-- **Cut admissibility, by the semantic route**: both premises are valid,
so the conclusion is, so the search returns a derivation of it.  The
derivation is the search's: it is not made from the two given ones
(`GLS/Cut.lean` has the source's construction). -/
def cutAdmissible : CutAdmissible := fun _ _ _ _ _ d₁ d₂ =>
  match proofOrRefutation _ with
  | .inl d => d
  | .inr r => absurd (valid_cut (soundness _ d₁) (soundness _ d₂)) r.not_valid

end GLS

#axioms_within_file [propext, Quot.sound]
