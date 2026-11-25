/-
Goal 1, soundness: what GLS derives is valid, in the two-valued models of
GL.  By induction on the derivation; the case of GLR is an induction
along the converse of the relation.  Theory file: it ends with its bound
on axioms.
-/
import GLS.Lemmas

namespace GLS

/-- **Soundness**: `Fam s → Valid s`. -/
theorem soundness : Soundness := by
  intro s d
  induction d with
  | idP p hΓ hΔ =>
    intro M _ _ w hw
    exact ⟨_, hΔ, hw _ hΓ⟩
  | botL h =>
    intro M _ _ w hw
    exact (hw _ h).elim
  | @impR Γ Δ A B h _ ih =>
    intro M hGL h2 w hw
    rcases h2 A w with hA | hA
    · have hprem : ∀ C ∈ A :: Γ, M.sat w C := by
        intro C hC
        rcases List.mem_cons.1 hC with rfl | hC
        · exact hA
        · exact hw _ hC
      obtain ⟨D, hD, hsat⟩ := ih M hGL h2 w hprem
      rcases List.mem_cons.1 hD with rfl | hD
      · exact ⟨A ⟶ D, h, fun _ => hsat⟩
      · exact ⟨D, List.mem_of_mem_erase hD, hsat⟩
    · exact ⟨A ⟶ B, h, fun hA' => absurd hA' hA⟩
  | @impL Γ Δ A B h _ _ ih₁ ih₂ =>
    intro M hGL h2 w hw
    have hrest : ∀ C ∈ Γ.erase (A ⟶ B), M.sat w C :=
      fun C hC => hw _ (List.mem_of_mem_erase hC)
    obtain ⟨D, hD, hsat⟩ := ih₁ M hGL h2 w hrest
    rcases List.mem_cons.1 hD with rfl | hD
    · have hB : M.sat w B := hw _ h hsat
      have hprem : ∀ C ∈ B :: Γ.erase (D ⟶ B), M.sat w C := by
        intro C hC
        rcases List.mem_cons.1 hC with rfl | hC
        · exact hB
        · exact hrest _ hC
      exact ih₂ M hGL h2 w hprem
    · exact ⟨D, hD, hsat⟩
  | @glr Γ Δ A h _ ih =>
    intro M hGL h2 w hw
    refine ⟨□A, h, ?_⟩
    intro v hwv
    induction v using hGL.cwf.induction with
    | _ v ihv =>
      have hprem : ∀ C ∈ xbox Γ ++ [□A], M.sat v C := by
        intro C hC
        rcases List.mem_append.1 hC with hC | hC
        · rcases mem_xbox.1 hC with hC | ⟨hC, B, rfl⟩
          · exact hw _ hC v hwv
          · intro u hvu
            exact hw _ hC u (hGL.trans _ _ _ hwv hvu)
        · rw [List.mem_singleton] at hC
          subst hC
          intro u hvu
          exact ihv u hvu (hGL.trans _ _ _ hwv hvu)
      obtain ⟨D, hD, hsat⟩ := ih M hGL h2 v hprem
      rw [List.mem_singleton] at hD
      subst hD
      exact hsat

end GLS

#axioms_within_file [propext, Quot.sound]
