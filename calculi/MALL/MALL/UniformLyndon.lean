/-
Lyndon's condition for the uniform interpolant: every literal of
`ui p Γ` is a literal of `Γ`.  Hence every literal of `∀p A` and of `∃p A`
is a literal of `A`.

The proof follows `uiN_letters` (`MALL/Uniform.lean`), with literals in
place of letters: each disjunct of the interpolant is built from
interpolants of sequents whose formulas are formulas of `Γ` or immediate
subformulas of one, by connectives that add no literal.  Theory file: it
ends with its bound on axioms.
-/
import MALL.Uniform
import MALL.Craig

namespace MALL

open List UI

namespace UI

/-! ## The literals of the simplifying connectives -/

theorem lits_sTensor {A B ℓ : Form} (h : ℓ ∈ (sTensor A B).lits) :
    ℓ ∈ A.lits ∨ ℓ ∈ B.lits := by
  unfold sTensor at h
  split at h
  · cases h
  · split at h
    · exact .inr h
    · split at h
      · exact .inl h
      · split at h
        · cases h
        · exact mem_append.1 h

theorem lits_sPar {A B ℓ : Form} (h : ℓ ∈ (sPar A B).lits) : ℓ ∈ A.lits ∨ ℓ ∈ B.lits := by
  unfold sPar at h
  rcases lits_sTensor (Form.mem_lits_neg.1 h) with h | h
  · have := Form.mem_lits_neg.1 h
    rw [Form.neg_neg] at this
    exact .inl this
  · have := Form.mem_lits_neg.1 h
    rw [Form.neg_neg] at this
    exact .inr this

theorem lits_plusList {ℓ : Form} :
    ∀ l : List Form, ℓ ∈ (plusList l).lits → ∃ D, D ∈ l ∧ ℓ ∈ D.lits
  | [], h => by cases h
  | [A], h => ⟨A, mem_cons_self .., h⟩
  | A :: B :: l, h => by
    rcases mem_append.1 (show ℓ ∈ A.lits ++ (plusList (B :: l)).lits from h) with h | h
    · exact ⟨A, mem_cons_self .., h⟩
    · obtain ⟨D, hD, hDℓ⟩ := lits_plusList (B :: l) h
      exact ⟨D, mem_cons_of_mem _ hD, hDℓ⟩

theorem lits_sBig {ds : List Form} {ℓ : Form} (h : ℓ ∈ (sBig ds).lits) :
    ∃ D, D ∈ ds ∧ ℓ ∈ D.lits := by
  unfold sBig at h
  split at h
  · cases h
  · obtain ⟨D, hD, hDℓ⟩ := lits_plusList _ h
    exact ⟨D, (mem_filter.1 (mem_dedup.1 hD)).1, hDℓ⟩

theorem lits_sWith {A B ℓ : Form} (h : ℓ ∈ (sWith A B).lits) : ℓ ∈ A.lits ∨ ℓ ∈ B.lits := by
  unfold sWith at h
  obtain ⟨D, hD, hDℓ⟩ := lits_sBig (Form.mem_lits_neg.1 h)
  rcases mem_cons.1 hD with rfl | hD
  · have := Form.mem_lits_neg.1 hDℓ
    rw [Form.neg_neg] at this
    exact .inl this
  · rcases mem_cons.1 hD with rfl | hD
    · have := Form.mem_lits_neg.1 hDℓ
      rw [Form.neg_neg] at this
      exact .inr this
    · cases hD

end UI

/-! ## The literals of the interpolant -/

/-- **Every literal of the interpolant is a literal of the sequent**, at
every bound. -/
theorem uiN_lits (p : Nat) : ∀ (n : Nat) (Γ : List Form) (ℓ : Form),
    ℓ ∈ (uiN p n Γ).lits → ∃ C, C ∈ Γ ∧ ℓ ∈ C.lits
  | 0, _, _, h => by cases h
  | n + 1, Γ, ℓ, h => by
    obtain ⟨D, hD, hℓ⟩ := lits_sBig h
    rcases mem_step hD with hD | ⟨X, r, hr, hD⟩ | ⟨q, hq, rfl⟩
    · rcases mem_uiBase hD with ⟨rfl, rfl⟩ | ⟨rfl, _⟩ | ⟨A, rfl, rfl⟩
      · cases hℓ
      · exact ⟨D, mem_cons_self .., hℓ⟩
      · cases hℓ
    · have hp : Γ ~ X :: r := picks_perm hr
      have hX : X ∈ Γ := hp.mem_iff.2 (mem_cons_self ..)
      have hr' : ∀ C, C ∈ r → C ∈ Γ := fun C hC => hp.mem_iff.2 (mem_cons_of_mem _ hC)
      -- from a premise's interpolant to the conclusion
      have lift : ∀ (Γ' : List Form), (∀ C, C ∈ Γ' → C ∈ Γ ∨ ∀ b, b ∈ C.lits → b ∈ X.lits) →
          ℓ ∈ (uiN p n Γ').lits → ∃ C, C ∈ Γ ∧ ℓ ∈ C.lits := by
        intro Γ' hsub h'
        obtain ⟨C, hC, hℓC⟩ := uiN_lits p n Γ' ℓ h'
        rcases hsub C hC with hC | hC
        · exact ⟨C, hC, hℓC⟩
        · exact ⟨X, hX, hC ℓ hℓC⟩
      cases X with
      | atom _ | natom _ | one | zero => cases hD
      | top =>
        rcases mem_cons.1 hD with rfl | hD
        · cases hℓ
        · cases hD
      | bot =>
        rcases mem_cons.1 hD with rfl | hD
        · exact lift r (fun C hC => .inl (hr' C hC)) hℓ
        · cases hD
      | par A B =>
        rcases mem_cons.1 hD with rfl | hD
        · refine lift (A :: B :: r) (fun C hC => ?_) hℓ
          rcases mem_cons.1 hC with rfl | hC
          · exact .inr fun b hb => mem_append.2 (.inl hb)
          · rcases mem_cons.1 hC with rfl | hC
            · exact .inr fun b hb => mem_append.2 (.inr hb)
            · exact .inl (hr' C hC)
        · cases hD
      | wth A B =>
        rcases mem_cons.1 hD with rfl | hD
        · rcases lits_sWith hℓ with hℓ | hℓ
          · refine lift (A :: r) (fun C hC => ?_) hℓ
            rcases mem_cons.1 hC with rfl | hC
            · exact .inr fun b hb => mem_append.2 (.inl hb)
            · exact .inl (hr' C hC)
          · refine lift (B :: r) (fun C hC => ?_) hℓ
            rcases mem_cons.1 hC with rfl | hC
            · exact .inr fun b hb => mem_append.2 (.inr hb)
            · exact .inl (hr' C hC)
        · cases hD
      | plus A B =>
        rcases mem_cons.1 hD with rfl | hD
        · refine lift (A :: r) (fun C hC => ?_) hℓ
          rcases mem_cons.1 hC with rfl | hC
          · exact .inr fun b hb => mem_append.2 (.inl hb)
          · exact .inl (hr' C hC)
        · rcases mem_cons.1 hD with rfl | hD
          · refine lift (B :: r) (fun C hC => ?_) hℓ
            rcases mem_cons.1 hC with rfl | hC
            · exact .inr fun b hb => mem_append.2 (.inr hb)
            · exact .inl (hr' C hC)
          · cases hD
      | tensor A B =>
        obtain ⟨q, hq, rfl⟩ := mem_map.1 hD
        have pq : r ~ q.1 ++ q.2 := splits_perm hq
        rcases lits_sTensor hℓ with hℓ | hℓ
        · refine lift (A :: q.1) (fun C hC => ?_) hℓ
          rcases mem_cons.1 hC with rfl | hC
          · exact .inr fun b hb => mem_append.2 (.inl hb)
          · exact .inl (hr' C (pq.mem_iff.2 (mem_append.2 (.inl hC))))
        · refine lift (B :: q.2) (fun C hC => ?_) hℓ
          rcases mem_cons.1 hC with rfl | hC
          · exact .inr fun b hb => mem_append.2 (.inr hb)
          · exact .inl (hr' C (pq.mem_iff.2 (mem_append.2 (.inr hC))))
    · obtain ⟨pq, _, _⟩ := properSplits_spec hq
      rcases lits_sPar hℓ with hℓ | hℓ
      · obtain ⟨C, hC, hℓC⟩ := uiN_lits p n q.1 ℓ hℓ
        exact ⟨C, pq.mem_iff.2 (mem_append.2 (.inl hC)), hℓC⟩
      · obtain ⟨C, hC, hℓC⟩ := uiN_lits p n q.2 ℓ hℓ
        exact ⟨C, pq.mem_iff.2 (mem_append.2 (.inr hC)), hℓC⟩

/-- **Lyndon's condition for `ui`.** -/
theorem ui_lits (p : Nat) (Γ : List Form) : ∀ ℓ ∈ (ui p Γ).lits, ℓ ∈ litsL Γ := fun ℓ h =>
  let ⟨C, hC, hℓ⟩ := uiN_lits p _ Γ ℓ h
  mem_litsL.2 ⟨C, hC, hℓ⟩

theorem forallP_lits (p : Nat) (A : Form) : ∀ ℓ ∈ (forallP p A).lits, ℓ ∈ A.lits := fun ℓ h => by
  obtain ⟨C, hC, hℓ⟩ := uiN_lits p _ [A] ℓ h
  rcases mem_cons.1 hC with rfl | hC
  · exact hℓ
  · cases hC

/-- For `∃p A`, which is the negation of the interpolant at `A⊥`: the two
negations cancel. -/
theorem existsP_lits (p : Nat) (A : Form) : ∀ ℓ ∈ (existsP p A).lits, ℓ ∈ A.lits := fun ℓ h => by
  have h' : ℓᗮ ∈ (ui p [Aᗮ]).lits := Form.mem_lits_neg.1 h
  obtain ⟨C, hC, hℓ⟩ := uiN_lits p _ [Aᗮ] ℓᗮ h'
  rcases mem_cons.1 hC with rfl | hC
  · have := Form.mem_lits_neg.1 hℓ
    rwa [Form.neg_neg] at this
  · cases hC

theorem uniformInterpolationLyndon : UniformInterpolationLyndon := fun p Γ =>
  ⟨ui p Γ, ui_lits p Γ, ui_spec p Γ⟩

theorem uniformInterpolationLyndonForFormulas : UniformInterpolationLyndonForFormulas :=
  fun p A =>
    ⟨⟨forallP p A, forallP_lits p A, forallP_spec p A⟩,
     ⟨existsP p A, existsP_lits p A, existsP_spec p A⟩⟩

end MALL

#axioms_within_file [propext, Quot.sound]
