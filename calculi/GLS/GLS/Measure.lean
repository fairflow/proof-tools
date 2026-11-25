/-
The measure that ends proof search in PSGLS, and the termination of that
search.

Source: the Coq files `GL/PSGLS_termination_measure.v` (`usable_boxes`,
l. 486; `n_imp_subformS`, l. 106; `term_meas`, l. 542; and the lemmas at
l. 626, 647, 701).  The source's measure is the pair of the number of
usable boxes and the number of implications, compared lexicographically.
Here the two are joined in one number, `weight`, relative to a list `U`
that holds every boxed subformula of the sequent: so the measure of a
premise and of a conclusion are counted over the same list.  Theory file:
it ends with its bound on axioms.
-/
import GLS.Lemmas

namespace GLS

/-! ## Boxed subformulas -/

/-- The boxed subformulas of a formula, each occurrence once. -/
def Form.boxSubs : Form → List Form
  | .var _ => []
  | ⊥ => []
  | A ⟶ B => A.boxSubs ++ B.boxSubs
  | □A => □A :: A.boxSubs

/-- The boxed subformulas of the formulas of a sequent. -/
def Seq.boxSubs (s : Seq) : List Form :=
  s.ant.flatMap Form.boxSubs ++ s.suc.flatMap Form.boxSubs

/-- **`U` holds every boxed subformula of the sequent.** -/
def Closed (U : List Form) (s : Seq) : Prop :=
  ∀ A, A ∈ s.ant ∨ A ∈ s.suc → ∀ C ∈ A.boxSubs, C ∈ U

theorem closed_self (s : Seq) : Closed s.boxSubs s := by
  intro A hA C hC
  unfold Seq.boxSubs
  rw [List.mem_append, List.mem_flatMap, List.mem_flatMap]
  rcases hA with hA | hA
  · exact .inl ⟨A, hA, hC⟩
  · exact .inr ⟨A, hA, hC⟩

theorem boxSubs_imp_left {A B C : Form} (h : C ∈ A.boxSubs) : C ∈ (A ⟶ B).boxSubs :=
  List.mem_append.2 (.inl h)

theorem boxSubs_imp_right {A B C : Form} (h : C ∈ B.boxSubs) : C ∈ (A ⟶ B).boxSubs :=
  List.mem_append.2 (.inr h)

theorem boxSubs_box {A C : Form} (h : C ∈ A.boxSubs) : C ∈ (□A).boxSubs :=
  List.mem_cons_of_mem _ h

theorem boxSubs_self (A : Form) : □A ∈ (□A).boxSubs := List.mem_cons_self ..

/-! ## The two parts of the measure -/

/-- A boxed formula. -/
def Form.isBox : Form → Bool
  | □_ => true
  | _ => false

theorem Form.isBox_iff {C : Form} : C.isBox = true ↔ ∃ B, C = □B := by
  cases C <;> simp [Form.isBox]

/-- **The usable boxes, counted**: the boxed members of `U` that are not
in the antecedent `Γ`.  (The source's `usable_boxes`: the boxed
subformulas of the sequent that are not boxed formulas of its
antecedent.) -/
def ub (U Γ : List Form) : Nat := U.countP (fun C => C.isBox && !Γ.contains C)

theorem countP_lt_of {α : Type} {p q : α → Bool} : ∀ {l : List α},
    (∀ x ∈ l, p x = true → q x = true) → (∃ x ∈ l, q x = true ∧ p x = false) →
    l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => by cases hx
  | a :: l, h, ⟨x, hx, hq, hp⟩ => by
    rw [List.countP_cons, List.countP_cons]
    have hmono : l.countP p ≤ l.countP q :=
      List.countP_mono_left (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases List.mem_cons.1 hx with rfl | hx
    · simp only [hq, hp, if_true]
      simp only [Bool.false_eq_true, if_false]
      omega
    · have ih := countP_lt_of (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨x, hx, hq, hp⟩
      have ha := h a (List.mem_cons_self ..)
      cases hpa : p a with
      | false => cases hqa : q a <;> simp <;> omega
      | true => rw [ha hpa]; simp; omega

theorem ub_le {U Γ Γ' : List Form} (h : ∀ B, □B ∈ U → □B ∈ Γ → □B ∈ Γ') :
    ub U Γ' ≤ ub U Γ := by
  unfold ub
  apply List.countP_mono_left
  intro C hC hn
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hn ⊢
  obtain ⟨B, rfl⟩ := Form.isBox_iff.1 hn.1
  exact ⟨hn.1, fun hΓ => hn.2 (h B hC hΓ)⟩

theorem ub_lt {U Γ Γ' : List Form} (h : ∀ B, □B ∈ U → □B ∈ Γ → □B ∈ Γ') {A : Form}
    (hU : □A ∈ U) (hn : □A ∉ Γ) (hin : □A ∈ Γ') : ub U Γ' < ub U Γ := by
  unfold ub
  apply countP_lt_of
  · intro C hC hn
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hn ⊢
    obtain ⟨B, rfl⟩ := Form.isBox_iff.1 hn.1
    exact ⟨hn.1, fun hΓ => hn.2 (h B hC hΓ)⟩
  · refine ⟨□A, hU, ?_, ?_⟩
    · simpa [Form.isBox] using hn
    · simpa [Form.isBox] using hin

/-- The number of implications in a formula (the source's
`n_imp_subformF`). -/
def Form.nImp : Form → Nat
  | .var _ => 0
  | ⊥ => 0
  | A ⟶ B => A.nImp + B.nImp + 1
  | □A => A.nImp

/-- The number of implications in a list of formulas. -/
def nImpL : List Form → Nat
  | [] => 0
  | A :: Γ => A.nImp + nImpL Γ

/-- The number of implications in a sequent (the source's
`n_imp_subformS`). -/
def Seq.nImp (s : Seq) : Nat := nImpL s.ant + nImpL s.suc

theorem nImpL_append (Γ Γ' : List Form) : nImpL (Γ ++ Γ') = nImpL Γ + nImpL Γ' := by
  induction Γ with
  | nil => simp [nImpL]
  | cons A Γ ih => simp only [List.cons_append, nImpL, ih]; omega

theorem nImpL_erase {A : Form} {Γ : List Form} (h : A ∈ Γ) :
    nImpL (Γ.erase A) + A.nImp = nImpL Γ := by
  induction Γ with
  | nil => cases h
  | cons C Γ ih =>
    rw [List.erase_cons]
    by_cases hc : C = A
    · subst hc; simp only [beq_self_eq_true, if_true, nImpL]; omega
    · have hb : (C == A) = false := by simpa using hc
      simp only [hb, nImpL]
      rcases List.mem_cons.1 h with h | h
      · exact absurd h.symm hc
      · have := ih h; simp only [Bool.false_eq_true, if_false, nImpL]; omega

theorem nImpL_xbox_le (Γ : List Form) : nImpL (xbox Γ) ≤ 2 * nImpL Γ := by
  induction Γ with
  | nil => simp [xbox, nImpL]
  | cons A Γ ih =>
    have hcons : xbox (A :: Γ) = A.xb ++ xbox Γ := by simp [xbox]
    rw [hcons, nImpL_append]
    have hA : nImpL A.xb ≤ 2 * A.nImp := by
      cases A <;> simp [Form.xb, nImpL, Form.nImp] <;> omega
    simp only [nImpL]
    omega

/-! ## The measure -/

/-- **The measure of a sequent**, relative to `U`: it falls from the
conclusion of a rule of PSGLS to each premise. -/
def weight (U : List Form) (s : Seq) : Nat := (s.nImp + 1) * 3 ^ ub U s.ant

theorem weight_lt_imp {i i' b b' : Nat} (hi : i' < i) (hb : b' ≤ b) :
    (i' + 1) * 3 ^ b' < (i + 1) * 3 ^ b := by
  have h3 : 0 < 3 ^ b := Nat.pow_pos (by decide)
  have h1 : (i' + 1) * 3 ^ b' ≤ i * 3 ^ b :=
    Nat.mul_le_mul hi (Nat.pow_le_pow_right (by decide) hb)
  have h2 : i * 3 ^ b < (i + 1) * 3 ^ b := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  omega

theorem weight_lt_box {i i' b b' : Nat} (hi : i' ≤ 2 * i) (hb : b' < b) :
    (i' + 1) * 3 ^ b' < (i + 1) * 3 ^ b := by
  have h3 : 0 < 3 ^ b' := Nat.pow_pos (by decide)
  have hpow : 3 ^ b' * 3 ≤ 3 ^ b := by
    rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) hb
  have h1 : (i' + 1) * 3 ^ b' ≤ (2 * i + 1) * 3 ^ b' := Nat.mul_le_mul (by omega) (Nat.le_refl _)
  have h2 : (i + 1) * (3 ^ b' * 3) ≤ (i + 1) * 3 ^ b := Nat.mul_le_mul (Nat.le_refl _) hpow
  have h4 : (i + 1) * (3 ^ b' * 3) = (2 * i + 1) * 3 ^ b' + (i + 2) * 3 ^ b' := by
    rw [← Nat.add_mul, Nat.mul_comm (3 ^ b') 3, ← Nat.mul_assoc]
    congr 1; omega
  have h5 : 0 < (i + 2) * 3 ^ b' := Nat.mul_pos (by omega) h3
  omega

/-- **The step**: a premise of a rule of PSGLS keeps `U` closed and has a
smaller measure.  (The source's `GLR_applic_less_usable_boxes`,
`ImpR_applic_less_Imp_same_usable_boxes` and
`ImpL_applic_less_Imp_same_usable_boxes`.) -/
theorem PSPrem.step {U : List Form} {p c : Seq} (h : PSPrem p c) (hU : Closed U c) :
    Closed U p ∧ weight U p < weight U c := by
  obtain ⟨Γ, Δ⟩ := c
  cases h with
  | impR A B h e =>
    subst e
    refine ⟨?_, ?_⟩
    · intro C hC D hD
      rcases hC with hC | hC
      · rcases List.mem_cons.1 hC with rfl | hC
        · exact hU _ (.inr h) D (boxSubs_imp_left hD)
        · exact hU _ (.inl hC) D hD
      · rcases List.mem_cons.1 hC with rfl | hC
        · exact hU _ (.inr h) D (boxSubs_imp_right hD)
        · exact hU _ (.inr (List.mem_of_mem_erase hC)) D hD
    · have he := nImpL_erase h
      apply weight_lt_imp
      · simp only [Seq.nImp, nImpL, Form.nImp] at he ⊢; omega
      · exact ub_le (fun C _ hC => List.mem_cons_of_mem _ hC)
  | impL₁ A B h e =>
    subst e
    refine ⟨?_, ?_⟩
    · intro C hC D hD
      rcases hC with hC | hC
      · exact hU _ (.inl (List.mem_of_mem_erase hC)) D hD
      · rcases List.mem_cons.1 hC with rfl | hC
        · exact hU _ (.inl h) D (boxSubs_imp_left hD)
        · exact hU _ (.inr hC) D hD
    · have he := nImpL_erase h
      apply weight_lt_imp
      · simp only [Seq.nImp, nImpL, Form.nImp] at he ⊢; omega
      · exact ub_le (fun C _ hC => mem_erase_of_ne (by intro h; cases h) hC)
  | impL₂ A B h e =>
    subst e
    refine ⟨?_, ?_⟩
    · intro C hC D hD
      rcases hC with hC | hC
      · rcases List.mem_cons.1 hC with rfl | hC
        · exact hU _ (.inl h) D (boxSubs_imp_right hD)
        · exact hU _ (.inl (List.mem_of_mem_erase hC)) D hD
      · exact hU _ (.inr hC) D hD
    · have he := nImpL_erase h
      apply weight_lt_imp
      · simp only [Seq.nImp, nImpL, Form.nImp] at he ⊢; omega
      · exact ub_le (fun C _ hC => List.mem_cons_of_mem _ (mem_erase_of_ne (by intro h; cases h) hC))
  | glr A nP nB nBot h e =>
    subst e
    refine ⟨?_, ?_⟩
    · intro C hC D hD
      rcases hC with hC | hC
      · rcases List.mem_append.1 hC with hC | hC
        · rcases mem_xbox.1 hC with hC | ⟨hC, _⟩
          · exact hU _ (.inl hC) D (boxSubs_box hD)
          · exact hU _ (.inl hC) D hD
        · rw [List.mem_singleton] at hC; subst hC
          exact hU _ (.inr h) D hD
      · rw [List.mem_singleton] at hC; subst hC
        exact hU _ (.inr h) D (boxSubs_box hD)
    · apply weight_lt_box
      · have h1 := nImpL_xbox_le Γ
        have h2 : A.nImp ≤ nImpL Δ := by
          have := nImpL_erase h; simp only [Form.nImp] at this; omega
        simp only [Seq.nImp, nImpL_append, nImpL, Form.nImp]
        omega
      · refine ub_lt (fun B _ hB => List.mem_append_left _ (box_mem_xbox hB))
          (hU _ (.inr h) _ (boxSubs_self A)) (fun hΓ => nB ⟨A, hΓ, h⟩)
          (List.mem_append_right _ (List.mem_singleton.2 rfl))

/-- Every sequent over which `U` is closed is accessible for the premise
relation of PSGLS. -/
theorem acc_of_closed (U : List Form) : ∀ (n : Nat) (s : Seq), Closed U s → weight U s < n →
    Acc PSPrem s := by
  intro n
  induction n with
  | zero => intro s _ h; cases h
  | succ n ih =>
    intro s hU hw
    refine ⟨s, fun p hp => ?_⟩
    obtain ⟨hU', hlt⟩ := hp.step hU
    exact ih p hU' (by omega)

/-- **The termination of proof search in PSGLS** (the source's
`PSGLS_termin`, in the form of a well-founded relation): there is no
infinite sequence of sequents, each a premise of a rule of PSGLS with the
one before as conclusion. -/
theorem psTermination : PSTermination :=
  ⟨fun s => acc_of_closed s.boxSubs _ s (closed_self s) (Nat.lt_succ_self _)⟩

end GLS

#axioms_within_file [propext, Quot.sound]
