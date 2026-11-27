/-
A proved search that writes no sequent of GLS out: for every sequent, a
tree of moves that the replay accepts at it, or a finite tree at whose
root it is false.

The search of `GLS/Search.lean` returns a derivation of GLS as a term,
which holds every sequent of the derivation; the premise of GLR has
`B, □B` for each `□B` of the antecedent, with repetitions, so those
sequents have `2ⁿ` formulas after `n` nested GLR and the search builds
them (`campaign/measurements.md`, Table 1).

Here the search is made at sequents **without repeated formulas**: each
premise has its repeated formulas removed before the search goes on.
What it returns for a derivable sequent is a tree of moves, and with it
the proof that the tree replays at every sequent that has the formulas of
the one searched (`Yes`): a move that applies to a sequent applies to any
sequent with those formulas, and a premise there has the formulas of the
premise here, since a formula of a sequent without repetitions is gone
once it is erased.  So the tree found for a sequent less its repetitions
is a derivation of the sequent itself.  A tree of worlds refutes a
sequent if it refutes the sequent less its repetitions: truth of a
sequent looks at which formulas are there, not at how often.

    certOrRef : (s : Seq) → { c : Cert S // Cert.check s c = true } ⊕ Ref s      (S28)

The measure of `GLS/Measure.lean` serves: removing repeated formulas
changes neither the boxed formulas of an antecedent nor, upwards, the
number of implications.

Theory file: it ends with its bound on axioms.
-/
import GLS.Search
import GLS.Proof

namespace GLS

open ProofTools ProofTools.Explore

/-! ## Removing repeated formulas -/

/-- `A` put before a list, unless it is there already. -/
def insertNew (A : Form) (Γ : List Form) : List Form := if A ∈ Γ then Γ else A :: Γ

/-- A list less its repeated formulas: of several occurrences the last is
kept.  (Written through `insertNew` so that the recursive call is made
once: with the `if` written out in place, the compiled function made it
twice, and its time doubled with each formula of the list.  Found by the
measurements, `campaign/measurements.md`.) -/
def dedup : List Form → List Form
  | [] => []
  | A :: Γ => insertNew A (dedup Γ)

/-- The occurrences that `dedup` removes. -/
def dropped : List Form → List Form
  | [] => []
  | A :: Γ => if A ∈ dedup Γ then A :: dropped Γ else dropped Γ

theorem mem_dedup {A : Form} {Γ : List Form} : A ∈ dedup Γ ↔ A ∈ Γ := by
  induction Γ with
  | nil => simp [dedup]
  | cons C Γ ih =>
    by_cases hC : C ∈ dedup Γ
    · simp only [dedup, insertNew, hC, if_true, List.mem_cons, ih]
      constructor
      · exact .inr
      · rintro (rfl | h)
        · exact ih.1 hC
        · exact h
    · simp only [dedup, insertNew, hC, if_false, List.mem_cons, ih]

theorem dedup_perm (Γ : List Form) : Γ.Perm (dedup Γ ++ dropped Γ) := by
  induction Γ with
  | nil => exact List.Perm.refl _
  | cons C Γ ih =>
    by_cases hC : C ∈ dedup Γ
    · simp only [dedup, insertNew, dropped, hC, if_true]
      exact (ih.cons C).trans List.perm_middle.symm
    · simp only [dedup, insertNew, dropped, hC, if_false, List.cons_append]
      exact ih.cons C

/-- A sequent less its repeated formulas, on each side. -/
def Seq.dedup (s : Seq) : Seq := GLS.dedup s.ant ⇒ GLS.dedup s.suc

/-- **No formula of the list is repeated**: a formula is not in the list
less one occurrence of it. -/
def Once (Γ : List Form) : Prop := ∀ X, X ∉ Γ.erase X

theorem once_dedup (Γ : List Form) : Once (dedup Γ) := by
  induction Γ with
  | nil => intro X h; cases h
  | cons C Γ ih =>
    by_cases hC : C ∈ dedup Γ
    · simpa only [dedup, insertNew, hC, if_true] using ih
    · simp only [dedup, insertNew, hC, if_false]
      intro X hX
      rw [List.erase_cons] at hX
      by_cases hCX : C = X
      · subst hCX
        simp only [beq_self_eq_true, if_true] at hX
        exact hC hX
      · have : (C == X) = false := by simpa using hCX
        simp only [this] at hX
        rcases List.mem_cons.1 hX with h | h
        · exact hCX h.symm
        · exact ih X h

/-- No formula is repeated on either side. -/
def Seq.Once (q : Seq) : Prop := GLS.Once q.ant ∧ GLS.Once q.suc

theorem Seq.once_dedup (s : Seq) : s.dedup.Once := ⟨GLS.once_dedup _, GLS.once_dedup _⟩

/-- **`q'` has the formulas of `q`**, on each side. -/
def Seq.Sub (q q' : Seq) : Prop := (∀ A ∈ q.ant, A ∈ q'.ant) ∧ (∀ A ∈ q.suc, A ∈ q'.suc)

theorem Seq.dedup_sub (s : Seq) : s.dedup.Sub s :=
  ⟨fun _ h => mem_dedup.1 h, fun _ h => mem_dedup.1 h⟩

/-- Where no formula is repeated, what is left after one is erased is in
the larger list after it is erased there. -/
theorem erase_sub {Γ Γ' : List Form} (ho : Once Γ) (h : ∀ A ∈ Γ, A ∈ Γ') (X : Form) :
    ∀ C ∈ Γ.erase X, C ∈ Γ'.erase X := by
  intro C hC
  have hne : C ≠ X := fun e => ho X (e ▸ hC)
  exact mem_erase_of_ne hne (h C (List.mem_of_mem_erase hC))

theorem xbox_sub {Γ Γ' : List Form} (h : ∀ A ∈ Γ, A ∈ Γ') : ∀ C ∈ xbox Γ, C ∈ xbox Γ' := by
  intro C hC
  rcases mem_xbox.1 hC with h1 | ⟨h1, h2⟩
  · exact mem_xbox.2 (.inl (h _ h1))
  · exact mem_xbox.2 (.inr ⟨h _ h1, h2⟩)

/-! ## A tree of moves that replays at every sequent with these formulas -/

/-- **A tree of moves for `q` and for every sequent that has the formulas
of `q`.** -/
abbrev Yes (q : Seq) : Type := { c : Cert S // ∀ q', q.Sub q' → Cert.check q' c = true }

/-- IdP. -/
def Yes.idP {q : Seq} (p : Nat) (hΓ : Form.var p ∈ q.ant) (hΔ : Form.var p ∈ q.suc) : Yes q :=
  ⟨.mk (.idP p) [], fun q' hs => by
    have h : S.step (.idP p) q' = .ok [] :=
      step_of (by simp [Move.rule, hs.1 _ hΓ, hs.2 _ hΔ])
    rw [Cert.mk, Cert.check_node h]
    rfl⟩

/-- BotL. -/
def Yes.botL {q : Seq} (hΓ : ⊥ ∈ q.ant) : Yes q :=
  ⟨.mk .botL [], fun q' hs => by
    have h : S.step .botL q' = .ok [] := step_of (by simp [Move.rule, hs.1 _ hΓ])
    rw [Cert.mk, Cert.check_node h]
    rfl⟩

/-- ImpR, from a tree for the premise less its repeated formulas. -/
def Yes.impR {q : Seq} (ho : q.Once) (A B : Form) (h : A ⟶ B ∈ q.suc)
    (c : Yes (A :: q.ant ⇒ B :: q.suc.erase (A ⟶ B)).dedup) : Yes q :=
  ⟨.mk (.impR A B) [c.1], fun q' hs => by
    have hstep : S.step (.impR A B) q' = .ok [A :: q'.ant ⇒ B :: q'.suc.erase (A ⟶ B)] :=
      step_of (by simp [Move.rule, hs.2 _ h])
    have hc := c.2 (A :: q'.ant ⇒ B :: q'.suc.erase (A ⟶ B))
      ⟨fun C hC => by
          rcases List.mem_cons.1 (mem_dedup.1 hC) with e | hC
          · exact List.mem_cons.2 (.inl e)
          · exact List.mem_cons_of_mem _ (hs.1 _ hC),
        fun C hC => by
          rcases List.mem_cons.1 (mem_dedup.1 hC) with e | hC
          · exact List.mem_cons.2 (.inl e)
          · exact List.mem_cons_of_mem _ (erase_sub ho.2 hs.2 _ C hC)⟩
    rw [Cert.mk, Cert.check_node hstep]
    simp [Cert.checkL, hc]⟩

/-- ImpL, from trees for the two premises, each less its repeated
formulas. -/
def Yes.impL {q : Seq} (ho : q.Once) (A B : Form) (h : A ⟶ B ∈ q.ant)
    (c₁ : Yes (q.ant.erase (A ⟶ B) ⇒ A :: q.suc).dedup)
    (c₂ : Yes (B :: q.ant.erase (A ⟶ B) ⇒ q.suc).dedup) : Yes q :=
  ⟨.mk (.impL A B) [c₁.1, c₂.1], fun q' hs => by
    have hstep : S.step (.impL A B) q' =
        .ok [q'.ant.erase (A ⟶ B) ⇒ A :: q'.suc, B :: q'.ant.erase (A ⟶ B) ⇒ q'.suc] :=
      step_of (by simp [Move.rule, hs.1 _ h])
    have h₁ := c₁.2 (q'.ant.erase (A ⟶ B) ⇒ A :: q'.suc)
      ⟨fun C hC => erase_sub ho.1 hs.1 _ C (mem_dedup.1 hC),
        fun C hC => by
          rcases List.mem_cons.1 (mem_dedup.1 hC) with e | hC
          · exact List.mem_cons.2 (.inl e)
          · exact List.mem_cons_of_mem _ (hs.2 _ hC)⟩
    have h₂ := c₂.2 (B :: q'.ant.erase (A ⟶ B) ⇒ q'.suc)
      ⟨fun C hC => by
          rcases List.mem_cons.1 (mem_dedup.1 hC) with e | hC
          · exact List.mem_cons.2 (.inl e)
          · exact List.mem_cons_of_mem _ (erase_sub ho.1 hs.1 _ C hC),
        fun C hC => hs.2 _ (mem_dedup.1 hC)⟩
    rw [Cert.mk, Cert.check_node hstep]
    simp [Cert.checkL, h₁, h₂]⟩

/-- GLR, from a tree for the premise less its repeated formulas. -/
def Yes.glr {q : Seq} (A : Form) (h : □A ∈ q.suc)
    (c : Yes (xbox q.ant ++ [□A] ⇒ [A]).dedup) : Yes q :=
  ⟨.mk (.glr A) [c.1], fun q' hs => by
    have hstep : S.step (.glr A) q' = .ok [xbox q'.ant ++ [□A] ⇒ [A]] :=
      step_of (by simp [Move.rule, hs.2 _ h])
    have hc := c.2 (xbox q'.ant ++ [□A] ⇒ [A])
      ⟨fun C hC => by
          rcases List.mem_append.1 (mem_dedup.1 hC) with hC | hC
          · exact List.mem_append_left _ (xbox_sub hs.1 C hC)
          · exact List.mem_append_right _ hC,
        fun C hC => mem_dedup.1 hC⟩
    rw [Cert.mk, Cert.check_node hstep]
    simp [Cert.checkL, hc]⟩

/-- The tree of moves of the identity on a formula. -/
def idCert : Form → Cert S
  | .var p => .mk (.idP p) []
  | ⊥ => .mk .botL []
  | A ⟶ B => .mk (.impR A B) [.mk (.impL A B) [idCert A, idCert B]]
  | □A => .mk (.glr A) [idCert A]

/-- **The identity replays**: at every sequent with the formula on both
sides.  (`Fam.id`, as a tree of moves.) -/
theorem idCert_check : (A : Form) → (s : Seq) → A ∈ s.ant → A ∈ s.suc →
    Cert.check s (idCert A) = true
  | .var p, s, hΓ, hΔ => by
    have h : S.step (.idP p) s = .ok [] := step_of (by simp [Move.rule, hΓ, hΔ])
    rw [idCert, Cert.mk, Cert.check_node h]
    rfl
  | ⊥, s, hΓ, _ => by
    have h : S.step .botL s = .ok [] := step_of (by simp [Move.rule, hΓ])
    rw [idCert, Cert.mk, Cert.check_node h]
    rfl
  | A ⟶ B, s, hΓ, hΔ => by
    have h₁ : S.step (.impR A B) s = .ok [A :: s.ant ⇒ B :: s.suc.erase (A ⟶ B)] :=
      step_of (by simp [Move.rule, hΔ])
    have h₂ : S.step (.impL A B) (A :: s.ant ⇒ B :: s.suc.erase (A ⟶ B)) =
        .ok [(A :: s.ant).erase (A ⟶ B) ⇒ A :: B :: s.suc.erase (A ⟶ B),
          B :: (A :: s.ant).erase (A ⟶ B) ⇒ B :: s.suc.erase (A ⟶ B)] :=
      step_of (by simp [Move.rule, hΓ])
    have hA := idCert_check A ((A :: s.ant).erase (A ⟶ B) ⇒ A :: B :: s.suc.erase (A ⟶ B))
      (mem_erase_of_ne (Form.ne_imp_left A B) (List.mem_cons_self ..)) (List.mem_cons_self ..)
    have hB := idCert_check B (B :: (A :: s.ant).erase (A ⟶ B) ⇒ B :: s.suc.erase (A ⟶ B))
      (List.mem_cons_self ..) (List.mem_cons_self ..)
    rw [idCert, Cert.mk, Cert.check_node h₁]
    simp only [List.map, Cert.checkL, Bool.and_true]
    rw [Cert.mk, Cert.check_node h₂]
    simp [Cert.checkL, hA, hB]
  | □A, s, hΓ, hΔ => by
    have h : S.step (.glr A) s = .ok [xbox s.ant ++ [□A] ⇒ [A]] :=
      step_of (by simp [Move.rule, hΔ])
    have hA := idCert_check A (xbox s.ant ++ [□A] ⇒ [A])
      (List.mem_append_left _ (body_mem_xbox hΓ)) (List.mem_singleton.2 rfl)
    rw [idCert, Cert.mk, Cert.check_node h]
    simp [Cert.checkL, hA]

/-- IdB: the identity on a boxed formula. -/
def Yes.idB {q : Seq} (A : Form) (hΓ : □A ∈ q.ant) (hΔ : □A ∈ q.suc) : Yes q :=
  ⟨idCert (□A), fun q' hs => idCert_check (□A) q' (hs.1 _ hΓ) (hs.2 _ hΔ)⟩

/-- **A tree that refutes a sequent less its repeated formulas refutes the
sequent.** -/
def Ref.ofDedup {p : Seq} (r : Ref p.dedup) : Ref p :=
  ⟨r.1, by
    have h := r.2
    rw [refutedAt_iff] at h ⊢
    exact ⟨fun A hA => h.1 A (mem_dedup.2 hA), fun B hB => h.2 B (mem_dedup.2 hB)⟩⟩

/-! ## The search -/

/-- **GLR on each boxed formula of a list**, each premise less its
repeated formulas: a tree of moves as soon as one premise has one; the
refuting trees, if every premise is refuted; nothing if `rec` gives
nothing at some premise. -/
def tryBoxesD (Γ Δ : List Form) (rec : (q : Seq) → q.Once → Option (Yes q ⊕ Ref q)) :
    (bs : List Form) → (∀ A ∈ bs, □A ∈ Δ) → Option (Yes (Γ ⇒ Δ) ⊕ Kids Γ bs)
  | [], _ => some (.inr ⟨[], fun _ h => (nomatch h), fun _ h => (nomatch h)⟩)
  | A :: bs, h =>
    match rec (xbox Γ ++ [□A] ⇒ [A]).dedup (Seq.once_dedup _) with
    | none => none
    | some (.inl c) => some (.inl (Yes.glr (q := Γ ⇒ Δ) A (h A (List.mem_cons_self ..)) c))
    | some (.inr r) =>
      match tryBoxesD Γ Δ rec bs (fun B hB => h B (List.mem_cons_of_mem _ hB)) with
      | none => none
      | some (.inl d) => some (.inl d)
      | some (.inr k) => some (.inr
          ⟨r.ofDedup.1 :: k.ts,
            fun t ht => by
              rcases List.mem_cons.1 ht with rfl | ht
              · exact ⟨A, List.mem_cons_self .., r.ofDedup.2⟩
              · obtain ⟨B, hB, hr⟩ := k.each t ht
                exact ⟨B, List.mem_cons_of_mem _ hB, hr⟩,
            fun B hB => by
              rcases List.mem_cons.1 hB with rfl | hB
              · exact ⟨r.ofDedup.1, List.mem_cons_self .., r.ofDedup.2⟩
              · obtain ⟨t, ht, hr⟩ := k.all B hB
                exact ⟨t, List.mem_cons_of_mem _ ht, hr⟩⟩)

/-- **The search at sequents without repeated formulas**, with a number of
steps allowed: the search of `GLS/Search.lean`, each premise less its
repeated formulas.  A tree of moves that replays at every sequent with
the formulas of this one, or a tree at whose root the sequent is false,
or nothing where the steps run out. -/
def searchD : Nat → (q : Seq) → q.Once → Option (Yes q ⊕ Ref q)
  | 0, _, _ => none
  | n + 1, q, ho =>
    match classify q with
    | .idP p hΓ hΔ => some (.inl (Yes.idP p hΓ hΔ))
    | .botL h => some (.inl (Yes.botL h))
    | .idB A hΓ hΔ => some (.inl (Yes.idB A hΓ hΔ))
    | .impR A B h =>
      match searchD n (A :: q.ant ⇒ B :: q.suc.erase (A ⟶ B)).dedup (Seq.once_dedup _) with
      | none => none
      | some (.inl c) => some (.inl (Yes.impR ho A B h c))
      | some (.inr r) => some (.inr ⟨r.ofDedup.1, refuted_impR h r.ofDedup.2⟩)
    | .impL A B h =>
      match searchD n (q.ant.erase (A ⟶ B) ⇒ A :: q.suc).dedup (Seq.once_dedup _) with
      | none => none
      | some (.inr r) => some (.inr ⟨r.ofDedup.1, refuted_impL₁ h r.ofDedup.2⟩)
      | some (.inl c₁) =>
        match searchD n (B :: q.ant.erase (A ⟶ B) ⇒ q.suc).dedup (Seq.once_dedup _) with
        | none => none
        | some (.inr r) => some (.inr ⟨r.ofDedup.1, refuted_impL₂ h r.ofDedup.2⟩)
        | some (.inl c₂) => some (.inl (Yes.impL ho A B h c₁ c₂))
    | .prime nP nBot _ nR nL =>
      match tryBoxesD q.ant q.suc (searchD n) (q.suc.filterMap Form.unbox?)
          (fun _ hA => mem_unboxes.1 hA) with
      | none => none
      | some (.inl c) => some (.inl c)
      | some (.inr k) => some (.inr ⟨.node (q.ant.filterMap Form.var?) k.ts,
          prime_refuted (Γ := q.ant) (Δ := q.suc) nP nBot nR nL
            (fun t ht => by
              obtain ⟨A, hA, hr⟩ := k.each t ht
              exact ⟨A, mem_unboxes.1 hA, hr⟩)
            (fun A hA => k.all A (mem_unboxes.2 hA))⟩)

/-! ## The steps are enough -/

theorem closed_dedup {U : List Form} {p : Seq} (h : Closed U p) : Closed U p.dedup := by
  intro A hA
  exact h A (hA.elim (fun h => .inl (mem_dedup.1 h)) (fun h => .inr (mem_dedup.1 h)))

theorem nImpL_dedup_le (Γ : List Form) : nImpL (dedup Γ) ≤ nImpL Γ := by
  induction Γ with
  | nil => exact Nat.le_refl _
  | cons C Γ ih =>
    by_cases hC : C ∈ dedup Γ
    · simp only [dedup, insertNew, hC, if_true, nImpL]
      omega
    · simp only [dedup, insertNew, hC, if_false, nImpL]
      omega

/-- Removing repeated formulas does not raise the measure. -/
theorem weight_dedup_le (U : List Form) (p : Seq) : weight U p.dedup ≤ weight U p := by
  unfold weight
  apply Nat.mul_le_mul
  · have h₁ := nImpL_dedup_le p.ant
    have h₂ := nImpL_dedup_le p.suc
    simp only [Seq.nImp, Seq.dedup]
    omega
  · exact Nat.pow_le_pow_right (by decide)
      (ub_le (fun B _ hB => mem_dedup.2 hB))

theorem tryBoxesD_isSome {Γ Δ : List Form}
    {rec : (q : Seq) → q.Once → Option (Yes q ⊕ Ref q)} :
    ∀ (bs : List Form) (h : ∀ A ∈ bs, □A ∈ Δ),
      (∀ A ∈ bs, (rec (xbox Γ ++ [□A] ⇒ [A]).dedup (Seq.once_dedup _)).isSome = true) →
      (tryBoxesD Γ Δ rec bs h).isSome = true
  | [], _, _ => rfl
  | A :: bs, h, hrec => by
    have hA := hrec A (List.mem_cons_self ..)
    have ih := tryBoxesD_isSome (Γ := Γ) (Δ := Δ) (rec := rec) bs
      (fun B hB => h B (List.mem_cons_of_mem _ hB))
      (fun B hB => hrec B (List.mem_cons_of_mem _ hB))
    unfold tryBoxesD
    split
    · next hn => rw [hn] at hA; cases hA
    · rfl
    · split
      · next hn => rw [hn] at ih; cases ih
      · rfl
      · rfl

/-- With more steps than the measure of the sequent, the search answers. -/
theorem searchD_isSome (U : List Form) : ∀ (n : Nat) (q : Seq) (ho : q.Once), Closed U q →
    weight U q < n → (searchD n q ho).isSome = true := by
  intro n
  induction n with
  | zero => intro q _ _ h; cases h
  | succ n ih =>
    intro q ho hU hw
    have hrec : ∀ p, PSPrem p q → (searchD n p.dedup (Seq.once_dedup p)).isSome = true := by
      intro p hp
      obtain ⟨hU', hlt⟩ := hp.step hU
      have := weight_dedup_le U p
      exact ih p.dedup _ (closed_dedup hU') (by omega)
    unfold searchD
    split
    · rfl
    · rfl
    · rfl
    · next A B h _ =>
      have h1 := hrec _ (.impR A B h rfl)
      split
      · next hn => rw [hn] at h1; cases h1
      · rfl
      · rfl
    · next A B h _ =>
      have h1 := hrec _ (.impL₁ A B h rfl)
      have h2 := hrec _ (.impL₂ A B h rfl)
      split
      · next hn => rw [hn] at h1; cases h1
      · rfl
      · split
        · next hn => rw [hn] at h2; cases h2
        · rfl
        · rfl
    · next nP nBot nB nR nL _ =>
      have h1 := tryBoxesD_isSome (Γ := q.ant) (Δ := q.suc) (rec := searchD n)
        (q.suc.filterMap Form.unbox?) (fun _ hA => mem_unboxes.1 hA)
        (fun A hA => hrec _ (.glr A nP nB nBot (mem_unboxes.1 hA) rfl))
      split
      · next hn => rw [hn] at h1; cases h1
      · rfl
      · rfl

theorem searchD_fuel (s : Seq) :
    (searchD (fuel s.dedup) s.dedup (Seq.once_dedup s)).isSome = true :=
  searchD_isSome s.dedup.boxSubs _ s.dedup _ (closed_self _) (Nat.lt_succ_self _)

/-- **S28.  For every sequent, a tree of moves that the replay accepts at
it, or a tree at whose root it is false**: by the search at sequents
without repeated formulas, which writes no sequent of GLS out. -/
def certOrRef (s : Seq) : { c : Cert S // Cert.check s c = true } ⊕ Ref s :=
  match (searchD (fuel s.dedup) s.dedup (Seq.once_dedup s)).get (searchD_fuel s) with
  | .inl c => .inl ⟨c.1, c.2 s (Seq.dedup_sub s)⟩
  | .inr r => .inr r.ofDedup

end GLS

#axioms_within_file [propext, Quot.sound]
