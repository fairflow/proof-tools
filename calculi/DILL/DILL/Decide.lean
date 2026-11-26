/-
A decision procedure for derivability without cut in dual intuitionistic
linear logic, for the sequents with an empty unrestricted zone and no
`!`: a search for a derivation, by structural recursion on a bound on
the size of the sequent, and its completeness.

In a sequent `· ; Δ ⟹ C` in which `!` does not occur, copy does not
apply (the unrestricted zone is empty), nor do !L and !R, and no other
rule changes the unrestricted zone or brings in a `!`.  Read upwards,
every other rule removes a connective or a constant, so the size of the
sequent (`ssize Δ + C.size`) bounds the depth of the search.  The search
is sound by its type: it returns a derivation.  It is complete
(`Dec.search_complete`): where there is a derivation, the search with a
bound of at least the size finds one.  So `Nonempty (CF ([] ⨾ Δ ⟹ C))`
is decidable for such a sequent (`decideCF`), and the kernel can
evaluate the decision.

The design is that of `calculi/MALL/MALL/Decide.lean`, with two zones of
which one is empty, and a conclusion.  Theory file: it ends with its
bound on axioms.
-/
import DILL.System

namespace DILL

open List

namespace Dec

/-! ## The size of a sequent -/

theorem ssize_append (l₁ l₂ : List Form) : ssize (l₁ ++ l₂) = ssize l₁ + ssize l₂ := by
  induction l₁ with
  | nil => simp [ssize]
  | cons a l ih => simp only [List.cons_append, ssize, ih]; omega

/-- Permutations of a list have its size. -/
theorem ssize_perm {l₁ l₂ : List Form} (h : l₁ ~ l₂) : ssize l₁ = ssize l₂ := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [ssize, ih]
  | swap a b l => simp only [ssize]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## No `!` -/

/-- `!` occurs in no formula of the list. -/
def LBF (l : List Form) : Prop := ∀ A ∈ l, A.bangFree = true

theorem lbf_nil : LBF [] := fun _ h => nomatch h

theorem lbf_cons {A : Form} {l : List Form} : LBF (A :: l) ↔ A.bangFree = true ∧ LBF l :=
  ⟨fun h => ⟨h A (List.mem_cons_self ..), fun B hB => h B (List.mem_cons_of_mem _ hB)⟩,
   fun h B hB => by
    rcases List.mem_cons.1 hB with e | hB
    · rw [e]; exact h.1
    · exact h.2 B hB⟩

theorem lbf_append {l₁ l₂ : List Form} : LBF (l₁ ++ l₂) ↔ LBF l₁ ∧ LBF l₂ :=
  ⟨fun h => ⟨fun B hB => h B (List.mem_append.2 (.inl hB)),
    fun B hB => h B (List.mem_append.2 (.inr hB))⟩,
   fun h B hB => by
    rcases List.mem_append.1 hB with hB | hB
    · exact h.1 B hB
    · exact h.2 B hB⟩

theorem lbf_perm {l₁ l₂ : List Form} (h : l₁ ~ l₂) (h₁ : LBF l₁) : LBF l₂ :=
  fun B hB => h₁ B (h.mem_iff.2 hB)

theorem bf_tensor {A B : Form} : (A ⊗ B).bangFree = true ↔ A.bangFree = true ∧ B.bangFree = true := by
  simp [Form.bangFree]

theorem bf_lolli {A B : Form} : (A ⊸ B).bangFree = true ↔ A.bangFree = true ∧ B.bangFree = true := by
  simp [Form.bangFree]

theorem bf_wth {A B : Form} : (A & B).bangFree = true ↔ A.bangFree = true ∧ B.bangFree = true := by
  simp [Form.bangFree]

theorem bf_plus {A B : Form} :
    (Form.plus A B).bangFree = true ↔ A.bangFree = true ∧ B.bangFree = true := by
  simp [Form.bangFree]

/-! ## The first answer over a list -/

/-- The first answer of `f` over the members of `l`.  The function is
given, with each member, the proof that it is one. -/
def firstSome {α β : Type} : (l : List α) → ((a : α) → a ∈ l → Option β) → Option β
  | [], _ => none
  | a :: l, f =>
    match f a (List.mem_cons_self ..) with
    | some b => some b
    | none => firstSome l fun x h => f x (List.mem_cons_of_mem a h)

/-- Where `f` answers at some member, there is a first answer. -/
theorem firstSome_isSome {α β : Type} {l : List α} {f : (a : α) → a ∈ l → Option β}
    {a : α} (ha : a ∈ l) (h : (f a ha).isSome = true) : (firstSome l f).isSome = true := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    unfold firstSome
    cases hb : f b (List.mem_cons_self ..) with
    | some c => rfl
    | none =>
      rcases List.mem_cons.1 ha with e | e
      · subst e
        rw [hb] at h
        cases h
      · exact ih (f := fun x h => f x (List.mem_cons_of_mem b h)) e h

/-! ## The enumerations -/

/-- Every member of a list, each with the rest. -/
def picks : List Form → List (Form × List Form)
  | [] => []
  | a :: l => (a, l) :: (picks l).map fun p => (p.1, a :: p.2)

/-- A pick is a formula of the list and the rest of it. -/
theorem picks_perm {l : List Form} {p : Form × List Form} (h : p ∈ picks l) :
    l ~ p.1 :: p.2 := by
  induction l generalizing p with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with e | h
    · subst e
      exact .refl _
    · obtain ⟨p', hp', e⟩ := List.mem_map.1 h
      subst e
      exact ((ih hp').cons a).trans (.swap ..)

/-- Every formula of the list is picked. -/
theorem picks_mem {l : List Form} {x : Form} (h : x ∈ l) : ∃ r, (x, r) ∈ picks l := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with e | h
    · subst e
      exact ⟨l, List.mem_cons_self ..⟩
    · obtain ⟨r, hr⟩ := ih h
      exact ⟨a :: r, List.mem_cons_of_mem _ (List.mem_map.2 ⟨(x, r), hr, rfl⟩)⟩

/-- Every way to split a list into two sublists: each formula goes to the
left part or to the right one. -/
def splits : List Form → List (List Form × List Form)
  | [] => [([], [])]
  | a :: l =>
    (splits l).map (fun p => (a :: p.1, p.2)) ++ (splits l).map (fun p => (p.1, a :: p.2))

/-- The two parts of a split are, together, the list. -/
theorem splits_perm {l : List Form} {p : List Form × List Form} (h : p ∈ splits l) :
    l ~ p.1 ++ p.2 := by
  induction l generalizing p with
  | nil =>
    rcases List.mem_cons.1 h with e | h
    · subst e
      exact .refl _
    · cases h
  | cons a l ih =>
    rcases List.mem_append.1 h with h | h
    · obtain ⟨p', hp', e⟩ := List.mem_map.1 h
      subst e
      exact (ih hp').cons a
    · obtain ⟨p', hp', e⟩ := List.mem_map.1 h
      subst e
      have := ih hp'
      show a :: l ~ p'.1 ++ a :: p'.2
      perm_count [this]

/-- Every way to divide the list into two is, up to the order within each
part, a split. -/
theorem splits_complete {l Γ Δ : List Form} (h : l ~ Γ ++ Δ) :
    ∃ p, p ∈ splits l ∧ p.1 ~ Γ ∧ p.2 ~ Δ := by
  induction l generalizing Γ Δ with
  | nil =>
    have e := perm_nil_eq h.symm
    have e₁ : Γ = [] := by cases Γ with
      | nil => rfl
      | cons _ _ => cases e
    subst e₁
    have e₂ : Δ = [] := e
    subst e₂
    exact ⟨([], []), List.mem_cons_self .., .refl _, .refl _⟩
  | cons a l ih =>
    have ha : a ∈ Γ ++ Δ := h.mem_iff.1 (List.mem_cons_self ..)
    rcases List.mem_append.1 ha with ha | ha
    · have hp := perm_cons_erase ha
      have h' : l ~ Γ.erase a ++ Δ := by perm_count [h, hp]
      obtain ⟨p, hp', h₁, h₂⟩ := ih h'
      refine ⟨(a :: p.1, p.2), List.mem_append.2 (.inl (List.mem_map.2 ⟨p, hp', rfl⟩)), ?_, h₂⟩
      show a :: p.1 ~ Γ
      perm_count [h₁, hp]
    · have hp := perm_cons_erase ha
      have h' : l ~ Γ ++ Δ.erase a := by perm_count [h, hp]
      obtain ⟨p, hp', h₁, h₂⟩ := ih h'
      refine ⟨(p.1, a :: p.2), List.mem_append.2 (.inr (List.mem_map.2 ⟨p, hp', rfl⟩)), h₁, ?_⟩
      show a :: p.2 ~ Δ
      perm_count [h₂, hp]

/-! ## One rule, read upwards -/

/-- What the search returns at `· ; Δ ⟹ C`: a derivation without cut, or
nothing. -/
abbrev Ans (Δ : List Form) (C : Form) : Type := Option (CF ([] ⨾ Δ ⟹ C))

/-- init: the linear zone is the conclusion alone. -/
def initCase (Δ : List Form) (C : Form) : Ans Δ C :=
  if h : Δ = [C] then some (.init C (by subst h; exact .refl _)) else none

/-- **The right rule of the conclusion**, its premises sought with `rec`.
1R asks an empty zone; ⊤R has no premise; ⊸R has one; &R has two with the
same zone; ⊕R has either of two; ⊗R tries every split of the zone.  A
letter and `𝟎` have no right rule, and !R is not sought. -/
def rightStep (rec : (Δ : List Form) → (C : Form) → Ans Δ C) (Δ : List Form) :
    (C : Form) → Ans Δ C
  | .one => if h : Δ = [] then some (.oneR (by subst h; exact .refl _)) else none
  | .top => some .topR
  | .tensor A B =>
    firstSome (splits Δ) fun s hs =>
      match rec s.1 A with
      | none => none
      | some d₁ =>
        match rec s.2 B with
        | some d₂ => some (.tensorR s.1 s.2 (splits_perm hs) d₁ d₂)
        | none => none
  | .lolli A B =>
    match rec (A :: Δ) B with
    | some d => some (.lolliR d)
    | none => none
  | .wth A B =>
    match rec Δ A with
    | none => none
    | some d₁ =>
      match rec Δ B with
      | some d₂ => some (.withR d₁ d₂)
      | none => none
  | .plus A B =>
    match rec Δ A with
    | some d => some (.plusR₁ d)
    | none =>
      match rec Δ B with
      | some d => some (.plusR₂ d)
      | none => none
  | _ => none

/-- **The left rule of a principal formula**: the linear zone `Δ` is `P`
and `Δ'`; `P` is taken as principal, and the premises are sought with
`rec`.  0L has no premise; ⊗L and 1L have one; &L has either of two; ⊕L
has two with the same zone; ⊸L tries every split of `Δ'`.  A letter and
`⊤` have no left rule, and !L is not sought. -/
def leftStep (rec : (Δ : List Form) → (C : Form) → Ans Δ C) (Δ : List Form) (C : Form) :
    (P : Form) → (Δ' : List Form) → Δ ~ P :: Δ' → Ans Δ C
  | .zero, Δ', h => some (.zeroL Δ' h)
  | .one, Δ', h =>
    match rec Δ' C with
    | some d => some (.oneL Δ' h d)
    | none => none
  | .tensor A B, Δ', h =>
    match rec (A :: B :: Δ') C with
    | some d => some (.tensorL A B Δ' h d)
    | none => none
  | .wth A B, Δ', h =>
    match rec (A :: Δ') C with
    | some d => some (.withL₁ A B Δ' h d)
    | none =>
      match rec (B :: Δ') C with
      | some d => some (.withL₂ A B Δ' h d)
      | none => none
  | .plus A B, Δ', h =>
    match rec (A :: Δ') C with
    | none => none
    | some d₁ =>
      match rec (B :: Δ') C with
      | some d₂ => some (.plusL A B Δ' h d₁ d₂)
      | none => none
  | .lolli A B, Δ', h =>
    firstSome (splits Δ') fun s hs =>
      match rec s.1 A with
      | none => none
      | some d₁ =>
        match rec (B :: s.2) C with
        | some d₂ => some (.lolliL A B s.1 s.2 (h.trans ((splits_perm hs).cons _)) d₁ d₂)
        | none => none
  | _, _, _ => none

/-- **The search for a derivation without cut** of `· ; Δ ⟹ C`, with a
bound on its depth: init, then the right rule of the conclusion, then,
for each formula occurrence of the linear zone in turn, the left rule of
that occurrence. -/
def search : Nat → (Δ : List Form) → (C : Form) → Ans Δ C
  | 0, _, _ => none
  | n + 1, Δ, C =>
    match initCase Δ C with
    | some d => some d
    | none =>
      match rightStep (search n) Δ C with
      | some d => some d
      | none =>
        firstSome (picks Δ) fun p hp => leftStep (search n) Δ C p.1 p.2 (picks_perm hp)

/-! ## Completeness -/

theorem initCase_complete {Δ : List Form} {C : Form} (h : Δ ~ [C]) :
    (initCase Δ C).isSome = true := by
  cases perm_singleton_eq h
  simp [initCase]

/-- **One rule, read upwards, is complete**: where `rec` finds a
derivation of every derivable sequent without `!` of size at most `n`,
and `· ; Δ ⟹ C`, without `!` and of size at most `n + 1`, has a
derivation, either the sequent is an instance of init, or the last rule
of the derivation is a right rule and `rightStep` finds a derivation, or
it is a left rule with a principal formula `P`, and `leftStep` with `P`
as principal, whatever list is given as the rest, finds a derivation. -/
theorem step_complete {rec : (Δ : List Form) → (C : Form) → Ans Δ C} {n : Nat}
    (hrec : ∀ Δ C, ssize Δ + C.size ≤ n → LBF (C :: Δ) → Nonempty (CF ([] ⨾ Δ ⟹ C)) →
      (rec Δ C).isSome = true)
    {Δ : List Form} {C : Form} (hs : ssize Δ + C.size ≤ n + 1) (hbf : LBF (C :: Δ))
    (d : CF ([] ⨾ Δ ⟹ C)) :
    (initCase Δ C).isSome = true ∨ (rightStep rec Δ C).isSome = true ∨
      ∃ P, P ∈ Δ ∧ ∀ Δ' (h : Δ ~ P :: Δ'), (leftStep rec Δ C P Δ' h).isSome = true := by
  have mem : ∀ {P : Form} {Δ' : List Form}, Δ ~ P :: Δ' → P ∈ Δ :=
    fun h => h.mem_iff.2 (List.mem_cons_self ..)
  obtain ⟨hC, hΔ⟩ := lbf_cons.1 hbf
  cases d with
  | init A h => exact .inl (initCase_complete h)
  | copy A hΓ d => cases hΓ
  | cut hc => cases hc
  | cutU hc => cases hc
  | bangL A Δ₀ h d => exact absurd (hΔ _ (mem h)) (by simp [Form.bangFree])
  | bangR h d => exact absurd hC (by simp [Form.bangFree])
  | topR => exact .inr (.inl rfl)
  | oneR h =>
    cases perm_nil_eq h
    exact .inr (.inl rfl)
  | tensorR Δ₁ Δ₂ h d₁ d₂ =>
    refine .inr (.inl ?_)
    obtain ⟨s, hs₀, h₁, h₂⟩ := splits_complete h
    have hsz := ssize_perm (splits_perm hs₀)
    rw [ssize_append] at hsz
    have hb := lbf_append.1 (lbf_perm (splits_perm hs₀) hΔ)
    simp only [Form.size] at hs
    obtain ⟨hA, hB⟩ := bf_tensor.1 hC
    obtain ⟨d₁', hd₁⟩ := Option.isSome_iff_exists.1
      (hrec s.1 _ (by omega) (lbf_cons.2 ⟨hA, hb.1⟩) ⟨d₁.exch h₁.symm⟩)
    obtain ⟨d₂', hd₂⟩ := Option.isSome_iff_exists.1
      (hrec s.2 _ (by omega) (lbf_cons.2 ⟨hB, hb.2⟩) ⟨d₂.exch h₂.symm⟩)
    simp only [rightStep]
    refine firstSome_isSome hs₀ ?_
    simp only [hd₁, hd₂]
    rfl
  | lolliR d =>
    refine .inr (.inl ?_)
    simp only [Form.size] at hs
    obtain ⟨hA, hB⟩ := bf_lolli.1 hC
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1
      (hrec (_ :: Δ) _ (by simp only [ssize]; omega) (lbf_cons.2 ⟨hB, lbf_cons.2 ⟨hA, hΔ⟩⟩) ⟨d⟩)
    simp only [rightStep, hd']
    rfl
  | withR d₁ d₂ =>
    refine .inr (.inl ?_)
    simp only [Form.size] at hs
    obtain ⟨hA, hB⟩ := bf_wth.1 hC
    obtain ⟨d₁', hd₁⟩ := Option.isSome_iff_exists.1
      (hrec Δ _ (by omega) (lbf_cons.2 ⟨hA, hΔ⟩) ⟨d₁⟩)
    obtain ⟨d₂', hd₂⟩ := Option.isSome_iff_exists.1
      (hrec Δ _ (by omega) (lbf_cons.2 ⟨hB, hΔ⟩) ⟨d₂⟩)
    simp only [rightStep, hd₁, hd₂]
    rfl
  | plusR₁ d =>
    refine .inr (.inl ?_)
    simp only [Form.size] at hs
    obtain ⟨hA, hB⟩ := bf_plus.1 hC
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1
      (hrec Δ _ (by omega) (lbf_cons.2 ⟨hA, hΔ⟩) ⟨d⟩)
    simp only [rightStep, hd']
    rfl
  | @plusR₂ _ _ A B d =>
    refine .inr (.inl ?_)
    simp only [Form.size] at hs
    obtain ⟨hA, hB⟩ := bf_plus.1 hC
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1
      (hrec Δ _ (by omega) (lbf_cons.2 ⟨hB, hΔ⟩) ⟨d⟩)
    simp only [rightStep]
    cases rec Δ A with
    | some _ => rfl
    | none =>
      simp only [hd']
      rfl
  | zeroL Δ₀ h => exact .inr (.inr ⟨_, mem h, fun Δ' h' => rfl⟩)
  | oneL Δ₀ h d =>
    refine .inr (.inr ⟨_, mem h, fun Δ' h' => ?_⟩)
    have e : Δ₀ ~ Δ' := by perm_count [h, h']
    have hs' := ssize_perm h'
    have hb := lbf_cons.1 (lbf_perm h' hΔ)
    simp only [ssize, Form.size] at hs'
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1
      (hrec Δ' C (by omega) (lbf_cons.2 ⟨hC, hb.2⟩) ⟨d.exch e⟩)
    simp only [leftStep, hd']
    rfl
  | tensorL A B Δ₀ h d =>
    refine .inr (.inr ⟨_, mem h, fun Δ' h' => ?_⟩)
    have e : A :: B :: Δ₀ ~ A :: B :: Δ' := by perm_count [h, h']
    have hs' := ssize_perm h'
    have hb := lbf_cons.1 (lbf_perm h' hΔ)
    have hP := bf_tensor.1 hb.1
    simp only [ssize, Form.size] at hs'
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1
      (hrec (A :: B :: Δ') C (by simp only [ssize]; omega)
        (lbf_cons.2 ⟨hC, lbf_cons.2 ⟨hP.1, lbf_cons.2 ⟨hP.2, hb.2⟩⟩⟩) ⟨d.exch e⟩)
    simp only [leftStep, hd']
    rfl
  | withL₁ A B Δ₀ h d =>
    refine .inr (.inr ⟨_, mem h, fun Δ' h' => ?_⟩)
    have e : A :: Δ₀ ~ A :: Δ' := by perm_count [h, h']
    have hs' := ssize_perm h'
    have hb := lbf_cons.1 (lbf_perm h' hΔ)
    have hP := bf_wth.1 hb.1
    simp only [ssize, Form.size] at hs'
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1
      (hrec (A :: Δ') C (by simp only [ssize]; omega)
        (lbf_cons.2 ⟨hC, lbf_cons.2 ⟨hP.1, hb.2⟩⟩) ⟨d.exch e⟩)
    simp only [leftStep, hd']
    rfl
  | withL₂ A B Δ₀ h d =>
    refine .inr (.inr ⟨_, mem h, fun Δ' h' => ?_⟩)
    have e : B :: Δ₀ ~ B :: Δ' := by perm_count [h, h']
    have hs' := ssize_perm h'
    have hb := lbf_cons.1 (lbf_perm h' hΔ)
    have hP := bf_wth.1 hb.1
    simp only [ssize, Form.size] at hs'
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1
      (hrec (B :: Δ') C (by simp only [ssize]; omega)
        (lbf_cons.2 ⟨hC, lbf_cons.2 ⟨hP.2, hb.2⟩⟩) ⟨d.exch e⟩)
    simp only [leftStep]
    cases rec (A :: Δ') C with
    | some _ => rfl
    | none =>
      simp only [hd']
      rfl
  | plusL A B Δ₀ h d₁ d₂ =>
    refine .inr (.inr ⟨_, mem h, fun Δ' h' => ?_⟩)
    have e₁ : A :: Δ₀ ~ A :: Δ' := by perm_count [h, h']
    have e₂ : B :: Δ₀ ~ B :: Δ' := by perm_count [h, h']
    have hs' := ssize_perm h'
    have hb := lbf_cons.1 (lbf_perm h' hΔ)
    have hP := bf_plus.1 hb.1
    simp only [ssize, Form.size] at hs'
    obtain ⟨d₁', hd₁⟩ := Option.isSome_iff_exists.1
      (hrec (A :: Δ') C (by simp only [ssize]; omega)
        (lbf_cons.2 ⟨hC, lbf_cons.2 ⟨hP.1, hb.2⟩⟩) ⟨d₁.exch e₁⟩)
    obtain ⟨d₂', hd₂⟩ := Option.isSome_iff_exists.1
      (hrec (B :: Δ') C (by simp only [ssize]; omega)
        (lbf_cons.2 ⟨hC, lbf_cons.2 ⟨hP.2, hb.2⟩⟩) ⟨d₂.exch e₂⟩)
    simp only [leftStep, hd₁, hd₂]
    rfl
  | lolliL A B Δ₁ Δ₂ h d₁ d₂ =>
    refine .inr (.inr ⟨_, mem h, fun Δ' h' => ?_⟩)
    have e : Δ' ~ Δ₁ ++ Δ₂ := by perm_count [h, h']
    obtain ⟨s, hs₀, h₁, h₂⟩ := splits_complete e
    have hs' := ssize_perm h'
    have hsz := ssize_perm (splits_perm hs₀)
    rw [ssize_append] at hsz
    have hb := lbf_cons.1 (lbf_perm h' hΔ)
    have hP := bf_lolli.1 hb.1
    have hb' := lbf_append.1 (lbf_perm (splits_perm hs₀) hb.2)
    simp only [ssize, Form.size] at hs'
    obtain ⟨d₁', hd₁⟩ := Option.isSome_iff_exists.1
      (hrec s.1 A (by omega) (lbf_cons.2 ⟨hP.1, hb'.1⟩) ⟨d₁.exch h₁.symm⟩)
    obtain ⟨d₂', hd₂⟩ := Option.isSome_iff_exists.1
      (hrec (B :: s.2) C (by simp only [ssize]; omega)
        (lbf_cons.2 ⟨hC, lbf_cons.2 ⟨hP.2, hb'.2⟩⟩) ⟨d₂.exch (h₂.symm.cons B)⟩)
    simp only [leftStep]
    refine firstSome_isSome hs₀ ?_
    simp only [hd₁, hd₂]
    rfl

/-- **The search is complete**: where a sequent `· ; Δ ⟹ C` without `!`
and of size at most `n` has a derivation without cut, the search with
the bound `n` finds one.  (Soundness is by the type of `search`: what it
finds is a derivation.) -/
theorem search_complete : ∀ (n : Nat) (Δ : List Form) (C : Form), ssize Δ + C.size ≤ n →
    LBF (C :: Δ) → Nonempty (CF ([] ⨾ Δ ⟹ C)) → (search n Δ C).isSome = true
  | 0, _, C, hs, _, _ => absurd C.size_pos (by omega)
  | n + 1, Δ, C, hs, hbf, ⟨d⟩ => by
    unfold search
    cases hinit : initCase Δ C with
    | some _ => rfl
    | none =>
      cases hright : rightStep (search n) Δ C with
      | some _ => rfl
      | none =>
        rcases step_complete (search_complete n) hs hbf d with h | h | ⟨P, hP, hstep⟩
        · rw [hinit] at h
          cases h
        · rw [hright] at h
          cases h
        · obtain ⟨r, hr⟩ := picks_mem hP
          exact firstSome_isSome hr (hstep r (picks_perm hr))

/-- The search with the size of the sequent for its bound. -/
def searchCF (Δ : List Form) (C : Form) : Ans Δ C := search (ssize Δ + C.size) Δ C

/-- The search with the size of the sequent for its bound finds a
derivation exactly where there is one. -/
theorem searchCF_isSome_iff (Δ : List Form) (C : Form) (hbf : ∀ A ∈ C :: Δ, A.bangFree = true) :
    (searchCF Δ C).isSome = true ↔ Nonempty (CF ([] ⨾ Δ ⟹ C)) := by
  constructor
  · intro h
    obtain ⟨d, _⟩ := Option.isSome_iff_exists.1 h
    exact ⟨d⟩
  · exact search_complete _ Δ C (Nat.le_refl _) hbf

end Dec

/-- **Derivability without cut is decidable for the sequents with an
empty unrestricted zone and no `!`**: by the search. -/
def decideCF (Δ : List Form) (C : Form) (hbf : ∀ A ∈ C :: Δ, A.bangFree = true) :
    Decidable (Nonempty (CF ([] ⨾ Δ ⟹ C))) :=
  decidable_of_iff _ (Dec.searchCF_isSome_iff Δ C hbf)

namespace Dec

/-! ## The decision as an instance

`decideCF` asks a proof that `!` does not occur.  For a sequent written
out, the two classes below find that proof by the shape of the formulas,
so that `decide` applies (with `open DILL.Dec`: the instance of
`Decidable` is scoped). -/

/-- `!` does not occur in the formula. -/
class BFForm (A : Form) : Prop where
  out : A.bangFree = true

/-- `!` occurs in no formula of the list. -/
class BFList (l : List Form) : Prop where
  out : LBF l

instance (n : Nat) : BFForm (.atom n) := ⟨rfl⟩
instance : BFForm .one := ⟨rfl⟩
instance : BFForm .top := ⟨rfl⟩
instance : BFForm .zero := ⟨rfl⟩
instance (A B : Form) [BFForm A] [BFForm B] : BFForm (A ⊗ B) :=
  ⟨bf_tensor.2 ⟨BFForm.out, BFForm.out⟩⟩
instance (A B : Form) [BFForm A] [BFForm B] : BFForm (A ⊸ B) :=
  ⟨bf_lolli.2 ⟨BFForm.out, BFForm.out⟩⟩
instance (A B : Form) [BFForm A] [BFForm B] : BFForm (A & B) :=
  ⟨bf_wth.2 ⟨BFForm.out, BFForm.out⟩⟩
instance (A B : Form) [BFForm A] [BFForm B] : BFForm (.plus A B) :=
  ⟨bf_plus.2 ⟨BFForm.out, BFForm.out⟩⟩
instance : BFList [] := ⟨lbf_nil⟩
instance (A : Form) (l : List Form) [BFForm A] [BFList l] : BFList (A :: l) :=
  ⟨lbf_cons.2 ⟨BFForm.out, BFList.out⟩⟩

/-- The decision, found as an instance for a sequent written out. -/
scoped instance decCF (Δ : List Form) (C : Form) [BFList Δ] [BFForm C] :
    Decidable (Nonempty (CF ([] ⨾ Δ ⟹ C))) :=
  decideCF Δ C (lbf_cons.2 ⟨BFForm.out, BFList.out⟩)

/-! ## Six sequents, decided in the kernel -/

/-- `· ; a ⊸ b, a ⟹ b` is derivable. -/
example : Nonempty (CF ([] ⨾ [.atom 0 ⊸ .atom 1, .atom 0] ⟹ .atom 1)) := by decide

/-- `· ; a ⊗ b ⟹ b ⊗ a` is derivable. -/
example : Nonempty (CF ([] ⨾ [.atom 0 ⊗ .atom 1] ⟹ .atom 1 ⊗ .atom 0)) := by decide

/-- `· ; (a ⊸ b) & (a ⊸ c) ⟹ a ⊸ (b & c)` is derivable. -/
example : Nonempty (CF ([] ⨾ [(.atom 0 ⊸ .atom 1) & (.atom 0 ⊸ .atom 2)] ⟹
    .atom 0 ⊸ (.atom 1 & .atom 2))) := by decide

/-- `· ; a ⟹ 1` is not derivable: no weakening of the linear zone. -/
example : ¬ Nonempty (CF ([] ⨾ [.atom 0] ⟹ 𝟏)) := by decide

/-- `· ; a ⟹ a ⊗ a` is not derivable: no contraction of the linear
zone. -/
example : ¬ Nonempty (CF ([] ⨾ [.atom 0] ⟹ .atom 0 ⊗ .atom 0)) := by decide

/-- `· ; a ⊸ (b ⊗ c) ⟹ (a ⊸ b) ⊗ (a ⊸ c)` is not derivable. -/
example : ¬ Nonempty (CF ([] ⨾ [.atom 0 ⊸ (.atom 1 ⊗ .atom 2)] ⟹
    (.atom 0 ⊸ .atom 1) ⊗ (.atom 0 ⊸ .atom 2))) := by decide

end Dec

end DILL

#axioms_within_file [propext, Quot.sound]
