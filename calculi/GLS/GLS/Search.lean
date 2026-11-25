/-
Goal 2, completeness as data: a search that returns, for every sequent, a
derivation in GLS or a finite tree at whose root the sequent is false.

The search is backward proof search in PSGLS (the Coq file's
`PSGLS_rules`): an axiom where one applies, IdB among them; else an
implication rule, which loses nothing; else GLR on each boxed formula of
the succedent.  Where every premise of GLR is refuted, the refuting trees
become the children of a new root (this construction is not in the
source's Coq files: `campaign/plan.md`, Q3).  It is written by structural
recursion on a number of steps allowed, and `GLS/Measure.lean` gives a
number that is enough.  Theory file: it ends with its bound on axioms.
-/
import GLS.Identity
import GLS.TreeModel
import GLS.Measure

namespace GLS

/-- A tree at whose root the sequent is false, by the computed truth. -/
abbrev Ref (s : Seq) : Type := { t : Tree // s.refutedAt t = true }

theorem refutedAt_iff {s : Seq} {t : Tree} : s.refutedAt t = true ↔
    (∀ A ∈ s.ant, A.holds t = true) ∧ (∀ B ∈ s.suc, B.holds t = false) := by
  simp [Seq.refutedAt]

/-! ## What applies at a sequent -/

/-- A variable on both sides, if there is one. -/
def findIdP (Γ Δ : List Form) : Option Nat :=
  Γ.findSome? fun A => match A with
    | .var p => if Form.var p ∈ Δ then some p else none
    | _ => none

theorem findIdP_some {Γ Δ : List Form} {p : Nat} (h : findIdP Γ Δ = some p) :
    Form.var p ∈ Γ ∧ Form.var p ∈ Δ := by
  obtain ⟨A, hA, hf⟩ := List.exists_of_findSome?_eq_some h
  cases A with
  | var q =>
    by_cases hq : Form.var q ∈ Δ
    · simp only [hq, if_true, Option.some.injEq] at hf
      subst hf; exact ⟨hA, hq⟩
    · simp [hq] at hf
  | bot => simp at hf
  | imp _ _ => simp at hf
  | box _ => simp at hf

theorem findIdP_none {Γ Δ : List Form} (h : findIdP Γ Δ = none) : ¬ (Γ ⇒ Δ).IsIdP := by
  rintro ⟨p, hΓ, hΔ⟩
  have := List.findSome?_eq_none_iff.1 h _ hΓ
  simp [hΔ] at this

/-- A boxed formula on both sides, if there is one: its body. -/
def findIdB (Γ Δ : List Form) : Option Form :=
  Γ.findSome? fun A => match A with
    | □B => if □B ∈ Δ then some B else none
    | _ => none

theorem findIdB_some {Γ Δ : List Form} {B : Form} (h : findIdB Γ Δ = some B) :
    □B ∈ Γ ∧ □B ∈ Δ := by
  obtain ⟨A, hA, hf⟩ := List.exists_of_findSome?_eq_some h
  cases A with
  | box C =>
    by_cases hC : □C ∈ Δ
    · simp only [hC, if_true, Option.some.injEq] at hf
      subst hf; exact ⟨hA, hC⟩
    · simp [hC] at hf
  | bot => simp at hf
  | imp _ _ => simp at hf
  | var _ => simp at hf

theorem findIdB_none {Γ Δ : List Form} (h : findIdB Γ Δ = none) : ¬ (Γ ⇒ Δ).IsIdB := by
  rintro ⟨B, hΓ, hΔ⟩
  have := List.findSome?_eq_none_iff.1 h _ hΓ
  simp [hΔ] at this

/-- An implication of a list, if there is one: its two parts. -/
def findImp (Γ : List Form) : Option (Form × Form) :=
  Γ.findSome? fun A => match A with
    | A ⟶ B => some (A, B)
    | _ => none

theorem findImp_some {Γ : List Form} {A B : Form} (h : findImp Γ = some (A, B)) :
    A ⟶ B ∈ Γ := by
  obtain ⟨C, hC, hf⟩ := List.exists_of_findSome?_eq_some h
  cases C with
  | imp C₁ C₂ =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf; exact hC
  | bot => simp at hf
  | box _ => simp at hf
  | var _ => simp at hf

theorem findImp_none {Γ : List Form} (h : findImp Γ = none) : ∀ A B, A ⟶ B ∉ Γ := by
  intro A B hΓ
  have := List.findSome?_eq_none_iff.1 h _ hΓ
  simp at this

/-- The body of a boxed formula. -/
def Form.unbox? : Form → Option Form
  | □A => some A
  | _ => none

theorem mem_unboxes {Δ : List Form} {A : Form} : A ∈ Δ.filterMap Form.unbox? ↔ □A ∈ Δ := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨C, hC, hf⟩
    cases C <;> simp [Form.unbox?] at hf
    subst hf; exact hC
  · intro h; exact ⟨□A, h, rfl⟩

/-- The number of a variable. -/
def Form.var? : Form → Option Nat
  | .var p => some p
  | _ => none

theorem mem_vars {Γ : List Form} {p : Nat} : p ∈ Γ.filterMap Form.var? ↔ Form.var p ∈ Γ := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨C, hC, hf⟩
    cases C <;> simp [Form.var?] at hf
    subst hf; exact hC
  · intro h; exact ⟨.var p, h, rfl⟩

/-- **What applies at a sequent**, in the order the search tries: an axiom
of PSGLS, an implication on the right, one on the left, or nothing but
GLR. -/
inductive Shape (s : Seq) : Type where
  | idP (p : Nat) (hΓ : Form.var p ∈ s.ant) (hΔ : Form.var p ∈ s.suc)
  | botL (h : ⊥ ∈ s.ant)
  | idB (A : Form) (hΓ : □A ∈ s.ant) (hΔ : □A ∈ s.suc)
  | impR (A B : Form) (h : A ⟶ B ∈ s.suc)
  | impL (A B : Form) (h : A ⟶ B ∈ s.ant)
  | prime (nP : ¬ s.IsIdP) (nBot : ¬ s.IsBotL) (nB : ¬ s.IsIdB)
      (nR : ∀ A B, A ⟶ B ∉ s.suc) (nL : ∀ A B, A ⟶ B ∉ s.ant)

/-- The shape of a sequent. -/
def classify (s : Seq) : Shape s :=
  match hP : findIdP s.ant s.suc with
  | some p => .idP p (findIdP_some hP).1 (findIdP_some hP).2
  | none =>
    if hBot : ⊥ ∈ s.ant then .botL hBot else
    match hB : findIdB s.ant s.suc with
    | some A => .idB A (findIdB_some hB).1 (findIdB_some hB).2
    | none =>
      match hR : findImp s.suc with
      | some (A, B) => .impR A B (findImp_some hR)
      | none =>
        match hL : findImp s.ant with
        | some (A, B) => .impL A B (findImp_some hL)
        | none => .prime (findIdP_none hP) hBot (findIdB_none hB) (findImp_none hR)
            (findImp_none hL)

/-! ## A refutation of a premise is one of the conclusion; and the new root -/

theorem refuted_impR {Γ Δ : List Form} {A B : Form} {t : Tree} (_h : A ⟶ B ∈ Δ)
    (hr : (A :: Γ ⇒ B :: Δ.erase (A ⟶ B)).refutedAt t = true) : (Γ ⇒ Δ).refutedAt t = true := by
  rw [refutedAt_iff] at hr ⊢
  obtain ⟨h1, h2⟩ := hr
  refine ⟨fun C hC => h1 C (List.mem_cons_of_mem _ hC), fun C hC => ?_⟩
  rcases eq_or_mem_erase (b := A ⟶ B) hC with rfl | hC
  · have hA := h1 A (List.mem_cons_self ..)
    have hB := h2 B (List.mem_cons_self ..)
    simp [Form.holds, hA, hB]
  · exact h2 C (List.mem_cons_of_mem _ hC)

theorem refuted_impL₁ {Γ Δ : List Form} {A B : Form} {t : Tree} (_h : A ⟶ B ∈ Γ)
    (hr : (Γ.erase (A ⟶ B) ⇒ A :: Δ).refutedAt t = true) : (Γ ⇒ Δ).refutedAt t = true := by
  rw [refutedAt_iff] at hr ⊢
  obtain ⟨h1, h2⟩ := hr
  refine ⟨fun C hC => ?_, fun C hC => h2 C (List.mem_cons_of_mem _ hC)⟩
  rcases eq_or_mem_erase (b := A ⟶ B) hC with rfl | hC
  · have hA := h2 A (List.mem_cons_self ..)
    simp [Form.holds, hA]
  · exact h1 C hC

theorem refuted_impL₂ {Γ Δ : List Form} {A B : Form} {t : Tree} (_h : A ⟶ B ∈ Γ)
    (hr : (B :: Γ.erase (A ⟶ B) ⇒ Δ).refutedAt t = true) : (Γ ⇒ Δ).refutedAt t = true := by
  rw [refutedAt_iff] at hr ⊢
  obtain ⟨h1, h2⟩ := hr
  refine ⟨fun C hC => ?_, h2⟩
  rcases eq_or_mem_erase (b := A ⟶ B) hC with rfl | hC
  · have hB := h1 B (List.mem_cons_self ..)
    simp [Form.holds, hB]
  · exact h1 C (List.mem_cons_of_mem _ hC)

/-- **The trees that refute the premises of GLR** at an antecedent `Γ`, for
the boxed formulas `□A` with `A` in `bs`: each tree refutes one of the
premises, and each premise is refuted by one of the trees. -/
structure Kids (Γ : List Form) (bs : List Form) where
  /-- The trees. -/
  ts : List Tree
  /-- Each tree refutes a premise. -/
  each : ∀ t ∈ ts, ∃ A ∈ bs, (xbox Γ ++ [□A] ⇒ [A]).refutedAt t = true
  /-- Each premise is refuted by a tree. -/
  all : ∀ A ∈ bs, ∃ t ∈ ts, (xbox Γ ++ [□A] ⇒ [A]).refutedAt t = true

/-- **The new root** (the truth lemma of the construction).  A sequent
that is no axiom and has no implication at top level, every premise of
GLR at which is refuted by one of the trees `ts`, each of which refutes
such a premise, is false at the root of the tree whose children are `ts`
and at whose root the variables of the antecedent are true. -/
theorem prime_refuted {Γ Δ : List Form} {ts : List Tree}
    (nP : ¬ (Γ ⇒ Δ).IsIdP) (nBot : ¬ (Γ ⇒ Δ).IsBotL)
    (nR : ∀ A B, A ⟶ B ∉ Δ) (nL : ∀ A B, A ⟶ B ∉ Γ)
    (each : ∀ t ∈ ts, ∃ A, □A ∈ Δ ∧ (xbox Γ ++ [□A] ⇒ [A]).refutedAt t = true)
    (all : ∀ A, □A ∈ Δ → ∃ t ∈ ts, (xbox Γ ++ [□A] ⇒ [A]).refutedAt t = true) :
    (Γ ⇒ Δ).refutedAt (.node (Γ.filterMap Form.var?) ts) = true := by
  rw [refutedAt_iff]
  constructor
  · intro C hC
    cases C with
    | var p =>
      show (List.filterMap Form.var? Γ).contains p = true
      exact List.contains_iff_mem.2 (mem_vars.2 hC)
    | bot => exact absurd hC nBot
    | imp C₁ C₂ => exact absurd hC (nL _ _)
    | box B =>
      show (Tree.node _ ts).desc.all (fun u => B.holds u) = true
      rw [List.all_eq_true, Tree.desc_node]
      intro u hu
      obtain ⟨k, hk, hu⟩ := Tree.mem_descL.1 hu
      obtain ⟨A, _, hr⟩ := each k hk
      rw [refutedAt_iff] at hr
      rcases hu with rfl | hu
      · exact hr.1 B (List.mem_append_left _ (body_mem_xbox hC))
      · have hbox := hr.1 (□B) (List.mem_append_left _ (box_mem_xbox hC))
        have : k.desc.all (fun u => B.holds u) = true := hbox
        exact List.all_eq_true.1 this u hu
  · intro C hC
    cases C with
    | var p =>
      show (List.filterMap Form.var? Γ).contains p = false
      cases hc : (List.filterMap Form.var? Γ).contains p with
      | false => rfl
      | true => exact absurd ⟨p, mem_vars.1 (List.contains_iff_mem.1 hc), hC⟩ nP
    | bot => rfl
    | imp C₁ C₂ => exact absurd hC (nR _ _)
    | box A =>
      obtain ⟨t, ht, hr⟩ := all A hC
      rw [refutedAt_iff] at hr
      have hA : A.holds t = false := hr.2 A (List.mem_singleton.2 rfl)
      show (Tree.node _ ts).desc.all (fun u => A.holds u) = false
      cases hall : (Tree.node (List.filterMap Form.var? Γ) ts).desc.all (fun u => A.holds u) with
      | false => rfl
      | true =>
        rw [List.all_eq_true, Tree.desc_node] at hall
        have := hall t (Tree.mem_descL.2 ⟨t, ht, .inl rfl⟩)
        rw [hA] at this; cases this

/-! ## The search -/

/-- **GLR on each boxed formula of a list**: a derivation as soon as one
premise has one; the refuting trees, if every premise is refuted; nothing
if `rec` gives nothing at some premise. -/
def tryBoxes (Γ Δ : List Form) (rec : (s : Seq) → Option (Fam s ⊕ Ref s)) :
    (bs : List Form) → (∀ A ∈ bs, □A ∈ Δ) → Option (Fam (Γ ⇒ Δ) ⊕ Kids Γ bs)
  | [], _ => some (.inr ⟨[], fun _ h => (nomatch h), fun _ h => (nomatch h)⟩)
  | A :: bs, h =>
    match rec (xbox Γ ++ [□A] ⇒ [A]) with
    | none => none
    | some (.inl d) => some (.inl (.glr A (h A (List.mem_cons_self ..)) d))
    | some (.inr r) =>
      match tryBoxes Γ Δ rec bs (fun B hB => h B (List.mem_cons_of_mem _ hB)) with
      | none => none
      | some (.inl d) => some (.inl d)
      | some (.inr k) => some (.inr
          ⟨r.1 :: k.ts,
            fun t ht => by
              rcases List.mem_cons.1 ht with rfl | ht
              · exact ⟨A, List.mem_cons_self .., r.2⟩
              · obtain ⟨B, hB, hr⟩ := k.each t ht
                exact ⟨B, List.mem_cons_of_mem _ hB, hr⟩,
            fun B hB => by
              rcases List.mem_cons.1 hB with rfl | hB
              · exact ⟨r.1, List.mem_cons_self .., r.2⟩
              · obtain ⟨t, ht, hr⟩ := k.all B hB
                exact ⟨t, List.mem_cons_of_mem _ ht, hr⟩⟩)

/-- **The search, with a number of steps allowed**: a derivation in GLS,
or a tree at whose root the sequent is false, or nothing where the steps
run out. -/
def search : Nat → (s : Seq) → Option (Fam s ⊕ Ref s)
  | 0, _ => none
  | n + 1, s =>
    match classify s with
    | .idP p hΓ hΔ => some (.inl (.idP p hΓ hΔ))
    | .botL h => some (.inl (.botL h))
    | .idB A hΓ hΔ => some (.inl (Fam.id (□A) hΓ hΔ))
    | .impR A B h =>
      match search n (A :: s.ant ⇒ B :: s.suc.erase (A ⟶ B)) with
      | none => none
      | some (.inl d) => some (.inl (.impR A B h d))
      | some (.inr r) => some (.inr ⟨r.1, refuted_impR h r.2⟩)
    | .impL A B h =>
      match search n (s.ant.erase (A ⟶ B) ⇒ A :: s.suc) with
      | none => none
      | some (.inr r) => some (.inr ⟨r.1, refuted_impL₁ h r.2⟩)
      | some (.inl d₁) =>
        match search n (B :: s.ant.erase (A ⟶ B) ⇒ s.suc) with
        | none => none
        | some (.inr r) => some (.inr ⟨r.1, refuted_impL₂ h r.2⟩)
        | some (.inl d₂) => some (.inl (.impL A B h d₁ d₂))
    | .prime nP nBot _ nR nL =>
      match tryBoxes s.ant s.suc (search n) (s.suc.filterMap Form.unbox?)
          (fun _ hA => mem_unboxes.1 hA) with
      | none => none
      | some (.inl d) => some (.inl d)
      | some (.inr k) => some (.inr ⟨.node (s.ant.filterMap Form.var?) k.ts,
          prime_refuted (Γ := s.ant) (Δ := s.suc) nP nBot nR nL
            (fun t ht => by
              obtain ⟨A, hA, hr⟩ := k.each t ht
              exact ⟨A, mem_unboxes.1 hA, hr⟩)
            (fun A hA => k.all A (mem_unboxes.2 hA))⟩)

/-! ## The steps are enough -/

theorem tryBoxes_isSome {Γ Δ : List Form} {rec : (s : Seq) → Option (Fam s ⊕ Ref s)} :
    ∀ (bs : List Form) (h : ∀ A ∈ bs, □A ∈ Δ),
      (∀ A ∈ bs, (rec (xbox Γ ++ [□A] ⇒ [A])).isSome = true) →
      (tryBoxes Γ Δ rec bs h).isSome = true
  | [], _, _ => rfl
  | A :: bs, h, hrec => by
    have hA := hrec A (List.mem_cons_self ..)
    have ih := tryBoxes_isSome (Γ := Γ) (Δ := Δ) (rec := rec) bs
      (fun B hB => h B (List.mem_cons_of_mem _ hB))
      (fun B hB => hrec B (List.mem_cons_of_mem _ hB))
    unfold tryBoxes
    split
    · next hn => rw [hn] at hA; cases hA
    · rfl
    · split
      · next hn => rw [hn] at ih; cases ih
      · rfl
      · rfl

/-- With more steps than the measure of the sequent, the search answers. -/
theorem search_isSome (U : List Form) : ∀ (n : Nat) (s : Seq), Closed U s → weight U s < n →
    (search n s).isSome = true := by
  intro n
  induction n with
  | zero => intro s _ h; cases h
  | succ n ih =>
    intro s hU hw
    have hrec : ∀ p, PSPrem p s → (search n p).isSome = true := by
      intro p hp
      obtain ⟨hU', hlt⟩ := hp.step hU
      exact ih p hU' (by omega)
    unfold search
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
      have h1 := tryBoxes_isSome (Γ := s.ant) (Δ := s.suc) (rec := search n)
        (s.suc.filterMap Form.unbox?) (fun _ hA => mem_unboxes.1 hA)
        (fun A hA => hrec _ (.glr A nP nB nBot (mem_unboxes.1 hA) rfl))
      split
      · next hn => rw [hn] at h1; cases h1
      · rfl
      · rfl

/-- **The steps that are enough for a sequent.** -/
def fuel (s : Seq) : Nat := weight s.boxSubs s + 1

theorem search_fuel (s : Seq) : (search (fuel s) s).isSome = true :=
  search_isSome s.boxSubs _ s (closed_self s) (Nat.lt_succ_self _)

/-- For every sequent, a derivation in GLS or a tree at whose root it is
false, by the computed truth. -/
def proofOrRef (s : Seq) : Fam s ⊕ Ref s := (search (fuel s) s).get (search_fuel s)

/-- **Goal 2, completeness as data**: for every sequent, a derivation in
GLS or a refutation. -/
def proofOrRefutation : ProofOrRefutation := fun s =>
  match proofOrRef s with
  | .inl d => .inl d
  | .inr r => .inr ⟨r.1, not_satSeq_of_refutedAt r.2⟩

end GLS

#axioms_within_file [propext, Quot.sound]
