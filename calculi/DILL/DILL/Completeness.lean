/-
Completeness of the two-zone sequent calculus for the intuitionistic
phase semantics, for derivations without cut; and with soundness, cut
elimination as a proposition.

Source: KOT (Kanovich, Okada, Terui, 2006), the proof of Theorem 2.9 with
Remark 2.11 (after Okada): the canonical model, whose closed sets are the
intersections of the sets `⟦Γ′ ; Δ′ ⟹ C⟧` of contexts that derive `C`
without cut when put beside `Γ′ ; Δ′` (Theorem 2.8: a family of sets
closed under `{y} ⊸ –` induces a closure operator), and Lemma 2.10, by
induction on the formula.  The model is built here on the two-zone
calculus itself: a phase is a pair of an unrestricted zone, up to having
the same members, and a linear zone, up to permutation.  Theory file: it
ends with its bound on axioms.
-/
import DILL.Soundness

namespace DILL

open List

namespace Sem

/-! ## The monoid of contexts -/

/-- A context: an unrestricted zone and a linear zone. -/
abbrev Ph : Type := List Form × List Form

/-- Two contexts are the same phase: the unrestricted zones have the same
members, the linear zones are permutations of each other. -/
def Ph.r (a b : Ph) : Prop := (∀ B, B ∈ a.1 ↔ B ∈ b.1) ∧ a.2 ~ b.2

theorem Ph.r_equiv : Equivalence Ph.r :=
  ⟨fun _ => ⟨fun _ => Iff.rfl, Perm.refl _⟩,
   fun h => ⟨fun B => (h.1 B).symm, h.2.symm⟩,
   fun h₁ h₂ => ⟨fun B => (h₁.1 B).trans (h₂.1 B), h₁.2.trans h₂.2⟩⟩

/-- The setoid of contexts. -/
def synSetoid : Setoid Ph := ⟨Ph.r, Ph.r_equiv⟩

/-- The phases of the canonical model. -/
def SynM : Type := Quotient synSetoid

/-- The phase of a context. -/
def cls (Γ Δ : List Form) : SynM := Quotient.mk synSetoid (Γ, Δ)

theorem cls_sound {Γ Γ' Δ Δ' : List Form} (hΓ : ∀ B, B ∈ Γ ↔ B ∈ Γ') (hΔ : Δ ~ Δ') :
    cls Γ Δ = cls Γ' Δ' :=
  @Quotient.sound _ synSetoid (Γ, Δ) (Γ', Δ') ⟨hΓ, hΔ⟩

theorem mem_append_congr {Γ₁ Γ₁' Γ₂ Γ₂' : List Form} (h₁ : ∀ B, B ∈ Γ₁ ↔ B ∈ Γ₁')
    (h₂ : ∀ B, B ∈ Γ₂ ↔ B ∈ Γ₂') (B : Form) : B ∈ Γ₁ ++ Γ₂ ↔ B ∈ Γ₁' ++ Γ₂' := by
  rw [List.mem_append, List.mem_append, h₁ B, h₂ B]

/-- The product: the two zones are put side by side. -/
def synMul : SynM → SynM → SynM :=
  Quotient.lift₂ (s₁ := synSetoid) (s₂ := synSetoid)
    (fun a b => cls (a.1 ++ b.1) (a.2 ++ b.2))
    (fun _ _ _ _ h₁ h₂ => cls_sound (mem_append_congr h₁.1 h₂.1) (Perm.append h₁.2 h₂.2))

theorem synMul_comm (p q : SynM) : synMul p q = synMul q p :=
  Quotient.inductionOn₂ p q fun _ _ =>
    cls_sound (fun B => by rw [List.mem_append, List.mem_append]; exact Or.comm)
      perm_append_comm

theorem synMul_assoc (p q r : SynM) : synMul (synMul p q) r = synMul p (synMul q r) :=
  Quotient.inductionOn₃ p q r fun a b c => by
    show cls ((a.1 ++ b.1) ++ c.1) ((a.2 ++ b.2) ++ c.2) =
      cls (a.1 ++ (b.1 ++ c.1)) (a.2 ++ (b.2 ++ c.2))
    rw [List.append_assoc, List.append_assoc]

/-! ## The sets of the family, and the closure -/

/-- **The set of a sequent** (KOT, proof of Theorem 2.9: `⟦Γ′ ⊢ C⟧`): the
contexts that, put beside the hypotheses of the sequent, derive its
conclusion without cut. -/
def inF (j : Seq) : SynM → Prop :=
  Quotient.lift (s := synSetoid)
    (fun a : Ph => Nonempty (CF (a.1 ++ j.unr ⨾ a.2 ++ j.lin ⟹ j.goal)))
    (fun _ _ h => propext
      ⟨fun ⟨d⟩ => ⟨(d.mono (fun B => (mem_append_congr h.1 (fun _ => Iff.rfl) B).1)).exch
          (Perm.append_right _ h.2)⟩,
       fun ⟨d⟩ => ⟨(d.mono (fun B => (mem_append_congr h.1 (fun _ => Iff.rfl) B).2)).exch
          (Perm.append_right _ h.2.symm)⟩⟩)

/-- At the sequent with no hypothesis, the set is that of the contexts
that derive the formula. -/
theorem inF_nil (B : Form) (Γ Δ : List Form) :
    inF ([] ⨾ [] ⟹ B) (cls Γ Δ) ↔ Nonempty (CF (Γ ⨾ Δ ⟹ B)) := by
  show Nonempty (CF (Γ ++ [] ⨾ Δ ++ [] ⟹ B)) ↔ _
  rw [List.append_nil, List.append_nil]

theorem inF_nil_of {B : Form} {X : SynM → Prop}
    (h : ∀ Γ Δ, X (cls Γ Δ) → Nonempty (CF (Γ ⨾ Δ ⟹ B))) :
    ∀ p, X p → inF ([] ⨾ [] ⟹ B) p :=
  Quotient.ind fun ⟨Γ, Δ⟩ hp => (inF_nil B Γ Δ).2 (h Γ Δ hp)

/-- The family is closed under `{y} ⊸ –` (KOT Theorem 2.8): the phases
whose product with a context is in the set of a sequent are the set of
the sequent with the context added. -/
theorem inF_mul (j : Seq) (Γ₀ Δ₀ : List Form) (p : SynM) :
    inF j (synMul p (cls Γ₀ Δ₀)) ↔ inF (Γ₀ ++ j.unr ⨾ Δ₀ ++ j.lin ⟹ j.goal) p :=
  Quotient.inductionOn p fun a => by
    show Nonempty (CF ((a.1 ++ Γ₀) ++ j.unr ⨾ (a.2 ++ Δ₀) ++ j.lin ⟹ j.goal)) ↔
      Nonempty (CF (a.1 ++ (Γ₀ ++ j.unr) ⨾ a.2 ++ (Δ₀ ++ j.lin) ⟹ j.goal))
    rw [List.append_assoc, List.append_assoc]

theorem inF_mul_ex (j : Seq) (q : SynM) : ∃ j', ∀ x, inF j (synMul x q) ↔ inF j' x :=
  Quotient.inductionOn q fun ⟨Γ₀, Δ₀⟩ => ⟨_, inF_mul j Γ₀ Δ₀⟩

/-- **The closure**: the intersection of the sets of the family that
contain the set. -/
def synCl (X : SynM → Prop) (p : SynM) : Prop := ∀ j : Seq, (∀ q, X q → inF j q) → inF j p

/-- (Cl4), from the closure of the family under `{y} ⊸ –`. -/
theorem synCl_mul (X Y : SynM → Prop) (r : SynM)
    (h : ∃ p q, synCl X p ∧ synCl Y q ∧ r = synMul p q) :
    synCl (fun r => ∃ p q, X p ∧ Y q ∧ r = synMul p q) r := by
  obtain ⟨p, q, hp, hq, e⟩ := h
  intro j hj
  rw [e]
  have step : ∀ y, Y y → inF j (synMul p y) := fun y hy => by
    obtain ⟨j', hj'⟩ := inF_mul_ex j y
    exact (hj' p).2 (hp j' fun x hx => (hj' x).1 (hj _ ⟨x, y, hx, hy, rfl⟩))
  obtain ⟨j', hj'⟩ := inF_mul_ex j p
  rw [synMul_comm]
  exact (hj' q).2 (hq j' fun y hy => (hj' y).1 (by rw [synMul_comm]; exact step y hy))

/-- **The canonical phase space.** -/
def synSpace : PhaseSpace where
  M := SynM
  mul := synMul
  one := cls [] []
  one_mul := Quotient.ind fun _ => rfl
  mul_comm := synMul_comm
  mul_assoc := synMul_assoc
  Cl := synCl
  cl_ext := fun _ p hp _ hj => hj p hp
  cl_idem := fun _ _ hp j hj => hp j (fun _ hq => hq j hj)
  cl_mono := fun _ _ h _ hp j hj => hp j (fun q hq => hj q (h q hq))
  cl_mul := synCl_mul

/-- **The canonical model**: an atom is given the set of the contexts
that derive it. -/
def synModel : PhaseModel where
  toPhaseSpace := synSpace
  val := fun a => inF ([] ⨾ [] ⟹ .atom a)
  val_closed := fun _ _ hp => hp _ (fun _ h => h)

/-! ## The main lemma -/

/-- A phase that is in every set of the family that contains the
interpretation of `A` is in that interpretation, which is closed. -/
theorem interp_of_all (A : Form) (p : SynM)
    (h : ∀ j : Seq, (∀ q, synModel.interp A q → inF j q) → inF j p) : synModel.interp A p :=
  interp_closed synModel A p h

/-- The context `B ; ·` is an idempotent of `1`: weakening of the
unrestricted zone, which is read through membership. -/
theorem idem_cls (B : Form) : synModel.idem (cls [B] []) :=
  ⟨fun _ hj' =>
    let ⟨d⟩ := hj' (cls [] []) rfl
    ⟨d.mono fun _ h => .tail _ h⟩,
   cls_sound (fun C =>
    ⟨fun h => by
      rcases List.mem_cons.1 h with h | h
      · rw [h]; exact .head _
      · exact h,
     fun h => .tail _ h⟩) (.refl _)⟩

/-- Where `· ; B` is in the interpretation of `B`, so is `B ; ·`: by
copy. -/
theorem interp_copy (B : Form) (h : synModel.interp B (cls [] [B])) :
    synModel.interp B (cls [B] []) :=
  interp_of_all B _ fun j' hj' =>
    let ⟨d⟩ := hj' _ h
    show Nonempty (CF (B :: j'.unr ⨾ j'.lin ⟹ j'.goal)) from
      ⟨.copy B (.head _) (d.mono fun _ h => .tail _ h)⟩

/-- An idempotent phase has an empty linear zone. -/
theorem lin_nil_of_idem {Γ Δ : List Form} (h : synMul (cls Γ Δ) (cls Γ Δ) = cls Γ Δ) :
    Δ = [] := by
  have hr : Ph.r (Γ ++ Γ, Δ ++ Δ) (Γ, Δ) := @Quotient.exact _ synSetoid _ _ h
  have hl := hr.2.length_eq
  rw [List.length_append] at hl
  cases Δ with
  | nil => rfl
  | cons a Δ =>
    rw [List.length_cons] at hl
    omega

/-- **The main lemma** (KOT Lemma 2.10; Okada): the context `· ; B` is in
the interpretation of `B`, and every context of that interpretation
derives `B` without cut.  By induction on the formula. -/
theorem okada : ∀ B : Form, synModel.interp B (cls [] [B]) ∧
    ∀ p, synModel.interp B p → inF ([] ⨾ [] ⟹ B) p
  | .atom a => ⟨⟨.init (.atom a) (.refl _)⟩, fun _ h => h⟩
  | .tensor A B => by
    obtain ⟨a₁, a₂⟩ := okada A
    obtain ⟨b₁, b₂⟩ := okada B
    refine ⟨fun j hj => ?_, fun p hp => hp _ ?_⟩
    · obtain ⟨d⟩ : Nonempty (CF (j.unr ⨾ A :: B :: j.lin ⟹ j.goal)) :=
        hj (cls [] [A, B]) ⟨cls [] [A], cls [] [B], a₁, b₁, rfl⟩
      exact ⟨.tensorL A B j.lin (.refl _) d⟩
    · intro _ ⟨x, y, hx, hy, e⟩
      rw [e]
      have hx := a₂ x hx
      have hy := b₂ y hy
      revert hx hy
      refine Quotient.inductionOn₂ x y ?_
      intro ⟨Γ₁, Δ₁⟩ ⟨Γ₂, Δ₂⟩ hx hy
      obtain ⟨d₁⟩ := (inF_nil A Γ₁ Δ₁).1 hx
      obtain ⟨d₂⟩ := (inF_nil B Γ₂ Δ₂).1 hy
      exact (inF_nil (A ⊗ B) (Γ₁ ++ Γ₂) (Δ₁ ++ Δ₂)).2
        ⟨.tensorR Δ₁ Δ₂ (.refl _) (d₁.mono fun _ h => List.mem_append_left _ h)
          (d₂.mono fun _ h => List.mem_append_right _ h)⟩
  | .one => by
    refine ⟨fun j hj => ?_, fun p hp => hp _ ?_⟩
    · obtain ⟨d⟩ : Nonempty (CF (j.unr ⨾ j.lin ⟹ j.goal)) := hj (cls [] []) rfl
      exact ⟨.oneL j.lin (.refl _) d⟩
    · intro q hq
      have hq : q = cls [] [] := hq
      rw [hq]
      exact (inF_nil 𝟏 [] []).2 ⟨.oneR (.refl _)⟩
  | .lolli A B => by
    obtain ⟨a₁, a₂⟩ := okada A
    obtain ⟨b₁, b₂⟩ := okada B
    refine ⟨fun x hx => interp_of_all B _ fun j hj => ?_, inF_nil_of fun Γ Δ hp => ?_⟩
    · obtain ⟨d₂⟩ : Nonempty (CF (j.unr ⨾ B :: j.lin ⟹ j.goal)) := hj _ b₁
      have hx := a₂ x hx
      revert hx
      refine Quotient.inductionOn x ?_
      intro ⟨Γ, Δ⟩ hx
      obtain ⟨d₁⟩ := (inF_nil A Γ Δ).1 hx
      show Nonempty (CF ((Γ ++ []) ++ j.unr ⨾ (Δ ++ [A ⊸ B]) ++ j.lin ⟹ j.goal))
      exact ⟨.lolliL A B Δ j.lin (by perm_count [])
        (d₁.mono fun _ h => List.mem_append_left _ (List.mem_append_left _ h))
        (d₂.mono fun _ h => List.mem_append_right _ h)⟩
    · have h : synModel.interp B (cls Γ (A :: Δ)) := hp (cls [] [A]) a₁
      obtain ⟨d⟩ := (inF_nil B Γ (A :: Δ)).1 (b₂ _ h)
      exact ⟨.lolliR d⟩
  | .wth A B => by
    obtain ⟨a₁, a₂⟩ := okada A
    obtain ⟨b₁, b₂⟩ := okada B
    refine ⟨⟨interp_of_all A _ fun j hj => ?_, interp_of_all B _ fun j hj => ?_⟩,
      inF_nil_of fun Γ Δ hp => ?_⟩
    · obtain ⟨d⟩ : Nonempty (CF (j.unr ⨾ A :: j.lin ⟹ j.goal)) := hj _ a₁
      exact ⟨.withL₁ A B j.lin (.refl _) d⟩
    · obtain ⟨d⟩ : Nonempty (CF (j.unr ⨾ B :: j.lin ⟹ j.goal)) := hj _ b₁
      exact ⟨.withL₂ A B j.lin (.refl _) d⟩
    · obtain ⟨d₁⟩ := (inF_nil A Γ Δ).1 (a₂ _ hp.1)
      obtain ⟨d₂⟩ := (inF_nil B Γ Δ).1 (b₂ _ hp.2)
      exact ⟨.withR d₁ d₂⟩
  | .top => ⟨trivial, inF_nil_of fun _ _ _ => ⟨.topR⟩⟩
  | .plus A B => by
    obtain ⟨a₁, a₂⟩ := okada A
    obtain ⟨b₁, b₂⟩ := okada B
    refine ⟨fun j hj => ?_, fun p hp => hp _ (inF_nil_of fun Γ Δ h => ?_)⟩
    · obtain ⟨d₁⟩ : Nonempty (CF (j.unr ⨾ A :: j.lin ⟹ j.goal)) := hj _ (.inl a₁)
      obtain ⟨d₂⟩ : Nonempty (CF (j.unr ⨾ B :: j.lin ⟹ j.goal)) := hj _ (.inr b₁)
      exact ⟨.plusL A B j.lin (.refl _) d₁ d₂⟩
    · rcases h with h | h
      · obtain ⟨d⟩ := (inF_nil A Γ Δ).1 (a₂ _ h)
        exact ⟨.plusR₁ d⟩
      · obtain ⟨d⟩ := (inF_nil B Γ Δ).1 (b₂ _ h)
        exact ⟨.plusR₂ d⟩
  | .zero => ⟨fun j _ => ⟨.zeroL j.lin (.refl _)⟩, fun _ hp => hp _ (fun _ h => h.elim)⟩
  | .bang B => by
    obtain ⟨b₁, b₂⟩ := okada B
    refine ⟨fun j hj => ?_, fun p hp => hp _ (inF_nil_of fun Γ Δ h => ?_)⟩
    · obtain ⟨d⟩ : Nonempty (CF (B :: j.unr ⨾ j.lin ⟹ j.goal)) :=
        hj (cls [B] []) ⟨interp_copy B b₁, idem_cls B⟩
      exact ⟨.bangL B j.lin (.refl _) d⟩
    · obtain ⟨hB, hI⟩ := h
      have hΔ : Δ = [] := lin_nil_of_idem hI.2
      subst hΔ
      obtain ⟨d⟩ := (inF_nil B Γ []).1 (b₂ _ hB)
      exact ⟨.bangR (.refl _) d⟩

/-! ## Completeness -/

/-- The context `Γ ; ·` is a product for the unrestricted zone `Γ`. -/
theorem ctxU_cls : ∀ Γ : List Form, ctxU synModel Γ (cls Γ [])
  | [] => rfl
  | G :: Γ => ⟨cls [G] [], cls Γ [], ⟨interp_copy G (okada G).1, idem_cls G⟩, ctxU_cls Γ, rfl⟩

/-- The context `· ; Δ` is a product for the linear zone `Δ`. -/
theorem ctx_cls : ∀ Δ : List Form, ctx synModel Δ (cls [] Δ)
  | [] => rfl
  | D :: Δ => ⟨cls [] [D], cls [] Δ, (okada D).1, ctx_cls Δ, rfl⟩

/-- **A sequent satisfied in the canonical model has a derivation without
cut.** -/
theorem cf_of_sat (Γ Δ : List Form) (C : Form) (h : synModel.Sat (Γ ⨾ Δ ⟹ C)) :
    Nonempty (CF (Γ ⨾ Δ ⟹ C)) := by
  have h₁ : synModel.interp C (cls (Γ ++ []) Δ) :=
    holds_of_sat synModel _ h (cls Γ []) (cls [] Δ) (ctxU_cls Γ) (ctx_cls Δ)
  rw [List.append_nil] at h₁
  exact (inF_nil C Γ Δ).1 ((okada C).2 _ h₁)

end Sem

/-- **Completeness, without cut** (KOT Theorem 2.9 with Remark 2.11): a
valid sequent has a derivation without cut. -/
theorem completeness : Completeness := fun j h =>
  match j, h with
  | ⟨Γ, Δ, C⟩, h => Sem.cf_of_sat Γ Δ C (h Sem.synModel)

/-- **Cut elimination, as a proposition**: by soundness and
completeness. -/
theorem cutEliminationProp : CutEliminationProp := fun j h => completeness j (soundness j h)

/-- Validity, derivability, and derivability without cut are the same. -/
theorem Sem.valid_iff_derivable (j : Seq) : Valid j ↔ Derivable j :=
  ⟨fun h => let ⟨d⟩ := completeness j h; ⟨d.lift⟩, soundness j⟩

theorem Sem.derivable_iff_cf (j : Seq) : Derivable j ↔ Nonempty (CF j) :=
  ⟨cutEliminationProp j, fun ⟨d⟩ => ⟨d.lift⟩⟩

end DILL

#axioms_within_file [propext, Quot.sound]
