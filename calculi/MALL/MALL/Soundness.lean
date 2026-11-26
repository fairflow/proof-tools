/-
Soundness of the linear sequent calculus for the phase semantics.

Source: J.-Y. Girard, *Linear logic*, TCS 50 (1987), Proposition 1.16,
p. 23, with the properties of facts it uses (1.4, 1.5, 1.9.1).  Theory
file: it ends with its bound on axioms.
-/
import MALL.Statements

namespace MALL

open List

namespace PhaseSpace

variable {P : PhaseSpace}

theorem mul_left_comm (p q r : P.M) : P.mul p (P.mul q r) = P.mul q (P.mul p r) := by
  rw [← P.mul_assoc, P.mul_comm p q, P.mul_assoc]

/-- 1.4(ii): `G ⊂ H → H⊥ ⊂ G⊥`. -/
theorem dual_anti {G H : P.M → Prop} (h : ∀ p, G p → H p) {p : P.M} (hp : P.dual H p) :
    P.dual G p := fun q hq => hp q (h q hq)

/-- 1.4(i): `G ⊂ G⊥⊥`. -/
theorem le_dual_dual {G : P.M → Prop} {p : P.M} (h : G p) : P.dual (P.dual G) p :=
  fun q hq => by rw [P.mul_comm]; exact hq p h

/-- `G⊥⊥⊥ = G⊥`. -/
theorem dual3 {G : P.M → Prop} {p : P.M} : P.dual (P.dual (P.dual G)) p ↔ P.dual G p :=
  ⟨fun h q hq => h q (le_dual_dual hq), le_dual_dual⟩

theorem dual3_eq (G : P.M → Prop) : P.dual (P.dual (P.dual G)) = P.dual G :=
  funext fun _ => propext dual3

/-- 1.4(iii), one half: a dual is a fact. -/
theorem isFact_dual (G : P.M → Prop) : P.IsFact (P.dual G) := fun _ => dual3

theorem IsFact.dd_eq {G : P.M → Prop} (hG : P.IsFact G) : P.dual (P.dual G) = G :=
  funext fun p => propext (hG p)

/-- 1.5(i): `⊥` is a fact. -/
theorem isFact_bot : P.IsFact P.bot := fun p =>
  ⟨fun h => by
    have := h P.one (fun r hr => by rw [P.one_mul]; exact hr)
    rwa [P.mul_one] at this, le_dual_dual⟩

/-- 1.5(iii): `⊤ = P` is a fact. -/
theorem isFact_univ : P.IsFact (fun _ => True) := fun _ => ⟨fun _ => trivial, fun h => le_dual_dual (G := fun _ => True) h⟩

/-- 1.6, for two: the intersection of two facts is a fact. -/
theorem isFact_inter {G H : P.M → Prop} (hG : P.IsFact G) (hH : P.IsFact H) :
    P.IsFact (fun p => G p ∧ H p) := fun p =>
  ⟨fun h => ⟨(hG p).1 (dual_anti (fun _ hq => dual_anti (fun _ hx => hx.1) hq) h),
      (hH p).1 (dual_anti (fun _ hq => dual_anti (fun _ hx => hx.2) hq) h)⟩,
   fun h => le_dual_dual (G := fun p => G p ∧ H p) h⟩

/-- `(G ∪ H)⊥ = G⊥ ∩ H⊥`. -/
theorem dual_union (G H : P.M → Prop) :
    P.dual (fun p => G p ∨ H p) = fun p => P.dual G p ∧ P.dual H p :=
  funext fun _ => propext
    ⟨fun h => ⟨fun q hq => h q (.inl hq), fun q hq => h q (.inr hq)⟩,
     fun h q hq => hq.elim (h.1 q) (h.2 q)⟩

/-- `(G.H⊥⊥)⊥ = (G.H)⊥` (from Lemma 1.9.1). -/
theorem dual_prod_dd (G H : P.M → Prop) :
    P.dual (P.prod G (P.dual (P.dual H))) = P.dual (P.prod G H) :=
  funext fun p => propext
    ⟨dual_anti fun _ ⟨g, h, hg, hh, e⟩ => ⟨g, h, hg, le_dual_dual hh, e⟩,
     fun hp q ⟨g, y, hg, hy, e⟩ => by
      subst e
      have h1 : P.dual H (P.mul p g) := fun h hh => by
        rw [P.mul_assoc]; exact hp _ ⟨g, h, hg, hh, rfl⟩
      have := hy _ h1
      rwa [P.mul_comm, P.mul_assoc] at this⟩

/-- `G.{1} = G`. -/
theorem prod_one (G : P.M → Prop) : P.prod G (fun q => q = P.one) = G :=
  funext fun r => propext
    ⟨fun ⟨p, q, hp, hq, e⟩ => by subst hq; rw [P.mul_one] at e; exact e ▸ hp,
     fun h => ⟨r, P.one, h, rfl, (P.mul_one r).symm⟩⟩

end PhaseSpace

namespace PhaseStructure

open PhaseSpace

variable (S : PhaseStructure)

/-- The interpretation of a proposition is a fact (Definition 1.14(ii)). -/
theorem interp_fact : ∀ A : Form, S.IsFact (S.interp A)
  | .atom a => S.val_fact a
  | .natom _ => isFact_dual _
  | .one => isFact_dual _
  | .bot => isFact_bot
  | .top => isFact_univ
  | .zero => isFact_dual _
  | .tensor _ _ => isFact_dual _
  | .par _ _ => isFact_dual _
  | .wth A B => isFact_inter (interp_fact A) (interp_fact B)
  | .plus _ _ => isFact_dual _

/-- The interpretation of `A⊥` is the dual of that of `A` (1.7). -/
theorem interp_neg : ∀ A : Form, S.interp Aᗮ = S.dual (S.interp A)
  | .atom _ => rfl
  | .natom a => (IsFact.dd_eq (S.val_fact a)).symm
  | .one => (IsFact.dd_eq isFact_bot).symm
  | .bot => rfl
  | .top => rfl
  | .zero => (IsFact.dd_eq isFact_univ).symm
  | .tensor A B => by
    show S.dual (S.prod (S.dual (S.interp Aᗮ)) (S.dual (S.interp Bᗮ))) = _
    rw [interp_neg A, interp_neg B, IsFact.dd_eq (S.interp_fact A),
      IsFact.dd_eq (S.interp_fact B)]
    exact (dual3_eq _).symm
  | .par A B => by
    show S.dual (S.dual (S.prod (S.interp Aᗮ) (S.interp Bᗮ))) = _
    rw [interp_neg A, interp_neg B]
    rfl
  | .wth A B => by
    show S.dual (S.dual (fun p => S.interp Aᗮ p ∨ S.interp Bᗮ p)) = _
    rw [interp_neg A, interp_neg B, dual_union, IsFact.dd_eq (S.interp_fact A),
      IsFact.dd_eq (S.interp_fact B)]
    rfl
  | .plus A B => by
    show (fun p => S.interp Aᗮ p ∧ S.interp Bᗮ p) = _
    rw [interp_neg A, interp_neg B, ← dual_union]
    exact (dual3_eq _).symm

/-- **The phases of a context**: the product of the duals of its
formulas, `A₁⊥. … .Aₙ⊥`. -/
def ctx : List Form → S.M → Prop
  | [] => fun q => q = S.one
  | A :: Γ => S.prod (S.dual (S.interp A)) (ctx Γ)

/-- The sequent holds in the structure: every phase of its context is an
antiphase. -/
def Holds (Γ : List Form) : Prop := ∀ q, S.ctx Γ q → S.bot q

/-- The par of the formulas of a sequent is the dual of its context. -/
theorem interp_parAll : ∀ Γ : List Form, S.interp (parAll Γ) = S.dual (S.ctx Γ)
  | [] => funext fun p => propext
      ⟨fun h q hq => by subst hq; rw [S.mul_one]; exact h,
       fun h => by have := h S.one rfl; rwa [S.mul_one] at this⟩
  | [A] => by
    show S.interp A = S.dual (S.prod (S.dual (S.interp A)) (fun q => q = S.one))
    rw [prod_one, IsFact.dd_eq (S.interp_fact A)]
  | A :: B :: Γ => by
    show S.dual (S.prod (S.dual (S.interp A)) (S.dual (S.interp (parAll (B :: Γ))))) = _
    rw [interp_parAll (B :: Γ), dual_prod_dd]
    rfl

/-- Validity in a structure, through the context. -/
theorem sat_iff_holds (Γ : List Form) : S.Sat Γ ↔ S.Holds Γ := by
  unfold Sat Holds
  rw [interp_parAll]
  constructor
  · intro h q hq; have := h q hq; rwa [S.one_mul] at this
  · intro h q hq; rw [S.one_mul]; exact h q hq

theorem ctx_perm {Γ Γ' : List Form} (h : Γ ~ Γ') : ∀ q, S.ctx Γ q → S.ctx Γ' q := by
  induction h with
  | nil => exact fun _ h => h
  | cons A _ ih => exact fun q ⟨a, g, ha, hg, e⟩ => ⟨a, g, ha, ih g hg, e⟩
  | swap A B Γ =>
    rintro q ⟨b, x, hb, ⟨a, g, ha, hg, rfl⟩, rfl⟩
    exact ⟨a, S.mul b g, ha, ⟨b, g, hb, hg, rfl⟩, mul_left_comm ..⟩
  | trans _ _ ih₁ ih₂ => exact fun q h => ih₂ q (ih₁ q h)

theorem holds_perm {Γ Γ' : List Form} (h : Γ ~ Γ') (hΓ : S.Holds Γ) : S.Holds Γ' :=
  fun q hq => hΓ q (S.ctx_perm h.symm q hq)

theorem ctx_append (Γ Δ : List Form) (q : S.M) :
    S.ctx (Γ ++ Δ) q ↔ ∃ g d, S.ctx Γ g ∧ S.ctx Δ d ∧ q = S.mul g d := by
  induction Γ generalizing q with
  | nil =>
    constructor
    · intro h; exact ⟨S.one, q, rfl, h, (S.one_mul q).symm⟩
    · rintro ⟨g, d, rfl, hd, rfl⟩; rw [S.one_mul]; exact hd
  | cons A Γ ih =>
    constructor
    · rintro ⟨a, x, ha, hx, rfl⟩
      obtain ⟨g, d, hg, hd, rfl⟩ := (ih x).1 hx
      exact ⟨S.mul a g, d, ⟨a, g, ha, hg, rfl⟩, hd, (S.mul_assoc ..).symm⟩
    · rintro ⟨_, d, ⟨a, g, ha, hg, rfl⟩, hd, rfl⟩
      exact ⟨a, S.mul g d, ha, (ih _).2 ⟨g, d, hg, hd, rfl⟩, S.mul_assoc ..⟩

/-- A sequent `⊢ A, Γ` holds exactly if every phase of the context `Γ` is
a phase of `A`. -/
theorem holds_cons (A : Form) (Γ : List Form) :
    S.Holds (A :: Γ) ↔ ∀ g, S.ctx Γ g → S.interp A g := by
  constructor
  · intro h g hg
    refine (S.interp_fact A g).1 fun a ha => ?_
    rw [S.mul_comm]
    exact h _ ⟨a, g, ha, hg, rfl⟩
  · rintro h q ⟨a, g, ha, hg, rfl⟩
    exact ha g (h g hg)

/-- Every derivable sequent holds in every phase structure: by induction
on the derivation, a case for each rule (the proof of 1.16, (i)-(x)). -/
theorem holds_of_fam {Ξ : List Form} (d : Fam Ξ) : S.Holds Ξ := by
  induction d with
  | ax A h =>
    refine S.holds_perm h.symm ((S.holds_cons ..).2 ?_)
    rintro g ⟨a, x, ha, rfl, rfl⟩
    rw [S.mul_one]
    rw [interp_neg] at ha
    exact (S.interp_fact A a).1 ha
  | cut A Γ Δ h _ _ ih₁ ih₂ =>
    refine S.holds_perm h.symm fun q hq => ?_
    obtain ⟨g, d, hg, hd, rfl⟩ := (S.ctx_append ..).1 hq
    have h₁ := (S.holds_cons ..).1 ih₁ g hg
    have h₂ := (S.holds_cons ..).1 ih₂ d hd
    rw [interp_neg] at h₂
    rw [S.mul_comm]
    exact h₂ g h₁
  | top Γ h => exact S.holds_perm h.symm ((S.holds_cons ..).2 fun _ _ => trivial)
  | wth A B Γ h _ _ ih₁ ih₂ =>
    exact S.holds_perm h.symm ((S.holds_cons ..).2 fun g hg =>
      ⟨(S.holds_cons ..).1 ih₁ g hg, (S.holds_cons ..).1 ih₂ g hg⟩)
  | plus₁ A B Γ h _ ih =>
    exact S.holds_perm h.symm ((S.holds_cons ..).2 fun g hg =>
      le_dual_dual (.inl ((S.holds_cons ..).1 ih g hg)))
  | plus₂ A B Γ h _ ih =>
    exact S.holds_perm h.symm ((S.holds_cons ..).2 fun g hg =>
      le_dual_dual (.inr ((S.holds_cons ..).1 ih g hg)))
  | one h =>
    refine S.holds_perm h.symm ((S.holds_cons ..).2 ?_)
    rintro g rfl r hr
    rw [S.one_mul]; exact hr
  | bot Γ h _ ih => exact S.holds_perm h.symm ((S.holds_cons ..).2 fun g hg => ih g hg)
  | tensor A B Γ Δ h _ _ ih₁ ih₂ =>
    refine S.holds_perm h.symm ((S.holds_cons ..).2 fun x hx => ?_)
    obtain ⟨g, d, hg, hd, rfl⟩ := (S.ctx_append ..).1 hx
    exact le_dual_dual ⟨g, d, (S.holds_cons ..).1 ih₁ g hg, (S.holds_cons ..).1 ih₂ d hd, rfl⟩
  | par A B Γ h _ ih =>
    refine S.holds_perm h.symm ((S.holds_cons ..).2 fun g hg => ?_)
    rintro q ⟨a, b, ha, hb, rfl⟩
    have := ha _ ((S.holds_cons ..).1 ih (S.mul b g) ⟨b, g, hb, hg, rfl⟩)
    rw [S.mul_comm g, S.mul_assoc]
    exact this

/-- Validity in a structure does not depend on the order of the sequent
(the par of its formulas does). -/
theorem sat_perm {Γ Γ' : List Form} (h : Γ ~ Γ') : S.Sat Γ ↔ S.Sat Γ' := by
  rw [sat_iff_holds, sat_iff_holds]
  exact ⟨S.holds_perm h, S.holds_perm h.symm⟩

end PhaseStructure

/-- Validity does not depend on the order of the sequent. -/
theorem valid_perm {Γ Γ' : List Form} (h : Γ ~ Γ') : Valid Γ ↔ Valid Γ' :=
  ⟨fun hv S => (S.sat_perm h).1 (hv S), fun hv S => (S.sat_perm h).2 (hv S)⟩

/-- **Soundness** (Girard, Proposition 1.16). -/
theorem soundness : Soundness := fun _ ⟨d⟩ S => (S.sat_iff_holds _).2 (S.holds_of_fam d)

end MALL

#axioms_within_file [propext, Quot.sound]
