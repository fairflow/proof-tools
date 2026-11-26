/-
Soundness of the two-zone sequent calculus, with the two cuts, for the
intuitionistic phase semantics.

Source: KOT (Kanovich, Okada, Terui, *Intuitionistic phase semantics is
almost classical*, 2006), Theorem 2.9, the half "if `A` is provable then
`A` is satisfied in every model", with the facts on closed sets of their
Section 2 (Lemma 2.3: `X ⊸ Y` is closed when `Y` is).  The formula of a
two-zone sequent is taken apart first (`sat_iff_holds`): the sequent
`G₁, …, Gₙ ; D₁, …, Dₘ ⟹ C` is satisfied exactly when every product
`g₁ · … · gₙ · d₁ · … · dₘ`, with `gᵢ` in `⟦Gᵢ⟧ ∩ I` and `dⱼ` in `⟦Dⱼ⟧`,
is in `⟦C⟧`.  Theory file: it ends with its bound on axioms.
-/
import DILL.Statements

namespace DILL

open List

namespace Sem

/-! ## Phase spaces: the monoid, closed sets -/

section Space

variable {P : PhaseSpace}

theorem mul_one (p : P.M) : P.mul p P.one = p := by rw [P.mul_comm, P.one_mul]

theorem mul_left_comm (p q r : P.M) : P.mul p (P.mul q r) = P.mul q (P.mul p r) := by
  rw [← P.mul_assoc, P.mul_comm p q, P.mul_assoc]

/-- `(p · q) · (r · s) = (p · r) · (q · s)`. -/
theorem mul_mul_mul_comm (p q r s : P.M) :
    P.mul (P.mul p q) (P.mul r s) = P.mul (P.mul p r) (P.mul q s) := by
  rw [P.mul_assoc, P.mul_assoc, mul_left_comm q r s]

/-- A closure is closed: (Cl2). -/
theorem cl_closed (X : P.M → Prop) : P.IsClosed (P.Cl X) := P.cl_idem X

/-- A closed set that contains `X` contains its closure. -/
theorem cl_le {X Y : P.M → Prop} (hY : P.IsClosed Y) (h : ∀ p, X p → Y p) {p : P.M}
    (hp : P.Cl X p) : Y p :=
  hY p (P.cl_mono X Y h p hp)

/-- **Elimination of a closure under a product**, from (Cl4): to show
`p · r ∈ Y` for every `p` of `Cl X`, where `Y` is closed, it is enough to
show it for every `p` of `X`. -/
theorem cl_elim {X Y : P.M → Prop} (hY : P.IsClosed Y) (r : P.M)
    (h : ∀ p, X p → Y (P.mul p r)) {p : P.M} (hp : P.Cl X p) : Y (P.mul p r) := by
  have := P.cl_mul X (fun q => q = r) (P.mul p r) ⟨p, r, hp, P.cl_ext _ r rfl, rfl⟩
  refine cl_le hY ?_ this
  intro s ⟨x, y, hx, hy, e⟩
  have hy : y = r := hy
  subst hy
  subst e
  exact h x hx

/-- KOT Lemma 2.3 (2): `X ⊸ Y` is closed when `Y` is. -/
theorem closed_lolli {X Y : P.M → Prop} (hY : P.IsClosed Y) :
    P.IsClosed (fun z => ∀ x, X x → Y (P.mul x z)) := by
  intro z hz x hx
  rw [P.mul_comm]
  exact cl_elim hY x (fun p hp => by rw [P.mul_comm]; exact hp x hx) hz

/-- The intersection of two closed sets is closed. -/
theorem closed_inter {X Y : P.M → Prop} (hX : P.IsClosed X) (hY : P.IsClosed Y) :
    P.IsClosed (fun p => X p ∧ Y p) :=
  fun _ hp => ⟨cl_le hX (fun _ h => h.1) hp, cl_le hY (fun _ h => h.2) hp⟩

theorem unit_one : P.unit P.one := P.cl_ext _ _ rfl

/-- `1 · Y ⊆ Y` for a closed `Y`. -/
theorem unit_mul_closed {Y : P.M → Prop} (hY : P.IsClosed Y) {g p : P.M} (hg : P.unit g)
    (hp : Y p) : Y (P.mul g p) :=
  cl_elim hY p (fun q hq => by
    have hq : q = P.one := hq
    rw [hq, P.one_mul]; exact hp) hg

theorem unit_mul {g h : P.M} (hg : P.unit g) (hh : P.unit h) : P.unit (P.mul g h) :=
  unit_mul_closed (cl_closed _) hg hh

theorem idem_one : P.idem P.one := ⟨unit_one, P.one_mul _⟩

/-- A product of idempotents of `1` is one. -/
theorem idem_mul {g h : P.M} (hg : P.idem g) (hh : P.idem h) : P.idem (P.mul g h) :=
  ⟨unit_mul hg.1 hh.1, by rw [mul_mul_mul_comm, hg.2, hh.2]⟩

/-- An idempotent is shared between the two factors of a product. -/
theorem idem_split {g : P.M} (h : P.mul g g = g) (p q : P.M) :
    P.mul g (P.mul p q) = P.mul (P.mul g p) (P.mul g q) := by
  rw [mul_mul_mul_comm, h]

end Space

/-! ## Models: interpretations are closed; a sequent, taken apart -/

variable (S : PhaseModel)

/-- The interpretation of a formula is a closed set (KOT Definition 2.6
with Lemma 2.3). -/
theorem interp_closed : ∀ A : Form, S.IsClosed (S.interp A)
  | .atom a => S.val_closed a
  | .tensor _ _ => cl_closed _
  | .one => cl_closed _
  | .lolli _ B => closed_lolli (interp_closed B)
  | .wth A B => closed_inter (interp_closed A) (interp_closed B)
  | .top => fun _ _ => trivial
  | .plus _ _ => cl_closed _
  | .zero => cl_closed _
  | .bang _ => cl_closed _

/-- The products `d₁ · … · dₘ` with `dⱼ ∈ ⟦Dⱼ⟧`: the linear zone, before
closure. -/
def ctx : List Form → S.M → Prop
  | [] => fun p => p = S.one
  | A :: Δ => fun r => ∃ p q, S.interp A p ∧ ctx Δ q ∧ r = S.mul p q

/-- The products `g₁ · … · gₙ` with `gᵢ ∈ ⟦Gᵢ⟧ ∩ I`: the unrestricted
zone, before closure. -/
def ctxU : List Form → S.M → Prop
  | [] => fun p => p = S.one
  | A :: Γ => fun r => ∃ p q, (S.interp A p ∧ S.idem p) ∧ ctxU Γ q ∧ r = S.mul p q

theorem ctx_append : ∀ (Δ Δ' : List Form) (m : S.M),
    ctx S (Δ ++ Δ') m ↔ ∃ p q, ctx S Δ p ∧ ctx S Δ' q ∧ m = S.mul p q
  | [], Δ', m =>
    ⟨fun h => ⟨S.one, m, rfl, h, (S.one_mul m).symm⟩,
     fun ⟨p, q, hp, hq, e⟩ => by
      have hp : p = S.one := hp
      rw [e, hp, S.one_mul]; exact hq⟩
  | A :: Δ, Δ', m =>
    ⟨fun ⟨a, r, ha, hr, e⟩ =>
      let ⟨p, q, hp, hq, e'⟩ := (ctx_append Δ Δ' r).1 hr
      ⟨S.mul a p, q, ⟨a, p, ha, hp, rfl⟩, hq, by rw [e, e', S.mul_assoc]⟩,
     fun ⟨_, q, ⟨a, p, ha, hp, e₁⟩, hq, e⟩ =>
      ⟨a, S.mul p q, ha, (ctx_append Δ Δ' _).2 ⟨p, q, hp, hq, rfl⟩, by
        rw [e, e₁, S.mul_assoc]⟩⟩

/-- The products of a zone are those of a permutation of it. -/
theorem ctx_perm {Δ Δ' : List Form} (h : Δ ~ Δ') : ∀ m, ctx S Δ m → ctx S Δ' m := by
  induction h with
  | nil => exact fun _ h => h
  | cons a _ ih => exact fun _ ⟨p, q, hp, hq, e⟩ => ⟨p, q, hp, ih q hq, e⟩
  | swap a b l =>
    exact fun _ ⟨p, _, hp, ⟨q, r, hq, hr, e'⟩, e⟩ =>
      ⟨q, S.mul p r, hq, ⟨p, r, hp, hr, rfl⟩, by rw [e, e', mul_left_comm]⟩
  | trans _ _ ih₁ ih₂ => exact fun m h => ih₂ m (ih₁ m h)

/-- A product for the unrestricted zone is an idempotent of `1`. -/
theorem ctxU_idem : ∀ (Γ : List Form) (g : S.M), ctxU S Γ g → S.idem g
  | [], g, h => by
    have h : g = S.one := h
    rw [h]; exact idem_one
  | _ :: Γ, g, ⟨p, q, hp, hq, e⟩ => by
    rw [e]; exact idem_mul hp.2 (ctxU_idem Γ q hq)

/-- A product for the unrestricted zone absorbs a phase of each formula
of the zone: what the rule copy needs. -/
theorem ctxU_mem : ∀ (Γ : List Form) (A : Form) (g : S.M), A ∈ Γ → ctxU S Γ g →
    ∃ a, S.interp A a ∧ S.mul g a = g
  | B :: Γ, A, g, hA, ⟨p, q, hp, hq, e⟩ => by
    rcases List.mem_cons.1 hA with hA | hA
    · subst hA
      refine ⟨p, hp.1, ?_⟩
      rw [e, S.mul_comm, ← S.mul_assoc, hp.2.2]
    · obtain ⟨a, ha, e'⟩ := ctxU_mem Γ A q hA hq
      refine ⟨a, ha, ?_⟩
      rw [e, S.mul_assoc, e']

/-- **The sequent holds in the model**: every product of phases of its
hypotheses, those of the unrestricted zone idempotents of `1`, is in the
interpretation of its conclusion. -/
def Holds (j : Seq) : Prop :=
  ∀ g m, ctxU S j.unr g → ctx S j.lin m → S.interp j.goal (S.mul g m)

theorem tensorAll_of_ctx : ∀ (Δ : List Form) (m : S.M), ctx S Δ m → S.interp (tensorAll Δ) m
  | [], _, h => S.cl_ext _ _ h
  | _ :: Δ, _, ⟨p, q, hp, hq, e⟩ => S.cl_ext _ _ ⟨p, q, hp, tensorAll_of_ctx Δ q hq, e⟩

theorem tensorAll_le : ∀ (Δ : List Form) (m : S.M),
    S.interp (tensorAll Δ) m → S.Cl (ctx S Δ) m
  | [], _, h => h
  | A :: Δ, m, h => by
    have h : S.Cl (S.prod (S.interp A) (S.interp (tensorAll Δ))) m := h
    refine cl_le (cl_closed _) ?_ h
    intro _ ⟨p, q, hp, hq, e⟩
    rw [e]
    exact S.cl_mul (S.interp A) (ctx S Δ) _ ⟨p, q, S.cl_ext _ _ hp, tensorAll_le Δ q hq, rfl⟩

theorem tensorAll_bang_le : ∀ (Γ Δ : List Form) (x : S.M),
    S.interp (tensorAll (Γ.map Form.bang ++ Δ)) x → S.Cl (S.prod (ctxU S Γ) (ctx S Δ)) x
  | [], Δ, x, h =>
    cl_le (cl_closed _) (fun m hm => S.cl_ext _ _ ⟨S.one, m, rfl, hm, (S.one_mul m).symm⟩)
      (tensorAll_le S Δ x h)
  | G :: Γ, Δ, x, h => by
    have h : S.Cl (S.prod (S.Cl (fun p => S.interp G p ∧ S.idem p))
        (S.interp (tensorAll (Γ.map Form.bang ++ Δ)))) x := h
    refine cl_le (cl_closed _) ?_ h
    intro _ ⟨p, q, hp, hq, e⟩
    rw [e]
    have := S.cl_mul (fun p => S.interp G p ∧ S.idem p) (S.prod (ctxU S Γ) (ctx S Δ)) _
      ⟨p, q, hp, tensorAll_bang_le Γ Δ q hq, rfl⟩
    refine cl_le (cl_closed _) ?_ this
    intro _ ⟨a, _, ha, ⟨g, m, hg, hm, e₁⟩, e₂⟩
    rw [e₂, e₁, ← S.mul_assoc]
    exact S.cl_ext _ _ ⟨S.mul a g, m, ⟨a, g, ha, hg, rfl⟩, hm, rfl⟩

theorem tensorAll_bang_of : ∀ (Γ Δ : List Form) (g m : S.M), ctxU S Γ g → ctx S Δ m →
    S.interp (tensorAll (Γ.map Form.bang ++ Δ)) (S.mul g m)
  | [], Δ, g, m, hg, hm => by
    have hg : g = S.one := hg
    rw [hg, S.one_mul]; exact tensorAll_of_ctx S Δ m hm
  | G :: Γ, Δ, _, m, ⟨p, q, hp, hq, e⟩, hm => by
    rw [e, S.mul_assoc]
    exact S.cl_ext _ _ ⟨p, S.mul q m, S.cl_ext _ _ hp, tensorAll_bang_of Γ Δ q m hq hm, rfl⟩

/-- A sequent that holds is satisfied. -/
theorem sat_of_holds (j : Seq) (h : Holds S j) : S.Sat j := by
  intro x hx
  rw [mul_one]
  refine cl_le (interp_closed S j.goal) ?_ (tensorAll_bang_le S j.unr j.lin x hx)
  intro _ ⟨g, m, hg, hm, e⟩
  rw [e]; exact h g m hg hm

/-- A sequent that is satisfied holds. -/
theorem holds_of_sat (j : Seq) (h : S.Sat j) : Holds S j := by
  intro g m hg hm
  have := h _ (tensorAll_bang_of S j.unr j.lin g m hg hm)
  rwa [mul_one] at this

/-- **The formula of a sequent, taken apart.** -/
theorem sat_iff_holds (j : Seq) : S.Sat j ↔ Holds S j :=
  ⟨holds_of_sat S j, sat_of_holds S j⟩

/-! ## Soundness -/

/-- **Every rule keeps `Holds`**, the two cuts among them: by recursion
on the derivation, one case a rule. -/
theorem holds_of_fam : {Γ Ξ : List Form} → {C : Form} → Fam true (Γ ⨾ Ξ ⟹ C) →
    ∀ g m, ctxU S Γ g → ctx S Ξ m → S.interp C (S.mul g m)
  | _, _, _, .init A h, g, m, hg, hm => by
    obtain ⟨p, q, hp, hq, e⟩ := ctx_perm S h m hm
    have hq : q = S.one := hq
    rw [e, hq, mul_one]
    exact unit_mul_closed (interp_closed S A) (ctxU_idem S _ g hg).1 hp
  | _, _, _, .copy A hΓ d, g, m, hg, hm => by
    obtain ⟨a, ha, e⟩ := ctxU_mem S _ A g hΓ hg
    have := holds_of_fam d g (S.mul a m) hg ⟨a, m, ha, hm, rfl⟩
    rwa [← S.mul_assoc, e] at this
  | _, _, C, .tensorL A B Δ h d, g, m, hg, hm => by
    obtain ⟨p, q, hp, hq, e⟩ := ctx_perm S h m hm
    rw [e, mul_left_comm]
    refine cl_elim (interp_closed S C) _ ?_ hp
    intro _ ⟨a, b, ha, hb, e'⟩
    have := holds_of_fam d g (S.mul a (S.mul b q)) hg ⟨a, _, ha, ⟨b, q, hb, hq, rfl⟩, rfl⟩
    rw [e', S.mul_assoc, mul_left_comm b g q, mul_left_comm a g]
    exact this
  | _, _, _, .tensorR Δ Δ' h d₁ d₂, g, m, hg, hm => by
    obtain ⟨p, q, hp, hq, e⟩ := (ctx_append S Δ Δ' m).1 (ctx_perm S h m hm)
    rw [e, idem_split (ctxU_idem S _ g hg).2]
    exact S.cl_ext _ _ ⟨_, _, holds_of_fam d₁ g p hg hp, holds_of_fam d₂ g q hg hq, rfl⟩
  | _, _, C, .oneL Δ h d, g, m, hg, hm => by
    obtain ⟨p, q, hp, hq, e⟩ := ctx_perm S h m hm
    rw [e, mul_left_comm]
    refine cl_elim (interp_closed S C) _ ?_ hp
    intro x hx
    have hx : x = S.one := hx
    rw [hx, S.one_mul]; exact holds_of_fam d g q hg hq
  | _, _, _, .oneR h, g, m, hg, hm => by
    have hm : m = S.one := ctx_perm S h m hm
    rw [hm, mul_one]; exact (ctxU_idem S _ g hg).1
  | _, _, _, .lolliL A B Δ Δ' h d₁ d₂, g, m, hg, hm => by
    obtain ⟨f, r, hf, hr, e⟩ := ctx_perm S h m hm
    obtain ⟨p, q, hp, hq, e'⟩ := (ctx_append S Δ Δ' r).1 hr
    have hB : S.interp B (S.mul (S.mul g p) f) := hf _ (holds_of_fam d₁ g p hg hp)
    have := holds_of_fam d₂ g _ hg ⟨_, q, hB, hq, rfl⟩
    have e₂ : S.mul g (S.mul f (S.mul p q)) = S.mul g (S.mul (S.mul (S.mul g p) f) q) := by
      rw [S.mul_assoc (S.mul g p), S.mul_assoc g p, ← S.mul_assoc g g, (ctxU_idem S _ g hg).2,
        mul_left_comm p f q]
    rw [e, e', e₂]; exact this
  | _, _, _, .lolliR d, g, m, hg, hm => by
    intro x hx
    have := holds_of_fam d g (S.mul x m) hg ⟨x, m, hx, hm, rfl⟩
    rwa [mul_left_comm] at this
  | _, _, _, .withL₁ A B Δ h d, g, m, hg, hm => by
    obtain ⟨p, q, hp, hq, e⟩ := ctx_perm S h m hm
    rw [e]; exact holds_of_fam d g _ hg ⟨p, q, hp.1, hq, rfl⟩
  | _, _, _, .withL₂ A B Δ h d, g, m, hg, hm => by
    obtain ⟨p, q, hp, hq, e⟩ := ctx_perm S h m hm
    rw [e]; exact holds_of_fam d g _ hg ⟨p, q, hp.2, hq, rfl⟩
  | _, _, _, .withR d₁ d₂, g, m, hg, hm =>
    ⟨holds_of_fam d₁ g m hg hm, holds_of_fam d₂ g m hg hm⟩
  | _, _, _, .topR, _, _, _, _ => trivial
  | _, _, C, .zeroL Δ h, g, m, _, hm => by
    obtain ⟨p, q, hp, _, e⟩ := ctx_perm S h m hm
    rw [e, mul_left_comm]
    exact cl_elim (interp_closed S C) _ (fun _ hx => hx.elim) hp
  | _, _, C, .plusL A B Δ h d₁ d₂, g, m, hg, hm => by
    obtain ⟨p, q, hp, hq, e⟩ := ctx_perm S h m hm
    rw [e, mul_left_comm]
    refine cl_elim (interp_closed S C) _ ?_ hp
    intro x hx
    rw [mul_left_comm]
    rcases hx with hx | hx
    · exact holds_of_fam d₁ g _ hg ⟨x, q, hx, hq, rfl⟩
    · exact holds_of_fam d₂ g _ hg ⟨x, q, hx, hq, rfl⟩
  | _, _, _, .plusR₁ d, g, m, hg, hm => S.cl_ext _ _ (.inl (holds_of_fam d g m hg hm))
  | _, _, _, .plusR₂ d, g, m, hg, hm => S.cl_ext _ _ (.inr (holds_of_fam d g m hg hm))
  | _, _, C, .bangL A Δ h d, g, m, hg, hm => by
    obtain ⟨p, q, hp, hq, e⟩ := ctx_perm S h m hm
    rw [e, mul_left_comm]
    refine cl_elim (interp_closed S C) _ ?_ hp
    intro x hx
    rw [← S.mul_assoc]
    exact holds_of_fam d (S.mul x g) q ⟨x, g, hx, hg, rfl⟩ hq
  | _, _, _, .bangR h d, g, m, hg, hm => by
    have hm : m = S.one := ctx_perm S h m hm
    have hA := holds_of_fam d g S.one hg rfl
    rw [hm]
    exact S.cl_ext _ _ ⟨hA, by rw [mul_one]; exact ctxU_idem S _ g hg⟩
  | _, _, _, .cut _ A Δ Δ' h d₁ d₂, g, m, hg, hm => by
    obtain ⟨p, q, hp, hq, e⟩ := (ctx_append S Δ Δ' m).1 (ctx_perm S h m hm)
    have := holds_of_fam d₂ g _ hg ⟨_, q, holds_of_fam d₁ g p hg hp, hq, rfl⟩
    rw [S.mul_assoc g p q, ← S.mul_assoc g g, (ctxU_idem S _ g hg).2] at this
    rw [e]; exact this
  | _, _, _, .cutU _ A d₁ d₂, g, m, hg, hm => by
    have hA := holds_of_fam d₁ g S.one hg rfl
    rw [mul_one] at hA
    have := holds_of_fam d₂ (S.mul g g) m ⟨g, g, ⟨hA, ctxU_idem S _ g hg⟩, hg, rfl⟩ hm
    rwa [(ctxU_idem S _ g hg).2] at this

end Sem

/-- **Soundness** (KOT Theorem 2.9, one half): a sequent with a
derivation, the two cuts allowed, is satisfied in every intuitionistic
phase model. -/
theorem soundness : Soundness := fun j ⟨d⟩ S =>
  match j, d with
  | ⟨_, _, _⟩, d => Sem.sat_of_holds S _ fun g m hg hm => Sem.holds_of_fam S d g m hg hm

end DILL

#axioms_within_file [propext, Quot.sound]
