/-
The sequent calculus of dual intuitionistic linear logic, with the two
cuts and without: one inductive family with a Boolean parameter, one
constructor for each rule.

Source: CCP (Chang, Chaudhuri, Pfenning, CMU-CS-03-131R), Figure 2,
p. 12, the rules for a goal that is true and the connectives ⊗, 1, ⊸, &,
⊤, ⊕, 0, !; the cuts are Principle 7, items 1 and 2, p. 11.  Theory file:
it ends with its bound on axioms.

How a rule of the figure reads here (the divergences are in
`campaign/rule-table.md`).

* The linear zone `Δ` is a list read as a multiset.  A rule that takes
  something out of the linear zone of its conclusion concludes a variable
  zone `Ξ`, of which it asks only that it be a permutation (`~`) of the
  zone the figure writes.  So exchange has no constructor: it is the
  function `Fam.exch`.
* The unrestricted zone `Γ` is a list read through membership: copy asks
  `A ∈ Γ`, where the figure writes `Γ, A`; !L puts `A` at the head.
  Weakening, contraction and exchange of `Γ` have no constructor: they
  are the function `Fam.mono`.
* `Fam true` is the calculus with the two cuts, `Fam false` the calculus
  of the figure.

`Ξ` is the linear zone of a conclusion, which the figure has no one
letter for.
-/
import DILL.Perm

namespace DILL

open List

/-- **The sequent calculus** (CCP Figure 2, p. 12), with the cuts of
Principle 7 where `c = true`.  Into `Type`: a derivation is data. -/
inductive Fam (c : Bool) : Seq → Type where
  /-- init: `Γ ; A ⟹ A`. -/
  | init {Γ Ξ : List Form} (A : Form) (h : Ξ ~ [A]) : Fam c (Γ ⨾ Ξ ⟹ A)
  /-- copy: from `Γ, A ; Δ, A ⟹ γ` to `Γ, A ; Δ ⟹ γ`. -/
  | copy {Γ Ξ : List Form} {C : Form} (A : Form) (hΓ : A ∈ Γ)
      (d : Fam c (Γ ⨾ A :: Ξ ⟹ C)) : Fam c (Γ ⨾ Ξ ⟹ C)
  /-- ⊗L: from `Γ ; Δ, A, B ⟹ γ` to `Γ ; Δ, A ⊗ B ⟹ γ`. -/
  | tensorL {Γ Ξ : List Form} {C : Form} (A B : Form) (Δ : List Form) (h : Ξ ~ A ⊗ B :: Δ)
      (d : Fam c (Γ ⨾ A :: B :: Δ ⟹ C)) : Fam c (Γ ⨾ Ξ ⟹ C)
  /-- ⊗R: from `Γ ; Δ ⟹ A` and `Γ ; Δ′ ⟹ B` to `Γ ; Δ, Δ′ ⟹ A ⊗ B`. -/
  | tensorR {Γ Ξ : List Form} {A B : Form} (Δ Δ' : List Form) (h : Ξ ~ Δ ++ Δ')
      (d₁ : Fam c (Γ ⨾ Δ ⟹ A)) (d₂ : Fam c (Γ ⨾ Δ' ⟹ B)) : Fam c (Γ ⨾ Ξ ⟹ A ⊗ B)
  /-- 1L: from `Γ ; Δ ⟹ γ` to `Γ ; Δ, 1 ⟹ γ`. -/
  | oneL {Γ Ξ : List Form} {C : Form} (Δ : List Form) (h : Ξ ~ 𝟏 :: Δ)
      (d : Fam c (Γ ⨾ Δ ⟹ C)) : Fam c (Γ ⨾ Ξ ⟹ C)
  /-- 1R: `Γ ; · ⟹ 1`. -/
  | oneR {Γ Ξ : List Form} (h : Ξ ~ []) : Fam c (Γ ⨾ Ξ ⟹ 𝟏)
  /-- ⊸L: from `Γ ; Δ ⟹ A` and `Γ ; Δ′, B ⟹ γ` to
  `Γ ; Δ, Δ′, A ⊸ B ⟹ γ`. -/
  | lolliL {Γ Ξ : List Form} {C : Form} (A B : Form) (Δ Δ' : List Form)
      (h : Ξ ~ A ⊸ B :: (Δ ++ Δ'))
      (d₁ : Fam c (Γ ⨾ Δ ⟹ A)) (d₂ : Fam c (Γ ⨾ B :: Δ' ⟹ C)) : Fam c (Γ ⨾ Ξ ⟹ C)
  /-- ⊸R: from `Γ ; Δ, A ⟹ B` to `Γ ; Δ ⟹ A ⊸ B`. -/
  | lolliR {Γ Ξ : List Form} {A B : Form}
      (d : Fam c (Γ ⨾ A :: Ξ ⟹ B)) : Fam c (Γ ⨾ Ξ ⟹ A ⊸ B)
  /-- &L₁: from `Γ ; Δ, A ⟹ γ` to `Γ ; Δ, A & B ⟹ γ`. -/
  | withL₁ {Γ Ξ : List Form} {C : Form} (A B : Form) (Δ : List Form) (h : Ξ ~ A & B :: Δ)
      (d : Fam c (Γ ⨾ A :: Δ ⟹ C)) : Fam c (Γ ⨾ Ξ ⟹ C)
  /-- &L₂: from `Γ ; Δ, B ⟹ γ` to `Γ ; Δ, A & B ⟹ γ`. -/
  | withL₂ {Γ Ξ : List Form} {C : Form} (A B : Form) (Δ : List Form) (h : Ξ ~ A & B :: Δ)
      (d : Fam c (Γ ⨾ B :: Δ ⟹ C)) : Fam c (Γ ⨾ Ξ ⟹ C)
  /-- &R: from `Γ ; Δ ⟹ A` and `Γ ; Δ ⟹ B` to `Γ ; Δ ⟹ A & B`. -/
  | withR {Γ Ξ : List Form} {A B : Form}
      (d₁ : Fam c (Γ ⨾ Ξ ⟹ A)) (d₂ : Fam c (Γ ⨾ Ξ ⟹ B)) : Fam c (Γ ⨾ Ξ ⟹ A & B)
  /-- ⊤R: `Γ ; Δ ⟹ ⊤`. -/
  | topR {Γ Ξ : List Form} : Fam c (Γ ⨾ Ξ ⟹ ⊤)
  /-- 0L: `Γ ; Δ, 0 ⟹ γ`. -/
  | zeroL {Γ Ξ : List Form} {C : Form} (Δ : List Form) (h : Ξ ~ 𝟎 :: Δ) : Fam c (Γ ⨾ Ξ ⟹ C)
  /-- ⊕L: from `Γ ; Δ, A ⟹ γ` and `Γ ; Δ, B ⟹ γ` to `Γ ; Δ, A ⊕ B ⟹ γ`. -/
  | plusL {Γ Ξ : List Form} {C : Form} (A B : Form) (Δ : List Form) (h : Ξ ~ (A ⊕ B) :: Δ)
      (d₁ : Fam c (Γ ⨾ A :: Δ ⟹ C)) (d₂ : Fam c (Γ ⨾ B :: Δ ⟹ C)) : Fam c (Γ ⨾ Ξ ⟹ C)
  /-- ⊕R₁: from `Γ ; Δ ⟹ A` to `Γ ; Δ ⟹ A ⊕ B` (the figure prints the
  conclusion with `&`: a misprint, divergence W1). -/
  | plusR₁ {Γ Ξ : List Form} {A B : Form}
      (d : Fam c (Γ ⨾ Ξ ⟹ A)) : Fam c (Γ ⨾ Ξ ⟹ A ⊕ B)
  /-- ⊕R₂: from `Γ ; Δ ⟹ B` to `Γ ; Δ ⟹ A ⊕ B` (as ⊕R₁). -/
  | plusR₂ {Γ Ξ : List Form} {A B : Form}
      (d : Fam c (Γ ⨾ Ξ ⟹ B)) : Fam c (Γ ⨾ Ξ ⟹ A ⊕ B)
  /-- !L: from `Γ, A ; Δ ⟹ γ` to `Γ ; Δ, !A ⟹ γ`. -/
  | bangL {Γ Ξ : List Form} {C : Form} (A : Form) (Δ : List Form) (h : Ξ ~ (!A) :: Δ)
      (d : Fam c (A :: Γ ⨾ Δ ⟹ C)) : Fam c (Γ ⨾ Ξ ⟹ C)
  /-- !R: from `Γ ; · ⟹ A` to `Γ ; · ⟹ !A`. -/
  | bangR {Γ Ξ : List Form} {A : Form} (h : Ξ ~ [])
      (d : Fam c (Γ ⨾ [] ⟹ A)) : Fam c (Γ ⨾ Ξ ⟹ !A)
  /-- Cut on a linear hypothesis (Principle 7.2): from `Γ ; Δ ⟹ A` and
  `Γ ; Δ′, A ⟹ γ` to `Γ ; Δ, Δ′ ⟹ γ`.  Only where `c = true`. -/
  | cut {Γ Ξ : List Form} {C : Form} (hc : c = true) (A : Form) (Δ Δ' : List Form)
      (h : Ξ ~ Δ ++ Δ')
      (d₁ : Fam c (Γ ⨾ Δ ⟹ A)) (d₂ : Fam c (Γ ⨾ A :: Δ' ⟹ C)) : Fam c (Γ ⨾ Ξ ⟹ C)
  /-- Cut on a valid hypothesis (Principle 7.1; "cut!" in Pfenning's
  notes): from `Γ ; · ⟹ A` and `Γ, A ; Δ′ ⟹ γ` to `Γ ; Δ′ ⟹ γ`.  Only
  where `c = true`. -/
  | cutU {Γ Ξ : List Form} {C : Form} (hc : c = true) (A : Form)
      (d₁ : Fam c (Γ ⨾ [] ⟹ A)) (d₂ : Fam c (A :: Γ ⨾ Ξ ⟹ C)) : Fam c (Γ ⨾ Ξ ⟹ C)

/-- **The calculus without the cuts**: Figure 2 as it stands. -/
abbrev CF : Seq → Type := Fam false

/-- A control for `#slime`: no computed index. -/
inductive CleanControl : List Nat → Prop where
  | nil : CleanControl []
  | cons {n : Nat} {ns : List Nat} (h : CleanControl ns) : CleanControl (n :: ns)

/-- A control for `#slime`: a computed index in a conclusion. -/
inductive SlimedControl : List Nat → Prop where
  | nil : SlimedControl []
  | app {ms ns : List Nat} (h₁ : SlimedControl ms) (h₂ : SlimedControl ns) :
      SlimedControl (ms ++ ns)

#rules DILL.Fam
#slime DILL.CleanControl DILL.SlimedControl
#slime DILL.Fam

/-- There is a derivation, with the cuts allowed. -/
def Derivable (j : Seq) : Prop := Nonempty (Fam true j)

/-- There is a derivation without cut. -/
def CFDerivable (j : Seq) : Prop := Nonempty (CF j)

/-! ## Exchange in the linear zone -/

/-- **Exchange in the linear zone** (CCP p. 2: "allow free exchange among
the linear hypotheses"): the same rules, at the permuted zone. -/
def Fam.exch {c : Bool} : {Γ Ξ Ξ' : List Form} → {C : Form} → Ξ ~ Ξ' →
    Fam c (Γ ⨾ Ξ ⟹ C) → Fam c (Γ ⨾ Ξ' ⟹ C)
  | _, _, _, _, e, .init A h => .init A (e.symm.trans h)
  | _, _, _, _, e, .copy A hΓ d => .copy A hΓ (d.exch (e.cons A))
  | _, _, _, _, e, .tensorL A B Δ h d => .tensorL A B Δ (e.symm.trans h) d
  | _, _, _, _, e, .tensorR Δ Δ' h d₁ d₂ => .tensorR Δ Δ' (e.symm.trans h) d₁ d₂
  | _, _, _, _, e, .oneL Δ h d => .oneL Δ (e.symm.trans h) d
  | _, _, _, _, e, .oneR h => .oneR (e.symm.trans h)
  | _, _, _, _, e, .lolliL A B Δ Δ' h d₁ d₂ => .lolliL A B Δ Δ' (e.symm.trans h) d₁ d₂
  | _, _, _, _, e, .lolliR d => .lolliR (d.exch (e.cons _))
  | _, _, _, _, e, .withL₁ A B Δ h d => .withL₁ A B Δ (e.symm.trans h) d
  | _, _, _, _, e, .withL₂ A B Δ h d => .withL₂ A B Δ (e.symm.trans h) d
  | _, _, _, _, e, .withR d₁ d₂ => .withR (d₁.exch e) (d₂.exch e)
  | _, _, _, _, _, .topR => .topR
  | _, _, _, _, e, .zeroL Δ h => .zeroL Δ (e.symm.trans h)
  | _, _, _, _, e, .plusL A B Δ h d₁ d₂ => .plusL A B Δ (e.symm.trans h) d₁ d₂
  | _, _, _, _, e, .plusR₁ d => .plusR₁ (d.exch e)
  | _, _, _, _, e, .plusR₂ d => .plusR₂ (d.exch e)
  | _, _, _, _, e, .bangL A Δ h d => .bangL A Δ (e.symm.trans h) d
  | _, _, _, _, e, .bangR h d => .bangR (e.symm.trans h) d
  | _, _, _, _, e, .cut hc A Δ Δ' h d₁ d₂ => .cut hc A Δ Δ' (e.symm.trans h) d₁ d₂
  | _, _, _, _, e, .cutU hc A d₁ d₂ => .cutU hc A d₁ (d₂.exch e)

/-! ## The unrestricted zone: weakening, contraction, exchange -/

/-- Membership is kept under a new head on both sides. -/
theorem cons_sub {A : Form} {Γ Γ' : List Form} (s : ∀ B, B ∈ Γ → B ∈ Γ') :
    ∀ B, B ∈ A :: Γ → B ∈ A :: Γ' := by
  intro B hB
  cases hB with
  | head => exact .head _
  | tail _ h => exact .tail _ (s B h)

/-- **The unrestricted zone may grow, shrink to its members, and be
reordered**: a derivation at `Γ` is one at every `Γ'` that has the
members of `Γ`.  Weakening and contraction of the valid hypotheses (CCP
Theorem 2, p. 11) are instances. -/
def Fam.mono {c : Bool} : {Γ Γ' Ξ : List Form} → {C : Form} → (∀ B, B ∈ Γ → B ∈ Γ') →
    Fam c (Γ ⨾ Ξ ⟹ C) → Fam c (Γ' ⨾ Ξ ⟹ C)
  | _, _, _, _, _, .init A h => .init A h
  | _, _, _, _, s, .copy A hΓ d => .copy A (s A hΓ) (d.mono s)
  | _, _, _, _, s, .tensorL A B Δ h d => .tensorL A B Δ h (d.mono s)
  | _, _, _, _, s, .tensorR Δ Δ' h d₁ d₂ => .tensorR Δ Δ' h (d₁.mono s) (d₂.mono s)
  | _, _, _, _, s, .oneL Δ h d => .oneL Δ h (d.mono s)
  | _, _, _, _, _, .oneR h => .oneR h
  | _, _, _, _, s, .lolliL A B Δ Δ' h d₁ d₂ => .lolliL A B Δ Δ' h (d₁.mono s) (d₂.mono s)
  | _, _, _, _, s, .lolliR d => .lolliR (d.mono s)
  | _, _, _, _, s, .withL₁ A B Δ h d => .withL₁ A B Δ h (d.mono s)
  | _, _, _, _, s, .withL₂ A B Δ h d => .withL₂ A B Δ h (d.mono s)
  | _, _, _, _, s, .withR d₁ d₂ => .withR (d₁.mono s) (d₂.mono s)
  | _, _, _, _, _, .topR => .topR
  | _, _, _, _, _, .zeroL Δ h => .zeroL Δ h
  | _, _, _, _, s, .plusL A B Δ h d₁ d₂ => .plusL A B Δ h (d₁.mono s) (d₂.mono s)
  | _, _, _, _, s, .plusR₁ d => .plusR₁ (d.mono s)
  | _, _, _, _, s, .plusR₂ d => .plusR₂ (d.mono s)
  | _, _, _, _, s, .bangL A Δ h d => .bangL A Δ h (d.mono (cons_sub s))
  | _, _, _, _, s, .bangR h d => .bangR h (d.mono s)
  | _, _, _, _, s, .cut hc A Δ Δ' h d₁ d₂ => .cut hc A Δ Δ' h (d₁.mono s) (d₂.mono s)
  | _, _, _, _, s, .cutU hc A d₁ d₂ => .cutU hc A (d₁.mono s) (d₂.mono (cons_sub s))

/-- **Weakening of the unrestricted zone** (CCP Theorem 2.1). -/
def Fam.weakenU {c : Bool} {Γ Ξ : List Form} {C : Form} (A : Form)
    (d : Fam c (Γ ⨾ Ξ ⟹ C)) : Fam c (A :: Γ ⨾ Ξ ⟹ C) :=
  d.mono fun _ h => .tail _ h

/-- **Contraction of the unrestricted zone** (CCP Theorem 2.2). -/
def Fam.contractU {c : Bool} {Γ Ξ : List Form} {C : Form} {A : Form}
    (d : Fam c (A :: A :: Γ ⨾ Ξ ⟹ C)) : Fam c (A :: Γ ⨾ Ξ ⟹ C) :=
  d.mono fun B h => by
    cases h with
    | head => exact .head _
    | tail _ h => exact h

/-- A derivation without cut is a derivation of the calculus with cut. -/
def Fam.lift {c : Bool} : {j : Seq} → Fam false j → Fam c j
  | _, .init A h => .init A h
  | _, .copy A hΓ d => .copy A hΓ d.lift
  | _, .tensorL A B Δ h d => .tensorL A B Δ h d.lift
  | _, .tensorR Δ Δ' h d₁ d₂ => .tensorR Δ Δ' h d₁.lift d₂.lift
  | _, .oneL Δ h d => .oneL Δ h d.lift
  | _, .oneR h => .oneR h
  | _, .lolliL A B Δ Δ' h d₁ d₂ => .lolliL A B Δ Δ' h d₁.lift d₂.lift
  | _, .lolliR d => .lolliR d.lift
  | _, .withL₁ A B Δ h d => .withL₁ A B Δ h d.lift
  | _, .withL₂ A B Δ h d => .withL₂ A B Δ h d.lift
  | _, .withR d₁ d₂ => .withR d₁.lift d₂.lift
  | _, .topR => .topR
  | _, .zeroL Δ h => .zeroL Δ h
  | _, .plusL A B Δ h d₁ d₂ => .plusL A B Δ h d₁.lift d₂.lift
  | _, .plusR₁ d => .plusR₁ d.lift
  | _, .plusR₂ d => .plusR₂ d.lift
  | _, .bangL A Δ h d => .bangL A Δ h d.lift
  | _, .bangR h d => .bangR h d.lift

/-! ## Heights -/

/-- **The height of a derivation**: an instance of a rule with no premise
has height 1, and an instance with premises one more than the highest of
them. -/
def Fam.height {c : Bool} : {j : Seq} → Fam c j → Nat
  | _, .init _ _ => 1
  | _, .copy _ _ d => d.height + 1
  | _, .tensorL _ _ _ _ d => d.height + 1
  | _, .tensorR _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | _, .oneL _ _ d => d.height + 1
  | _, .oneR _ => 1
  | _, .lolliL _ _ _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | _, .lolliR d => d.height + 1
  | _, .withL₁ _ _ _ _ d => d.height + 1
  | _, .withL₂ _ _ _ _ d => d.height + 1
  | _, .withR d₁ d₂ => max d₁.height d₂.height + 1
  | _, .topR => 1
  | _, .zeroL _ _ => 1
  | _, .plusL _ _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | _, .plusR₁ d => d.height + 1
  | _, .plusR₂ d => d.height + 1
  | _, .bangL _ _ _ d => d.height + 1
  | _, .bangR _ d => d.height + 1
  | _, .cut _ _ _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | _, .cutU _ _ d₁ d₂ => max d₁.height d₂.height + 1

theorem Fam.height_exch_aux {c : Bool} {j : Seq} (d : Fam c j) :
    ∀ (Ξ' : List Form) (e : j.lin ~ Ξ'),
      (Fam.exch (Γ := j.unr) (C := j.goal) e d).height = d.height := by
  induction d with
  | _ => intros; simp_all [Fam.exch, Fam.height]

/-- Exchange in the linear zone keeps the height. -/
theorem Fam.height_exch {c : Bool} {Γ Ξ Ξ' : List Form} {C : Form} (e : Ξ ~ Ξ')
    (d : Fam c (Γ ⨾ Ξ ⟹ C)) : (d.exch e).height = d.height :=
  Fam.height_exch_aux d Ξ' e

theorem Fam.height_mono_aux {c : Bool} {j : Seq} (d : Fam c j) :
    ∀ (Γ' : List Form) (s : ∀ B, B ∈ j.unr → B ∈ Γ'),
      (Fam.mono (Ξ := j.lin) (C := j.goal) s d).height = d.height := by
  induction d with
  | _ => intros; simp_all [Fam.mono, Fam.height]

/-- The unrestricted zone is changed with the height kept. -/
theorem Fam.height_mono {c : Bool} {Γ Γ' Ξ : List Form} {C : Form}
    (s : ∀ B, B ∈ Γ → B ∈ Γ') (d : Fam c (Γ ⨾ Ξ ⟹ C)) : (d.mono s).height = d.height :=
  Fam.height_mono_aux d Γ' s

end DILL

#axioms_within_file [propext, Quot.sound]
