/-
Completeness of the linear sequent calculus for the phase semantics, for
derivations without cut; and with soundness, cut elimination as a
proposition.

Sources.  J.-Y. Girard, *Linear logic*, TCS 50 (1987), Theorem 1.17,
pp. 23-24: the phase space of multisets of formulas, whose antiphases are
the provable ones.  Y. Lafont, *The finite model property for various
fragments of linear logic*, J. Symbolic Logic 62 (1997), in the author's
version, p. 2: Lemma 1 ("Okada"), `A• ⊂ {A}⊥` in the syntactical model, by
induction on the formula and without the cut rule; and Theorem 1.

The lemma is proved once, for any phase space with an image of each
formula whose antiphases are closed under the rules (`RuleModel`), and the
syntactical model is built once, for any congruence on sequents and any
set of sequents closed under the rules (`Syn`): the finite model of
`MALL/FiniteModel.lean` is a second instance.  Theory file: it ends with
its bound on axioms.
-/
import MALL.Soundness

namespace MALL

open List PhaseSpace

/-- A phase space with a phase `e A` for each formula, whose antiphases
are closed under the rules of the calculus without cut (read on phases:
`e A . m` for the sequent `⊢ A, Γ`). -/
structure RuleModel where
  /-- The phase space. -/
  P : PhaseSpace
  /-- The phase of a formula. -/
  e : Form → P.M
  /-- The logical axiom, at a letter. -/
  ax : ∀ a : Nat, P.bot (P.mul (e (.atom a)) (e (.natom a)))
  /-- The rule 1. -/
  one : P.bot (e 𝟏)
  /-- The rule ⊥. -/
  bot : ∀ m, P.bot m → P.bot (P.mul (e ⊥) m)
  /-- The rule ⊤. -/
  top : ∀ m, P.bot (P.mul (e ⊤) m)
  /-- The rule ⅋. -/
  par : ∀ A B m, P.bot (P.mul (e A) (P.mul (e B) m)) → P.bot (P.mul (e (A ⅋ B)) m)
  /-- The rule ⊗. -/
  tensor : ∀ A B m n, P.bot (P.mul (e A) m) → P.bot (P.mul (e B) n) →
    P.bot (P.mul (e (A ⊗ B)) (P.mul m n))
  /-- The rule &. -/
  wth : ∀ A B m, P.bot (P.mul (e A) m) → P.bot (P.mul (e B) m) → P.bot (P.mul (e (A & B)) m)
  /-- The rule 1⊕. -/
  plus₁ : ∀ A B m, P.bot (P.mul (e A) m) → P.bot (P.mul (e (A ⊕ B)) m)
  /-- The rule 2⊕. -/
  plus₂ : ∀ A B m, P.bot (P.mul (e B) m) → P.bot (P.mul (e (A ⊕ B)) m)

namespace RuleModel

variable (R : RuleModel)

/-- The phase structure of a rule model: the fact of a letter `a` is
`{a}⊥` (Lafont, p. 2: "α• = {α}⊥"). -/
def str : PhaseStructure where
  toPhaseSpace := R.P
  val := fun a m => R.P.bot (R.P.mul (R.e (.atom a)) m)
  val_fact := fun a p =>
    ⟨fun h => by
      have := h (R.e (.atom a)) (fun r hr => hr)
      rwa [R.P.mul_comm] at this,
     fun h => le_dual_dual (G := fun m => R.P.bot (R.P.mul (R.e (.atom a)) m)) h⟩

/-- **Okada's lemma** (Lafont, Lemma 1): `A• ⊂ {A}⊥`.  By induction on the
formula; no cut. -/
theorem okada : ∀ (A : Form) (m : R.P.M), R.str.interp A m → R.P.bot (R.P.mul (R.e A) m)
  | .atom _, _, h => h
  | .natom a, m, h => by
    have : R.P.bot (R.P.mul m (R.e (.natom a))) := h (R.e (.natom a)) (R.ax a)
    rwa [R.P.mul_comm] at this
  | .one, m, h => by
    have : R.P.bot (R.P.mul m (R.e 𝟏)) := h (R.e 𝟏) R.one
    rwa [R.P.mul_comm] at this
  | .bot, m, h => R.bot m h
  | .top, m, _ => R.top m
  | .zero, m, h => by
    have : R.P.bot (R.P.mul m (R.e 𝟎)) := h (R.e 𝟎) trivial
    rwa [R.P.mul_comm] at this
  | .tensor A B, m, h => by
    have : R.P.bot (R.P.mul m (R.e (A ⊗ B))) := h (R.e (A ⊗ B)) (fun q ⟨x, y, hx, hy, e⟩ => by
      subst e; exact R.tensor A B x y (okada A x hx) (okada B y hy))
    rwa [R.P.mul_comm] at this
  | .par A B, m, h => by
    have : R.P.bot (R.P.mul m (R.P.mul (R.e A) (R.e B))) := h (R.P.mul (R.e A) (R.e B))
      ⟨R.e A, R.e B, fun x hx => okada A x hx, fun y hy => okada B y hy, rfl⟩
    rw [R.P.mul_comm, R.P.mul_assoc] at this
    exact R.par A B m this
  | .wth A B, m, h => R.wth A B m (okada A m h.1) (okada B m h.2)
  | .plus A B, m, h => by
    have : R.P.bot (R.P.mul m (R.e (A ⊕ B))) := h (R.e (A ⊕ B)) (fun q hq =>
      hq.elim (fun hA => R.plus₁ A B q (okada A q hA)) (fun hB => R.plus₂ A B q (okada B q hB)))
    rwa [R.P.mul_comm] at this

/-- The phase of a sequent: the product of the phases of its formulas. -/
def eAll : List Form → R.P.M
  | [] => R.P.one
  | A :: Γ => R.P.mul (R.e A) (eAll Γ)

theorem ctx_eAll : ∀ Γ : List Form, R.str.ctx Γ (R.eAll Γ)
  | [] => rfl
  | A :: Γ => ⟨R.e A, R.eAll Γ, fun x hx => R.okada A x hx, ctx_eAll Γ, rfl⟩

/-- A sequent that is valid in the structure of a rule model has its phase
among the antiphases. -/
theorem bot_of_sat (Γ : List Form) (h : R.str.Sat Γ) : R.P.bot (R.eAll Γ) :=
  (R.str.sat_iff_holds Γ).1 h _ (R.ctx_eAll Γ)

end RuleModel

/-- **The data of a syntactical model**: a congruence `r` on sequents that
contains the permutations, and a set `B` of sequents, closed under `r` and
under the rules of the calculus without cut. -/
structure Syn where
  /-- The congruence. -/
  r : List Form → List Form → Prop
  /-- It is an equivalence. -/
  equiv : Equivalence r
  /-- It contains the permutations. -/
  perm : ∀ {Γ Δ : List Form}, Γ ~ Δ → r Γ Δ
  /-- It is a congruence for juxtaposition. -/
  app : ∀ {Γ Γ' Δ Δ' : List Form}, r Γ Γ' → r Δ Δ' → r (Γ ++ Δ) (Γ' ++ Δ')
  /-- The sequents that are to be the antiphases. -/
  B : List Form → Prop
  /-- They are closed under the congruence. -/
  B_r : ∀ {Γ Δ : List Form}, r Γ Δ → B Γ → B Δ
  /-- The logical axiom, at a letter. -/
  ax : ∀ a : Nat, B [.atom a, .natom a]
  /-- The rule 1. -/
  one : B [𝟏]
  /-- The rule ⊥. -/
  bot : ∀ Γ, B Γ → B (⊥ :: Γ)
  /-- The rule ⊤. -/
  top : ∀ Γ, B (⊤ :: Γ)
  /-- The rule ⅋. -/
  par : ∀ A C Γ, B (A :: C :: Γ) → B (A ⅋ C :: Γ)
  /-- The rule ⊗. -/
  tensor : ∀ A C Γ Δ, B (A :: Γ) → B (C :: Δ) → B (A ⊗ C :: (Γ ++ Δ))
  /-- The rule &. -/
  wth : ∀ A C Γ, B (A :: Γ) → B (C :: Γ) → B (A & C :: Γ)
  /-- The rule 1⊕. -/
  plus₁ : ∀ A C Γ, B (A :: Γ) → B ((A ⊕ C) :: Γ)
  /-- The rule 2⊕. -/
  plus₂ : ∀ A C Γ, B (C :: Γ) → B ((A ⊕ C) :: Γ)

namespace Syn

variable (Y : Syn)

/-- The congruence, as a setoid. -/
def setoid : Setoid (List Form) := ⟨Y.r, Y.equiv⟩

/-- The phases: sequents up to the congruence. -/
def M : Type := Quotient Y.setoid

/-- The phase of a sequent. -/
def cls (Γ : List Form) : Y.M := Quotient.mk Y.setoid Γ

theorem sound {Γ Δ : List Form} (h : Y.r Γ Δ) : Y.cls Γ = Y.cls Δ :=
  @Quotient.sound _ Y.setoid Γ Δ h

/-- The product: juxtaposition. -/
def mul : Y.M → Y.M → Y.M :=
  Quotient.lift₂ (fun Γ Δ => Y.cls (Γ ++ Δ)) (fun _ _ _ _ h₁ h₂ => Y.sound (Y.app h₁ h₂))

/-- The antiphases. -/
def botM : Y.M → Prop :=
  Quotient.lift Y.B (fun _ _ h => propext ⟨Y.B_r h, Y.B_r (Y.equiv.symm h)⟩)

/-- **The syntactical phase space** (Girard, p. 24; Lafont, p. 2): the
monoid of sequents under juxtaposition, with the empty sequent as unit. -/
def space : PhaseSpace where
  M := Y.M
  mul := Y.mul
  one := Y.cls []
  one_mul := Quotient.ind fun _ => rfl
  mul_one := Quotient.ind fun Γ => congrArg Y.cls (List.append_nil Γ)
  mul_comm := fun p q => Quotient.inductionOn₂ p q fun _ _ => Y.sound (Y.perm perm_append_comm)
  mul_assoc := fun p q r =>
    Quotient.inductionOn₃ p q r fun Γ Δ Θ => congrArg Y.cls (List.append_assoc Γ Δ Θ)
  bot := Y.botM

/-- **The syntactical model**, as a rule model: the phase of a formula is
the sequent of that one formula. -/
def ruleModel : RuleModel where
  P := Y.space
  e := fun A => Y.cls [A]
  ax := Y.ax
  one := Y.one
  bot := Quotient.ind fun Γ h => Y.bot Γ h
  top := Quotient.ind fun Γ => Y.top Γ
  par := fun A C => Quotient.ind fun Γ h => Y.par A C Γ h
  tensor := fun A C m n => Quotient.inductionOn₂ m n fun Γ Δ h₁ h₂ => Y.tensor A C Γ Δ h₁ h₂
  wth := fun A C => Quotient.ind fun Γ h₁ h₂ => Y.wth A C Γ h₁ h₂
  plus₁ := fun A C => Quotient.ind fun Γ h => Y.plus₁ A C Γ h
  plus₂ := fun A C => Quotient.ind fun Γ h => Y.plus₂ A C Γ h

theorem eAll_eq : ∀ Γ : List Form, Y.ruleModel.eAll Γ = Y.cls Γ
  | [] => rfl
  | A :: Γ => by
    show Y.mul (Y.cls [A]) (Y.ruleModel.eAll Γ) = _
    rw [eAll_eq Γ]; rfl

/-- The syntactical phase structure. -/
def str : PhaseStructure := Y.ruleModel.str

/-- **A sequent valid in the syntactical structure is in `B`.** -/
theorem B_of_sat (Γ : List Form) (h : Y.str.Sat Γ) : Y.B Γ := by
  have := Y.ruleModel.bot_of_sat Γ h
  rw [Y.eAll_eq] at this
  exact this

end Syn

/-- **Girard's syntactical model, without cut**: sequents up to
permutation, the antiphases those with a derivation without cut. -/
def synCF : Syn where
  r := List.Perm
  equiv := ⟨Perm.refl, Perm.symm, Perm.trans⟩
  perm := id
  app := Perm.append
  B := fun Γ => Nonempty (CF Γ)
  B_r := fun h ⟨d⟩ => ⟨d.exch h⟩
  ax := fun a => ⟨.ax (.atom a) (.refl _)⟩
  one := ⟨.one (.refl _)⟩
  bot := fun Γ ⟨d⟩ => ⟨.bot Γ (.refl _) d⟩
  top := fun Γ => ⟨.top Γ (.refl _)⟩
  par := fun A C Γ ⟨d⟩ => ⟨.par A C Γ (.refl _) d⟩
  tensor := fun A C Γ Δ ⟨d₁⟩ ⟨d₂⟩ => ⟨.tensor A C Γ Δ (.refl _) d₁ d₂⟩
  wth := fun A C Γ ⟨d₁⟩ ⟨d₂⟩ => ⟨.wth A C Γ (.refl _) d₁ d₂⟩
  plus₁ := fun A C Γ ⟨d⟩ => ⟨.plus₁ A C Γ (.refl _) d⟩
  plus₂ := fun A C Γ ⟨d⟩ => ⟨.plus₂ A C Γ (.refl _) d⟩

/-- **Completeness** (Girard, Theorem 1.17; in the form of Lafont's Theorem
1, (2) ⟹ (4)): a valid sequent has a derivation without cut. -/
theorem completeness : Completeness := fun Γ h => synCF.B_of_sat Γ (h synCF.str)

/-- **Cut elimination, as a proposition** (Lafont, Theorem 1,
(1) ⟹ (4)): by soundness and completeness. -/
theorem cutEliminationProp : CutEliminationProp := fun Γ h => completeness Γ (soundness Γ h)

/-- Validity, derivability, and derivability without cut are the same
(Lafont, Theorem 1). -/
theorem valid_iff_derivable (Γ : List Form) : Valid Γ ↔ Derivable Γ :=
  ⟨fun h => let ⟨d⟩ := completeness Γ h; ⟨d.toFam⟩, soundness Γ⟩

theorem derivable_iff_cf (Γ : List Form) : Derivable Γ ↔ Nonempty (CF Γ) :=
  ⟨cutEliminationProp Γ, fun ⟨d⟩ => ⟨d.toFam⟩⟩

end MALL

#axioms_within_file [propext, Quot.sound]
