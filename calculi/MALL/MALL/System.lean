/-
The linear sequent calculus for the multiplicatives and additives (MALL),
with cut and without: two inductive families, one constructor for each
rule.

Source: J.-Y. Girard, *Linear logic*, TCS 50 (1987), Definition 1.15,
p. 22.  Theory file: it ends with its bound on axioms.

How a rule of the source reads here (the divergences of representation
are in `campaign/rule-table.md`).  The source's sequents are sequences
`⊢ A₁, …, Aₙ`, with a rule of exchange.  Here a sequent is a list read as
a multiset: every rule concludes a sequent `Ξ` of which it asks only that
it be a permutation of the conclusion the figure writes.  This is the
source's own "variant without exchange, adapted to multisets of formulas"
(p. 24).  So the rule of exchange has no constructor: it is the function
`Fam.exch` below.  The figure as it stands, with its exchange rule, is the
family `Lit` of `MALL/Source.lean`, proved equivalent to this one.

The source's bold letters (lists of formulas) are `Γ`, `Δ` here; `Ξ` is
the whole conclusion, which the figure has no letter for.
-/
import MALL.Perm

namespace MALL

open List

/-- **The linear sequent calculus** (Girard, Definition 1.15, p. 22),
without the exponentials.  Into `Type`: a derivation is data. -/
inductive Fam : List Form → Type where
  /-- Logical axioms: `⊢ A, A⊥`. -/
  | ax {Ξ : List Form} (A : Form) (h : Ξ ~ [A, Aᗮ]) : Fam Ξ
  /-- Cut rule: from `⊢ A, Γ` and `⊢ A⊥, Δ` to `⊢ Γ, Δ`. -/
  | cut {Ξ : List Form} (A : Form) (Γ Δ : List Form) (h : Ξ ~ Γ ++ Δ)
      (d₁ : Fam (A :: Γ)) (d₂ : Fam (Aᗮ :: Δ)) : Fam Ξ
  /-- Additive rules, ⊤: `⊢ ⊤, Γ` "(axiom, Γ arbitrary) (no rule for 0)". -/
  | top {Ξ : List Form} (Γ : List Form) (h : Ξ ~ ⊤ :: Γ) : Fam Ξ
  /-- Additive rules, &: from `⊢ A, Γ` and `⊢ B, Γ` to `⊢ A & B, Γ`. -/
  | wth {Ξ : List Form} (A B : Form) (Γ : List Form) (h : Ξ ~ A & B :: Γ)
      (d₁ : Fam (A :: Γ)) (d₂ : Fam (B :: Γ)) : Fam Ξ
  /-- Additive rules, 1⊕: from `⊢ A, Γ` to `⊢ A ⊕ B, Γ`. -/
  | plus₁ {Ξ : List Form} (A B : Form) (Γ : List Form) (h : Ξ ~ A ⊕ B :: Γ)
      (d : Fam (A :: Γ)) : Fam Ξ
  /-- Additive rules, 2⊕: from `⊢ B, Γ` to `⊢ A ⊕ B, Γ`. -/
  | plus₂ {Ξ : List Form} (A B : Form) (Γ : List Form) (h : Ξ ~ A ⊕ B :: Γ)
      (d : Fam (B :: Γ)) : Fam Ξ
  /-- Multiplicative rules, 1: `⊢ 1` "(axiom)". -/
  | one {Ξ : List Form} (h : Ξ ~ [𝟏]) : Fam Ξ
  /-- Multiplicative rules, ⊥: from `⊢ Γ` to `⊢ ⊥, Γ`. -/
  | bot {Ξ : List Form} (Γ : List Form) (h : Ξ ~ ⊥ :: Γ) (d : Fam Γ) : Fam Ξ
  /-- Multiplicative rules, ⊗: from `⊢ A, Γ` and `⊢ B, Δ` to
  `⊢ A ⊗ B, Γ, Δ`. -/
  | tensor {Ξ : List Form} (A B : Form) (Γ Δ : List Form) (h : Ξ ~ A ⊗ B :: (Γ ++ Δ))
      (d₁ : Fam (A :: Γ)) (d₂ : Fam (B :: Δ)) : Fam Ξ
  /-- Multiplicative rules, ⅋: from `⊢ A, B, Γ` to `⊢ A ⅋ B, Γ`. -/
  | par {Ξ : List Form} (A B : Form) (Γ : List Form) (h : Ξ ~ A ⅋ B :: Γ)
      (d : Fam (A :: B :: Γ)) : Fam Ξ

/-- **The calculus without the cut rule**: the rules of `Fam` but cut. -/
inductive CF : List Form → Type where
  /-- Logical axioms. -/
  | ax {Ξ : List Form} (A : Form) (h : Ξ ~ [A, Aᗮ]) : CF Ξ
  /-- ⊤. -/
  | top {Ξ : List Form} (Γ : List Form) (h : Ξ ~ ⊤ :: Γ) : CF Ξ
  /-- &. -/
  | wth {Ξ : List Form} (A B : Form) (Γ : List Form) (h : Ξ ~ A & B :: Γ)
      (d₁ : CF (A :: Γ)) (d₂ : CF (B :: Γ)) : CF Ξ
  /-- 1⊕. -/
  | plus₁ {Ξ : List Form} (A B : Form) (Γ : List Form) (h : Ξ ~ A ⊕ B :: Γ)
      (d : CF (A :: Γ)) : CF Ξ
  /-- 2⊕. -/
  | plus₂ {Ξ : List Form} (A B : Form) (Γ : List Form) (h : Ξ ~ A ⊕ B :: Γ)
      (d : CF (B :: Γ)) : CF Ξ
  /-- 1. -/
  | one {Ξ : List Form} (h : Ξ ~ [𝟏]) : CF Ξ
  /-- ⊥. -/
  | bot {Ξ : List Form} (Γ : List Form) (h : Ξ ~ ⊥ :: Γ) (d : CF Γ) : CF Ξ
  /-- ⊗. -/
  | tensor {Ξ : List Form} (A B : Form) (Γ Δ : List Form) (h : Ξ ~ A ⊗ B :: (Γ ++ Δ))
      (d₁ : CF (A :: Γ)) (d₂ : CF (B :: Δ)) : CF Ξ
  /-- ⅋. -/
  | par {Ξ : List Form} (A B : Form) (Γ : List Form) (h : Ξ ~ A ⅋ B :: Γ)
      (d : CF (A :: B :: Γ)) : CF Ξ

/-- A control for `#slime`: no computed index. -/
inductive CleanControl : List Nat → Prop where
  | nil : CleanControl []
  | cons {n : Nat} {ns : List Nat} (h : CleanControl ns) : CleanControl (n :: ns)

/-- A control for `#slime`: a computed index in a conclusion. -/
inductive SlimedControl : List Nat → Prop where
  | nil : SlimedControl []
  | app {ms ns : List Nat} (h₁ : SlimedControl ms) (h₂ : SlimedControl ns) :
      SlimedControl (ms ++ ns)

#rules MALL.Fam
#rules MALL.CF
#slime MALL.CleanControl MALL.SlimedControl
#slime MALL.Fam
#slime MALL.CF

/-- There is a derivation, with cut allowed. -/
def Derivable (Γ : List Form) : Prop := Nonempty (Fam Γ)

/-! ## Exchange -/

/-- **Exchange** (the source's rule EXCH, p. 22: "where B is obtained by
permuting the formulas of A"): the same last rule, at the permuted
sequent, with the same premises. -/
def Fam.exch {Ξ Ξ' : List Form} (e : Ξ ~ Ξ') : Fam Ξ → Fam Ξ'
  | .ax A h => .ax A (e.symm.trans h)
  | .cut A Γ Δ h d₁ d₂ => .cut A Γ Δ (e.symm.trans h) d₁ d₂
  | .top Γ h => .top Γ (e.symm.trans h)
  | .wth A B Γ h d₁ d₂ => .wth A B Γ (e.symm.trans h) d₁ d₂
  | .plus₁ A B Γ h d => .plus₁ A B Γ (e.symm.trans h) d
  | .plus₂ A B Γ h d => .plus₂ A B Γ (e.symm.trans h) d
  | .one h => .one (e.symm.trans h)
  | .bot Γ h d => .bot Γ (e.symm.trans h) d
  | .tensor A B Γ Δ h d₁ d₂ => .tensor A B Γ Δ (e.symm.trans h) d₁ d₂
  | .par A B Γ h d => .par A B Γ (e.symm.trans h) d

/-- Exchange, without cut. -/
def CF.exch {Ξ Ξ' : List Form} (e : Ξ ~ Ξ') : CF Ξ → CF Ξ'
  | .ax A h => .ax A (e.symm.trans h)
  | .top Γ h => .top Γ (e.symm.trans h)
  | .wth A B Γ h d₁ d₂ => .wth A B Γ (e.symm.trans h) d₁ d₂
  | .plus₁ A B Γ h d => .plus₁ A B Γ (e.symm.trans h) d
  | .plus₂ A B Γ h d => .plus₂ A B Γ (e.symm.trans h) d
  | .one h => .one (e.symm.trans h)
  | .bot Γ h d => .bot Γ (e.symm.trans h) d
  | .tensor A B Γ Δ h d₁ d₂ => .tensor A B Γ Δ (e.symm.trans h) d₁ d₂
  | .par A B Γ h d => .par A B Γ (e.symm.trans h) d

/-- A derivation without cut is a derivation. -/
def CF.toFam : {Ξ : List Form} → CF Ξ → Fam Ξ
  | _, .ax A h => .ax A h
  | _, .top Γ h => .top Γ h
  | _, .wth A B Γ h d₁ d₂ => .wth A B Γ h d₁.toFam d₂.toFam
  | _, .plus₁ A B Γ h d => .plus₁ A B Γ h d.toFam
  | _, .plus₂ A B Γ h d => .plus₂ A B Γ h d.toFam
  | _, .one h => .one h
  | _, .bot Γ h d => .bot Γ h d.toFam
  | _, .tensor A B Γ Δ h d₁ d₂ => .tensor A B Γ Δ h d₁.toFam d₂.toFam
  | _, .par A B Γ h d => .par A B Γ h d.toFam

/-! ## Heights -/

/-- **The height of a derivation**: an instance of a rule with no premise
has height 1, and an instance with premises one more than the highest of
them. -/
def Fam.height : {Ξ : List Form} → Fam Ξ → Nat
  | _, .ax _ _ => 1
  | _, .cut _ _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | _, .top _ _ => 1
  | _, .wth _ _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | _, .plus₁ _ _ _ _ d => d.height + 1
  | _, .plus₂ _ _ _ _ d => d.height + 1
  | _, .one _ => 1
  | _, .bot _ _ d => d.height + 1
  | _, .tensor _ _ _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | _, .par _ _ _ _ d => d.height + 1

/-- The height of a derivation without cut. -/
def CF.height : {Ξ : List Form} → CF Ξ → Nat
  | _, .ax _ _ => 1
  | _, .top _ _ => 1
  | _, .wth _ _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | _, .plus₁ _ _ _ _ d => d.height + 1
  | _, .plus₂ _ _ _ _ d => d.height + 1
  | _, .one _ => 1
  | _, .bot _ _ d => d.height + 1
  | _, .tensor _ _ _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | _, .par _ _ _ _ d => d.height + 1

/-- Exchange keeps the height. -/
theorem Fam.height_exch {Ξ Ξ' : List Form} (e : Ξ ~ Ξ') (d : Fam Ξ) :
    (d.exch e).height = d.height := by
  cases d <;> rfl

/-- Exchange keeps the height, without cut. -/
theorem CF.height_exch {Ξ Ξ' : List Form} (e : Ξ ~ Ξ') (d : CF Ξ) :
    (d.exch e).height = d.height := by
  cases d <;> rfl

end MALL

#axioms_within_file [propext, Quot.sound]
