/-
One-zone intuitionistic linear logic, with explicit rules for `!`: the
calculus that the two-zone sequents are read into.

Source: KOT (Kanovich, Okada, Terui 2006), Figure 1, p. 4, "Inference
Rules of Intuitionistic Linear Logic (ILL)", without the constant `⊥`
(so without `⊥l` and `⊥r`) and with exactly one formula on the right,
where the figure has at most one.  CCP's `ILL` (p. 19: the sequents of
its Figure 3 with one formula on the right, for the core connectives) has
the same rules for `!`, under the names !L, weak!, contr!, !R.  Theory
file: it ends with its bound on axioms.

A sequent `Γ ⊢ C` is `ILL c Γ C`, with `Γ` a list read as a multiset
("finite multisets of formulas", Definition 2.1): as in `DILL.Fam`, a
rule concludes a variable `Ξ` under a permutation hypothesis.  `ILL true`
has the rule Cut, `ILL false` has not.
-/
import DILL.System

namespace DILL

open List

/-- **Intuitionistic linear logic** (KOT Figure 1, p. 4), without `⊥`,
one formula on the right. -/
inductive ILL (c : Bool) : List Form → Form → Type where
  /-- Identity: `A ⊢ A`. -/
  | id {Ξ : List Form} (A : Form) (h : Ξ ~ [A]) : ILL c Ξ A
  /-- Cut: from `Γ₁ ⊢ A` and `A, Γ₂ ⊢ Δ` to `Γ₁, Γ₂ ⊢ Δ`.  Only where
  `c = true`. -/
  | cut {Ξ : List Form} {C : Form} (hc : c = true) (A : Form) (Γ₁ Γ₂ : List Form)
      (h : Ξ ~ Γ₁ ++ Γ₂) (d₁ : ILL c Γ₁ A) (d₂ : ILL c (A :: Γ₂) C) : ILL c Ξ C
  /-- ⊗l: from `A, B, Γ ⊢ Δ` to `A ⊗ B, Γ ⊢ Δ`. -/
  | tensorL {Ξ : List Form} {C : Form} (A B : Form) (Γ : List Form) (h : Ξ ~ A ⊗ B :: Γ)
      (d : ILL c (A :: B :: Γ) C) : ILL c Ξ C
  /-- ⊗r: from `Γ₁ ⊢ A` and `Γ₂ ⊢ B` to `Γ₁, Γ₂ ⊢ A ⊗ B`. -/
  | tensorR {Ξ : List Form} {A B : Form} (Γ₁ Γ₂ : List Form) (h : Ξ ~ Γ₁ ++ Γ₂)
      (d₁ : ILL c Γ₁ A) (d₂ : ILL c Γ₂ B) : ILL c Ξ (A ⊗ B)
  /-- 1l: from `Γ ⊢ Δ` to `1, Γ ⊢ Δ`. -/
  | oneL {Ξ : List Form} {C : Form} (Γ : List Form) (h : Ξ ~ 𝟏 :: Γ)
      (d : ILL c Γ C) : ILL c Ξ C
  /-- 1r: `⊢ 1`. -/
  | oneR {Ξ : List Form} (h : Ξ ~ []) : ILL c Ξ 𝟏
  /-- ⊸l: from `Γ₁ ⊢ A` and `B, Γ₂ ⊢ Δ` to `A ⊸ B, Γ₁, Γ₂ ⊢ Δ`. -/
  | lolliL {Ξ : List Form} {C : Form} (A B : Form) (Γ₁ Γ₂ : List Form)
      (h : Ξ ~ A ⊸ B :: (Γ₁ ++ Γ₂))
      (d₁ : ILL c Γ₁ A) (d₂ : ILL c (B :: Γ₂) C) : ILL c Ξ C
  /-- ⊸r: from `A, Γ ⊢ B` to `Γ ⊢ A ⊸ B`. -/
  | lolliR {Ξ : List Form} {A B : Form} (d : ILL c (A :: Ξ) B) : ILL c Ξ (A ⊸ B)
  /-- ⊕l: from `A, Γ ⊢ Δ` and `B, Γ ⊢ Δ` to `A ⊕ B, Γ ⊢ Δ`. -/
  | plusL {Ξ : List Form} {C : Form} (A B : Form) (Γ : List Form) (h : Ξ ~ (A ⊕ B) :: Γ)
      (d₁ : ILL c (A :: Γ) C) (d₂ : ILL c (B :: Γ) C) : ILL c Ξ C
  /-- ⊕r₁: from `Γ ⊢ A` to `Γ ⊢ A ⊕ B`. -/
  | plusR₁ {Ξ : List Form} {A B : Form} (d : ILL c Ξ A) : ILL c Ξ (A ⊕ B)
  /-- ⊕r₂: from `Γ ⊢ B` to `Γ ⊢ A ⊕ B`. -/
  | plusR₂ {Ξ : List Form} {A B : Form} (d : ILL c Ξ B) : ILL c Ξ (A ⊕ B)
  /-- 0l: `0, Γ ⊢ Δ`. -/
  | zeroL {Ξ : List Form} {C : Form} (Γ : List Form) (h : Ξ ~ 𝟎 :: Γ) : ILL c Ξ C
  /-- &l₁: from `A, Γ ⊢ Δ` to `A & B, Γ ⊢ Δ`. -/
  | withL₁ {Ξ : List Form} {C : Form} (A B : Form) (Γ : List Form) (h : Ξ ~ A & B :: Γ)
      (d : ILL c (A :: Γ) C) : ILL c Ξ C
  /-- &l₂: from `B, Γ ⊢ Δ` to `A & B, Γ ⊢ Δ`. -/
  | withL₂ {Ξ : List Form} {C : Form} (A B : Form) (Γ : List Form) (h : Ξ ~ A & B :: Γ)
      (d : ILL c (B :: Γ) C) : ILL c Ξ C
  /-- &r: from `Γ ⊢ A` and `Γ ⊢ B` to `Γ ⊢ A & B`. -/
  | withR {Ξ : List Form} {A B : Form} (d₁ : ILL c Ξ A) (d₂ : ILL c Ξ B) : ILL c Ξ (A & B)
  /-- ⊤r: `Γ ⊢ ⊤`. -/
  | topR {Ξ : List Form} : ILL c Ξ ⊤
  /-- !D: from `A, Γ ⊢ Δ` to `!A, Γ ⊢ Δ`. -/
  | bangD {Ξ : List Form} {C : Form} (A : Form) (Γ : List Form) (h : Ξ ~ (!A) :: Γ)
      (d : ILL c (A :: Γ) C) : ILL c Ξ C
  /-- !C: from `!A, !A, Γ ⊢ Δ` to `!A, Γ ⊢ Δ`. -/
  | bangC {Ξ : List Form} {C : Form} (A : Form) (Γ : List Form) (h : Ξ ~ (!A) :: Γ)
      (d : ILL c ((!A) :: (!A) :: Γ) C) : ILL c Ξ C
  /-- !W: from `Γ ⊢ Δ` to `!A, Γ ⊢ Δ`. -/
  | bangW {Ξ : List Form} {C : Form} (A : Form) (Γ : List Form) (h : Ξ ~ (!A) :: Γ)
      (d : ILL c Γ C) : ILL c Ξ C
  /-- !r: from `!Γ ⊢ A` to `!Γ ⊢ !A`, where "`!Γ` stands for a multisets
  of formulas of the form `!A₁, …, !Aₙ`". -/
  | bangR {Ξ : List Form} {A : Form} (Γ : List Form) (h : Ξ ~ Γ.map Form.bang)
      (d : ILL c (Γ.map Form.bang) A) : ILL c Ξ (!A)

#rules DILL.ILL
#slime DILL.ILL

/-- There is a derivation in ILL, with Cut allowed. -/
def ILLDerivable (Γ : List Form) (C : Form) : Prop := Nonempty (ILL true Γ C)

end DILL

#axioms_within_file [propext, Quot.sound]
