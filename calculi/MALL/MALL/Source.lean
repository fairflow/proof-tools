/-
The figure of the source as it stands, with its exchange rule, proved
equivalent to the family `Fam`; and derivations of what the source
asserts, as terms of `Fam`.

Source: J.-Y. Girard, *Linear logic*, TCS 50 (1987), Definition 1.15,
p. 22.  This file is a check of the transcription: it imports the theory
file only.  Theory file: it ends with its bound on axioms.
-/
import MALL.System

namespace MALL

open List

/-- **The figure, letter for letter** (Definition 1.15, p. 22): sequents
are sequences, every rule acts on the first formula, and exchange is a
rule.  Two conclusions of the figure are computed (`A⊥` in the axiom, the
juxtaposition `Γ, Δ` in cut and ⊗): each is a variable here, with an
equation.  (`(A ⊕ B) :: Γ` has its parentheses because core Lean's `⊕`,
for sum types, binds less tightly than `::`.) -/
inductive Lit : List Form → Type where
  /-- Logical axioms: `⊢ A, A⊥`. -/
  | ax (A B : Form) (h : B = Aᗮ) : Lit [A, B]
  /-- Cut rule: `⊢ A, Γ` and `⊢ A⊥, Δ` give `⊢ Γ, Δ`. -/
  | cut (A : Form) {Γ Δ Ξ : List Form} (d₁ : Lit (A :: Γ)) (d₂ : Lit (Aᗮ :: Δ))
      (h : Ξ = Γ ++ Δ) : Lit Ξ
  /-- Exchange rule: "where B is obtained by permuting the formulas of A". -/
  | exch {Γ Γ' : List Form} (d : Lit Γ) (h : Γ ~ Γ') : Lit Γ'
  /-- ⊤: `⊢ ⊤, Γ`. -/
  | top (Γ : List Form) : Lit (⊤ :: Γ)
  /-- &. -/
  | wth {A B : Form} {Γ : List Form} (d₁ : Lit (A :: Γ)) (d₂ : Lit (B :: Γ)) : Lit (A & B :: Γ)
  /-- 1⊕. -/
  | plus₁ {A : Form} (B : Form) {Γ : List Form} (d : Lit (A :: Γ)) : Lit ((A ⊕ B) :: Γ)
  /-- 2⊕. -/
  | plus₂ (A : Form) {B : Form} {Γ : List Form} (d : Lit (B :: Γ)) : Lit ((A ⊕ B) :: Γ)
  /-- 1: `⊢ 1`. -/
  | one : Lit [𝟏]
  /-- ⊥. -/
  | bot {Γ : List Form} (d : Lit Γ) : Lit (⊥ :: Γ)
  /-- ⊗: `⊢ A, Γ` and `⊢ B, Δ` give `⊢ A ⊗ B, Γ, Δ`. -/
  | tensor {A B : Form} {Γ Δ Ξ : List Form} (d₁ : Lit (A :: Γ)) (d₂ : Lit (B :: Δ))
      (h : Ξ = Γ ++ Δ) : Lit (A ⊗ B :: Ξ)
  /-- ⅋. -/
  | par {A B : Form} {Γ : List Form} (d : Lit (A :: B :: Γ)) : Lit (A ⅋ B :: Γ)

#rules MALL.Lit
#slime MALL.Lit

/-- A derivation of the figure is a derivation of `Fam`: each rule with
the trivial permutation, and exchange by `Fam.exch`. -/
def Lit.toFam : {Γ : List Form} → Lit Γ → Fam Γ
  | _, .ax A _ h => .ax A (by subst h; exact .refl _)
  | _, .cut A d₁ d₂ h => .cut A _ _ (by subst h; exact .refl _) d₁.toFam d₂.toFam
  | _, .exch d h => d.toFam.exch h
  | _, .top Γ => .top Γ (.refl _)
  | _, .wth d₁ d₂ => .wth _ _ _ (.refl _) d₁.toFam d₂.toFam
  | _, .plus₁ B d => .plus₁ _ B _ (.refl _) d.toFam
  | _, .plus₂ A d => .plus₂ A _ _ (.refl _) d.toFam
  | _, .one => .one (.refl _)
  | _, .bot d => .bot _ (.refl _) d.toFam
  | _, .tensor d₁ d₂ h => .tensor _ _ _ _ (by subst h; exact .refl _) d₁.toFam d₂.toFam
  | _, .par d => .par _ _ _ (.refl _) d.toFam

/-- A derivation of `Fam` is a derivation of the figure: each rule,
followed by one exchange. -/
def Fam.toLit : {Γ : List Form} → Fam Γ → Lit Γ
  | _, .ax A h => .exch (.ax A Aᗮ rfl) h.symm
  | _, .cut A _ _ h d₁ d₂ => .exch (.cut A d₁.toLit d₂.toLit rfl) h.symm
  | _, .top Γ h => .exch (.top Γ) h.symm
  | _, .wth _ _ _ h d₁ d₂ => .exch (.wth d₁.toLit d₂.toLit) h.symm
  | _, .plus₁ _ B _ h d => .exch (.plus₁ B d.toLit) h.symm
  | _, .plus₂ A _ _ h d => .exch (.plus₂ A d.toLit) h.symm
  | _, .one h => .exch .one h.symm
  | _, .bot _ h d => .exch (.bot d.toLit) h.symm
  | _, .tensor _ _ _ _ h d₁ d₂ => .exch (.tensor d₁.toLit d₂.toLit rfl) h.symm
  | _, .par _ _ _ h d => .exch (.par d.toLit) h.symm

/-- **The two families derive the same sequents.** -/
theorem lit_iff_fam (Γ : List Form) : Nonempty (Lit Γ) ↔ Derivable Γ :=
  ⟨fun ⟨d⟩ => ⟨d.toFam⟩, fun ⟨d⟩ => ⟨d.toLit⟩⟩

/-! ## What the source asserts, as terms of the family

The source draws no derivation of this fragment (the one of p. 26 is of
the exponentials).  These are derivations of what it asserts, chosen by
the operator; `campaign/rule-table.md` cites each. -/

namespace Source

/-- The letter `p`. -/
abbrev p : Form := .atom 0
/-- The letter `q`. -/
abbrev q : Form := .atom 1
/-- The letter `r`. -/
abbrev r : Form := .atom 2

/-- The logical axiom at a letter, `⊢ p, p⊥`. -/
def axP : Fam [p, pᗮ] := .ax p (.refl _)

/-- The two steps of p. 26 that are in the fragment: from the axiom
`⊢ p⊥, p` to `⊢ p⊥, p ⊕ q` by 1⊕. -/
def p26 : Fam [pᗮ, p ⊕ q] :=
  .plus₁ p q [pᗮ] (by decide) (.ax p (.refl _))

/-- P. 5: "A ⊸ A & A is [derivable]", at a letter: `⊢ p⊥ ⅋ (p & p)`. -/
def p5 : Fam [pᗮ ⅋ (p & p)] :=
  .par pᗮ (p & p) [] (.refl _)                  -- ⊢ p⊥, p & p
    (.wth p p [pᗮ] (by decide)
      (.ax p (.refl _))                           -- ⊢ p, p⊥
      (.ax p (.refl _)))

/-- The axiom at a compound formula from axioms at letters (the remark of
p. 22): `⊢ (p ⊗ q)⊥, p ⊗ q`, that is `⊢ p⊥ ⅋ q⊥, p ⊗ q`. -/
def idTensor : Fam [(p ⊗ q)ᗮ, p ⊗ q] :=
  .par pᗮ qᗮ [p ⊗ q] (.refl _)                  -- ⊢ p⊥, q⊥, p ⊗ q
    (.tensor p q [pᗮ] [qᗮ] (by decide)
      (.ax p (.refl _))                           -- ⊢ p, p⊥
      (.ax q (.refl _)))                          -- ⊢ q, q⊥

/-- 1.9(ii), "times is commutative", one half: `⊢ (p ⊗ q)⊥, q ⊗ p`.  The
split of the context is the other way round. -/
def tensorComm : Fam [(p ⊗ q)ᗮ, q ⊗ p] :=
  .par pᗮ qᗮ [q ⊗ p] (.refl _)
    (.tensor q p [qᗮ] [pᗮ] (by decide) (.ax q (.refl _)) (.ax p (.refl _)))

/-- 1.9(ii), `1 ⊗ G = G`, one half: `⊢ (𝟏 ⊗ p)⊥, p`, that is
`⊢ ⊥ ⅋ p⊥, p`.  Uses the rule ⊥. -/
def tensorUnit : Fam [(𝟏 ⊗ p)ᗮ, p] :=
  .par ⊥ pᗮ [p] (.refl _)                        -- ⊢ ⊥, p⊥, p
    (.bot [pᗮ, p] (.refl _) (.ax p (by decide)))

/-- The other half: `⊢ p⊥, 𝟏 ⊗ p`.  Uses the rule 1, with the empty
context on the left of the split. -/
def tensorUnit' : Fam [pᗮ, 𝟏 ⊗ p] :=
  .tensor 𝟏 p [] [pᗮ] (by decide) (.one (.refl _)) (.ax p (.refl _))

/-- 1.13(i), "⊗ is distributive w.r.t. ⊕", one half:
`⊢ (p ⊗ (q ⊕ r))⊥, (p ⊗ q) ⊕ (p ⊗ r)`. -/
def distrib : Fam [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)] :=
  .par pᗮ (qᗮ & rᗮ) [(p ⊗ q) ⊕ (p ⊗ r)] (.refl _)        -- ⊢ p⊥, q⊥ & r⊥, (p⊗q) ⊕ (p⊗r)
    (.wth qᗮ rᗮ [pᗮ, (p ⊗ q) ⊕ (p ⊗ r)] (by decide)
      (.plus₁ (p ⊗ q) (p ⊗ r) [qᗮ, pᗮ] (by decide)          -- ⊢ p ⊗ q, q⊥, p⊥
        (.tensor p q [pᗮ] [qᗮ] (by decide) (.ax p (.refl _)) (.ax q (.refl _))))
      (.plus₂ (p ⊗ q) (p ⊗ r) [rᗮ, pᗮ] (by decide)          -- ⊢ p ⊗ r, r⊥, p⊥
        (.tensor p r [pᗮ] [rᗮ] (by decide) (.ax p (.refl _)) (.ax r (.refl _)))))

/-- 1.13(i), `⊤ ⅋ G = ⊤`, one half: `⊢ (⊤ ⅋ p)⊥, ⊤`, by the rule ⊤ with a
context. -/
def topAbsorbs : Fam [(⊤ ⅋ p)ᗮ, ⊤] := .top [(⊤ ⅋ p)ᗮ] (by decide)

/-- The cut rule: from `⊢ p ⊗ q, p⊥, q⊥` and `⊢ (p ⊗ q)⊥, q ⊗ p` to
`⊢ p⊥, q⊥, q ⊗ p`. -/
def cutEx : Fam [pᗮ, qᗮ, q ⊗ p] :=
  .cut (p ⊗ q) [pᗮ, qᗮ] [q ⊗ p] (.refl _)
    (.tensor p q [pᗮ] [qᗮ] (.refl _) (.ax p (.refl _)) (.ax q (.refl _)))
    tensorComm

example : cutEx.height = 4 := rfl

/-- The same derivations, in the figure's own form. -/
example : Lit [pᗮ ⅋ (p & p)] := p5.toLit

/-- The figure's form, written by hand: every rule at the head, and one
exchange to bring `p & p` there. -/
def p5Lit : Lit [pᗮ ⅋ (p & p)] :=
  .par (.exch (.wth (.ax p pᗮ rfl) (.ax p pᗮ rfl)) (by decide))

end Source

end MALL

#axioms_within_file [propext, Quot.sound]
