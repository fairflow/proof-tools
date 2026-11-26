/-
Tests of Craig interpolation (`MALL/Craig.lean`): the interpolant of
eight sequents, each divided in one or more ways, evaluated and pinned.

For each division:

* the interpolant is pinned in the kernel (`by decide +kernel`);
* the two derivations `⊢ C, Γ` and `⊢ C⊥, Δ` are fields of the result, so
  they exist by construction: they are restated at the pinned formula
  (`pinned`), and their rules are pinned by evaluation (`sketch`);
* the condition on letters and Lyndon's condition on literals are
  computed (`ok`).

The derivations are those that `searchCF` finds, but for the last
sequent, where two derivations written by hand have different
interpolants.  Every pinned value was pasted from Lean's output
(`#eval`) after reading it.

Code, not theory.  The letters are written `p q r`; a dual is typed `pᗮ`.
-/
import MALL.Craig
import MALL.Decide

namespace MALL.CraigTest

open MALL List

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

/-- The derivation without cut that the search finds. -/
def found (Γ : List Form) (h : (searchCF Γ).isSome = true := by decide +kernel) : CF Γ :=
  (searchCF Γ).get h

/-- The rules of a derivation, from the last one up. -/
def sketch : {Ξ : List Form} → CF Ξ → String
  | _, .ax _ _ => "ax"
  | _, .top _ _ => "⊤"
  | _, .wth _ _ _ _ d₁ d₂ => "&(" ++ sketch d₁ ++ ", " ++ sketch d₂ ++ ")"
  | _, .plus₁ _ _ _ _ d => "1⊕(" ++ sketch d ++ ")"
  | _, .plus₂ _ _ _ _ d => "2⊕(" ++ sketch d ++ ")"
  | _, .one _ => "1"
  | _, .bot _ _ d => "⊥(" ++ sketch d ++ ")"
  | _, .tensor _ _ _ _ _ d₁ d₂ => "⊗(" ++ sketch d₁ ++ ", " ++ sketch d₂ ++ ")"
  | _, .par _ _ _ _ d => "⅋(" ++ sketch d ++ ")"

/-- Every letter of `C` is a letter of `Γ` and of `Δ`, computed. -/
def lettersOK (C : Form) (Γ Δ : List Form) : Bool :=
  C.letters.all fun a => (lettersL Γ).contains a && (lettersL Δ).contains a

/-- Lyndon's condition, computed: every literal of `C` is a literal of
`Δ`, and its dual one of `Γ`. -/
def lyndonOK (C : Form) (Γ Δ : List Form) : Bool :=
  C.lits.all fun ℓ => (litsL Γ).contains ℓᗮ && (litsL Δ).contains ℓ

/-- The two conditions, of an interpolant. -/
def ok {Γ Δ : List Form} (i : Interpolant Γ Δ) : Bool :=
  lettersOK i.C Γ Δ && lyndonOK i.C Γ Δ

/-- The two derivations of an interpolant, at the formula it is pinned
to. -/
def pinned {Γ Δ : List Form} (i : Interpolant Γ Δ) (C : Form) (h : i.C = C) :
    CF (C :: Γ) × CF (Cᗮ :: Δ) :=
  h ▸ (i.left, i.right)

-- the computed conditions do refuse: `p` has the letters of `⊢ p, p`
-- divided in two, but not the signs; and `q` is not a letter of `p`
#guard lettersOK p [p] [p]
#guard !lyndonOK p [p] [p]
#guard !lettersOK q [p] [q]
#guard lyndonOK p [pᗮ] [p]

/-! ## 1. `⊢ p⊥, p`, divided in the four ways -/

/-- `(p⊥ ; p)`: the interpolant is `p`. -/
def ax₁ : Interpolant [pᗮ] [p] := craigInterpolation _ _ (found _)

example : ax₁.C = p := by decide +kernel
example : CF [p, pᗮ] × CF [pᗮ, p] := pinned ax₁ p (by decide +kernel)
#guard sketch ax₁.left == "ax" && sketch ax₁.right == "ax"
#guard ok ax₁

/-- `(p ; p⊥)`: the interpolant is `p⊥`. -/
def ax₂ : Interpolant [p] [pᗮ] := craigInterpolation _ _ (found _)

example : ax₂.C = pᗮ := by decide +kernel
example : CF [pᗮ, p] × CF [p, pᗮ] := pinned ax₂ pᗮ (by decide +kernel)
#guard sketch ax₂.left == "ax" && sketch ax₂.right == "ax"
#guard ok ax₂

/-- `(p⊥, p ; )`: the interpolant is `⊥`. -/
def ax₃ : Interpolant [pᗮ, p] [] := craigInterpolation _ _ (found _)

example : ax₃.C = ⊥ := by decide +kernel
example : CF [⊥, pᗮ, p] × CF [𝟏] := pinned ax₃ ⊥ (by decide +kernel)
#guard sketch ax₃.left == "⊥(ax)" && sketch ax₃.right == "1"
#guard ok ax₃

/-- `( ; p⊥, p)`: the interpolant is `𝟏`. -/
def ax₄ : Interpolant [] [pᗮ, p] := craigInterpolation _ _ (found _)

example : ax₄.C = 𝟏 := by decide +kernel
example : CF [𝟏] × CF [⊥, pᗮ, p] := pinned ax₄ 𝟏 (by decide +kernel)
#guard sketch ax₄.left == "1" && sketch ax₄.right == "⊥(ax)"
#guard ok ax₄

/-! ## 2. `⊢ (p ⊗ q)⊥, q ⊗ p` -/

/-- `((p ⊗ q)⊥ ; q ⊗ p)`: the interpolant is `q ⊗ p`. -/
def comm₁ : Interpolant [(p ⊗ q)ᗮ] [q ⊗ p] := craigInterpolation _ _ (found _)

example : comm₁.C = q ⊗ p := by decide +kernel
example : CF [q ⊗ p, pᗮ ⅋ qᗮ] × CF [qᗮ ⅋ pᗮ, q ⊗ p] := pinned comm₁ (q ⊗ p) (by decide +kernel)
#guard sketch comm₁.left == "⅋(⊗(ax, ax))" && sketch comm₁.right == "⅋(⊗(ax, ax))"
#guard ok comm₁

/-- The division reversed, `(q ⊗ p ; (p ⊗ q)⊥)`: the interpolant is the
dual, `q⊥ ⅋ p⊥`. -/
def comm₂ : Interpolant [q ⊗ p] [(p ⊗ q)ᗮ] := craigInterpolation _ _ (found _)

example : comm₂.C = qᗮ ⅋ pᗮ := by decide +kernel
example : comm₂.C = comm₁.Cᗮ := by decide +kernel
example : CF [qᗮ ⅋ pᗮ, q ⊗ p] × CF [q ⊗ p, pᗮ ⅋ qᗮ] :=
  pinned comm₂ (qᗮ ⅋ pᗮ) (by decide +kernel)
#guard sketch comm₂.left == "⅋(⊗(ax, ax))" && sketch comm₂.right == "⅋(⊗(ax, ax))"
#guard ok comm₂

/-! ## 3. ⊗ distributes over ⊕: `⊢ (p ⊗ (q ⊕ r))⊥, (p ⊗ q) ⊕ (p ⊗ r)` -/

/-- Divided between its two formulas: the interpolant is
`(p ⊗ q) ⊕ (p ⊗ r)`. -/
def distrib : Interpolant [(p ⊗ (q ⊕ r))ᗮ] [(p ⊗ q) ⊕ (p ⊗ r)] :=
  craigInterpolation _ _ (found _)

example : distrib.C = (p ⊗ q) ⊕ (p ⊗ r) := by decide +kernel
example :
    CF [(p ⊗ q) ⊕ (p ⊗ r), pᗮ ⅋ (qᗮ & rᗮ)] ×
      CF [(pᗮ ⅋ qᗮ) & (pᗮ ⅋ rᗮ), (p ⊗ q) ⊕ (p ⊗ r)] :=
  pinned distrib _ (by decide +kernel)
#guard sketch distrib.left == "⅋(&(1⊕(⊗(ax, ax)), 2⊕(⊗(ax, ax))))"
#guard sketch distrib.right == "&(1⊕(⅋(⊗(ax, ax))), 2⊕(⅋(⊗(ax, ax))))"
#guard ok distrib

/-! ## 4. & in each part: `⊢ p⊥ & q⊥, (p ⊕ q) & (q ⊕ p)` -/

/-- The interpolant is `(p & p) ⊕ (q & q)`: a & for the & of the second
part, under a ⊕ for the & of the first. -/
def withs : Interpolant [pᗮ & qᗮ] [(p ⊕ q) & (q ⊕ p)] := craigInterpolation _ _ (found _)

example : withs.C = (p & p) ⊕ (q & q) := by decide +kernel
example :
    CF [(p & p) ⊕ (q & q), pᗮ & qᗮ] × CF [(pᗮ ⊕ pᗮ) & (qᗮ ⊕ qᗮ), (p ⊕ q) & (q ⊕ p)] :=
  pinned withs _ (by decide +kernel)
#guard sketch withs.left == "&(1⊕(&(ax, ax)), 2⊕(&(ax, ax)))"
#guard sketch withs.right == "&(&(1⊕(1⊕(ax)), 2⊕(2⊕(ax))), &(1⊕(2⊕(ax)), 2⊕(1⊕(ax))))"
#guard ok withs

/-! ## 5. ⊤: `⊢ ⊤, p, q` -/

/-- ⊤ in the first part, `(⊤, p ; q)`: the interpolant is `𝟎`, though `p`
and `q` have no letter in common. -/
def top₁ : Interpolant [⊤, p] [q] := craigInterpolation _ _ (found _)

example : top₁.C = 𝟎 := by decide +kernel
example : CF [𝟎, ⊤, p] × CF [⊤, q] := pinned top₁ 𝟎 (by decide +kernel)
#guard sketch top₁.left == "⊤" && sketch top₁.right == "⊤"
#guard ok top₁

/-- ⊤ in the second part, `(p ; ⊤, q)`: the interpolant is `⊤`. -/
def top₂ : Interpolant [p] [⊤, q] := craigInterpolation _ _ (found _)

example : top₂.C = ⊤ := by decide +kernel
example : CF [⊤, p] × CF [𝟎, ⊤, q] := pinned top₂ ⊤ (by decide +kernel)
#guard sketch top₂.left == "⊤" && sketch top₂.right == "⊤"
#guard ok top₂

/-! ## 6. A context of three formulas, divided through a ⊗:
`⊢ p ⊗ q, p⊥, q⊥` -/

/-- `(p ⊗ q, p⊥ ; q⊥)`: ⊗ is in the first part, its premise `⊢ p, p⊥` is
all in the first part (`⊥`) and its premise `⊢ q, q⊥` is divided (`q⊥`):
the interpolant is `⊥ ⅋ q⊥`. -/
def three₁ : Interpolant [p ⊗ q, pᗮ] [qᗮ] := craigInterpolation _ _ (found _)

example : three₁.C = ⊥ ⅋ qᗮ := by decide +kernel
example : CF [⊥ ⅋ qᗮ, p ⊗ q, pᗮ] × CF [𝟏 ⊗ q, qᗮ] := pinned three₁ (⊥ ⅋ qᗮ) (by decide +kernel)
#guard sketch three₁.left == "⅋(⊗(⊥(ax), ax))" && sketch three₁.right == "⊗(1, ax)"
#guard ok three₁

/-- The division reversed, `(q⊥ ; p ⊗ q, p⊥)`: ⊗ is in the second part,
and the interpolant is the dual, `𝟏 ⊗ q`. -/
def three₂ : Interpolant [qᗮ] [p ⊗ q, pᗮ] := craigInterpolation _ _ (found _)

example : three₂.C = 𝟏 ⊗ q := by decide +kernel
example : three₂.C = three₁.Cᗮ := by decide +kernel
example : CF [𝟏 ⊗ q, qᗮ] × CF [⊥ ⅋ qᗮ, p ⊗ q, pᗮ] := pinned three₂ (𝟏 ⊗ q) (by decide +kernel)
#guard sketch three₂.left == "⊗(1, ax)" && sketch three₂.right == "⅋(⊗(⊥(ax), ax))"
#guard ok three₂

/-- `(p⊥, q⊥ ; p ⊗ q)`: the interpolant is `p ⊗ q`. -/
def three₃ : Interpolant [pᗮ, qᗮ] [p ⊗ q] := craigInterpolation _ _ (found _)

example : three₃.C = p ⊗ q := by decide +kernel
example : CF [p ⊗ q, pᗮ, qᗮ] × CF [pᗮ ⅋ qᗮ, p ⊗ q] := pinned three₃ (p ⊗ q) (by decide +kernel)
#guard sketch three₃.left == "⊗(ax, ax)" && sketch three₃.right == "⅋(⊗(ax, ax))"
#guard ok three₃

/-! ## 7. Two ⊗, one in each part: `⊢ p ⊗ q, r⊥, q⊥ ⊗ r, p⊥` -/

/-- `(p ⊗ q, r⊥ ; q⊥ ⊗ r, p⊥)`: the interpolant is `p⊥ ⅋ (q⊥ ⊗ r)`, a ⅋
for the ⊗ of the first part and a ⊗ for that of the second.  Each of its
three letters has in it the sign it has in the second part. -/
def two : Interpolant [p ⊗ q, rᗮ] [qᗮ ⊗ r, pᗮ] := craigInterpolation _ _ (found _)

example : two.C = pᗮ ⅋ (qᗮ ⊗ r) := by decide +kernel
example : CF [pᗮ ⅋ (qᗮ ⊗ r), p ⊗ q, rᗮ] × CF [p ⊗ (q ⅋ rᗮ), qᗮ ⊗ r, pᗮ] :=
  pinned two _ (by decide +kernel)
#guard sketch two.left == "⅋(⊗(ax, ⊗(ax, ax)))" && sketch two.right == "⊗(ax, ⅋(⊗(ax, ax)))"
#guard ok two

/-! ## 8. The interpolant is of the derivation: `⊢ ⊤ ⊕ p⊥, p`, by hand,
in two ways -/

/-- By 1⊕, then ⊤. -/
def byPlus₁ : CF [⊤ ⊕ pᗮ, p] := .plus₁ ⊤ pᗮ [p] (.refl _) (.top [p] (.refl _))

/-- By 2⊕, then the logical axiom. -/
def byPlus₂ : CF [⊤ ⊕ pᗮ, p] := .plus₂ ⊤ pᗮ [p] (.refl _) (.ax p (.swap ..))

/-- Of the first derivation, divided between its two formulas: `𝟎`. -/
def hand₁ : Interpolant [⊤ ⊕ pᗮ] [p] := craigInterpolation _ _ byPlus₁

example : hand₁.C = 𝟎 := by decide +kernel
example : CF [𝟎, ⊤ ⊕ pᗮ] × CF [⊤, p] := pinned hand₁ 𝟎 (by decide +kernel)
#guard sketch hand₁.left == "1⊕(⊤)" && sketch hand₁.right == "⊤"
#guard ok hand₁

/-- Of the second, at the same division: `p`. -/
def hand₂ : Interpolant [⊤ ⊕ pᗮ] [p] := craigInterpolation _ _ byPlus₂

example : hand₂.C = p := by decide +kernel
example : CF [p, ⊤ ⊕ pᗮ] × CF [pᗮ, p] := pinned hand₂ p (by decide +kernel)
#guard sketch hand₂.left == "2⊕(ax)" && sketch hand₂.right == "ax"
#guard ok hand₂

-- the search finds the first
#guard sketch (found [⊤ ⊕ pᗮ, p]) == "1⊕(⊤)"

/-! ## 9. For an implication -/

-- `p ⊗ q ⊸ q ⊗ p` has an interpolant in the letters of both
example : ∃ C : Form, Derivable [(p ⊗ q)ᗮ, C] ∧ Derivable [Cᗮ, q ⊗ p] ∧
    ∀ a ∈ C.letters, a ∈ (p ⊗ q).letters ∧ a ∈ (q ⊗ p).letters :=
  craigForFormulas (p ⊗ q) (q ⊗ p) ⟨(found _).toFam⟩

end MALL.CraigTest
