/-
Tests of cut elimination: the derivation of `MALL/Source.lean` that has a
cut, one cut on each pair of dual rules, an axiom against a rule, ⊤ in a
context, cuts that pass a rule that introduces another formula, and the
inversions.  Each result is a `CF` derivation by its type; its height is
pinned in the kernel (`by decide`) and its rules by evaluation
(`#guard`).  Every pinned value was pasted from Lean's output after
reading it.

Code, not theory.
-/
import MALL.Cut
import MALL.Source

namespace MALL.CutTest

open MALL List

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

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

/-- The logical axiom with the dual first: `⊢ A⊥, A`. -/
def ax' (A : Form) : CF [Aᗮ, A] := .ax A (.swap ..)

/-! ## 1. Derivations with cut -/

/-- `⊢ p⊥, q⊥, q ⊗ p` without cut: the cut of `Source.cutEx` on `p ⊗ q`
is gone. -/
def cutEx' : CF [pᗮ, qᗮ, q ⊗ p] := cutElimination _ Source.cutEx

example : Source.cutEx.height = 4 := by decide
example : cutEx'.height = 2 := by decide
#guard sketch cutEx' == "⊗(ax, ax)"

-- a derivation without cut is left as it is
example : (cutElimination _ Source.distrib).height = Source.distrib.height := by decide
#guard sketch (cutElimination _ Source.distrib) == "⅋(&(1⊕(⊗(ax, ax)), 2⊕(⊗(ax, ax))))"

/-- A cut above a cut: the left premise of the cut of `Source.cutEx` is
itself by a cut, against the axiom at `p ⊗ q`. -/
def nested : Fam [pᗮ, qᗮ, q ⊗ p] :=
  .cut (p ⊗ q) [pᗮ, qᗮ] [q ⊗ p] (.refl _)
    (.cut (p ⊗ q) [pᗮ, qᗮ] [p ⊗ q] (by decide)
      (.tensor p q [pᗮ] [qᗮ] (.refl _) (.ax p (.refl _)) (.ax q (.refl _)))
      (.ax (p ⊗ q) (.swap ..)))
    Source.tensorComm

example : nested.height = 4 := by decide
example : (cutElimination _ nested).height = 2 := by decide
#guard sketch (cutElimination _ nested) == "⊗(ax, ax)"

/-! ## 2. One cut on each pair of dual rules -/

/-- `⊢ p ⊗ q, p⊥, q⊥`, by ⊗. -/
def tensorL : CF [p ⊗ q, pᗮ, qᗮ] :=
  .tensor p q [pᗮ] [qᗮ] (.refl _) (.ax p (.refl _)) (.ax q (.refl _))

/-- `⊢ p⊥ ⅋ q⊥, q ⊗ p`, by ⅋. -/
def parR : CF [pᗮ ⅋ qᗮ, q ⊗ p] :=
  .par pᗮ qᗮ [q ⊗ p] (.refl _)
    (.tensor q p [qᗮ] [pᗮ] (by decide) (.ax q (.refl _)) (.ax p (.refl _)))

/-- ⊗ on the left, ⅋ on the right: two cuts on letters. -/
def tensorPar : CF [pᗮ, qᗮ, q ⊗ p] := cutAdmissible (p ⊗ q) [pᗮ, qᗮ] [q ⊗ p] tensorL parR
example : tensorPar.height = 2 := by decide
#guard sketch tensorPar == "⊗(ax, ax)"

/-- ⅋ on the left, ⊗ on the right. -/
def parTensor : CF [q ⊗ p, pᗮ, qᗮ] := cutAdmissible (pᗮ ⅋ qᗮ) [q ⊗ p] [pᗮ, qᗮ] parR tensorL
example : parTensor.height = 2 := by decide
#guard sketch parTensor == "⊗(ax, ax)"

/-- `⊢ p & ⊤, p⊥`, by &: the two premises are by different rules. -/
def wthL : CF [p & ⊤, pᗮ] := .wth p ⊤ [pᗮ] (.refl _) (.ax p (.refl _)) (.top [pᗮ] (.refl _))

/-- `⊢ p⊥ ⊕ 𝟎, p`, by 1⊕. -/
def plusR₁ : CF [(pᗮ ⊕ 𝟎), p] := .plus₁ pᗮ 𝟎 [p] (.refl _) (ax' p)

/-- `⊢ p⊥ ⊕ 𝟎, ⊤`, by 2⊕. -/
def plusR₂ : CF [(pᗮ ⊕ 𝟎), ⊤] := .plus₂ pᗮ 𝟎 [⊤] (.refl _) (.top [𝟎] (by decide))

/-- & on the left, 1⊕ on the right: the cut is on the first premise of &. -/
def wthPlus₁ : CF [pᗮ, p] := cutAdmissible (p & ⊤) [pᗮ] [p] wthL plusR₁
example : wthPlus₁.height = 1 := by decide
#guard sketch wthPlus₁ == "ax"

/-- & on the left, 2⊕ on the right: the cut is on the second premise. -/
def wthPlus₂ : CF [pᗮ, ⊤] := cutAdmissible (p & ⊤) [pᗮ] [⊤] wthL plusR₂
example : wthPlus₂.height = 1 := by decide
#guard sketch wthPlus₂ == "⊤"

/-- 1⊕ on the left, & on the right. -/
def plus₁Wth : CF [p, pᗮ] := cutAdmissible (.plus pᗮ 𝟎) [p] [pᗮ] plusR₁ wthL
example : plus₁Wth.height = 1 := by decide
#guard sketch plus₁Wth == "ax"

/-- 2⊕ on the left, & on the right. -/
def plus₂Wth : CF [⊤, pᗮ] := cutAdmissible (.plus pᗮ 𝟎) [⊤] [pᗮ] plusR₂ wthL
example : plus₂Wth.height = 1 := by decide
#guard sketch plus₂Wth == "⊤"

/-- `⊢ ⊥, p, p⊥`, by ⊥. -/
def botR : CF [⊥, p, pᗮ] := .bot [p, pᗮ] (.refl _) (.ax p (.refl _))

/-- 𝟏 on the left, ⊥ on the right: the premise of ⊥ is the result. -/
def oneBot : CF [p, pᗮ] := cutAdmissible 𝟏 [] [p, pᗮ] (.one (.refl _)) botR
example : oneBot.height = 1 := by decide
#guard sketch oneBot == "ax"

/-- ⊥ on the left, 𝟏 on the right. -/
def botOne : CF [p, pᗮ] := cutAdmissible ⊥ [p, pᗮ] [] botR (.one (.refl _))
example : botOne.height = 1 := by decide
#guard sketch botOne == "ax"

/-! ## 3. An axiom against a rule -/

/-- The axiom `⊢ p ⊗ q, (p ⊗ q)⊥` on the left: the right premise is the
result. -/
def axRule : CF [pᗮ ⅋ qᗮ, q ⊗ p] :=
  cutAdmissible (p ⊗ q) [pᗮ ⅋ qᗮ] [q ⊗ p] (.ax (p ⊗ q) (.refl _)) parR
example : axRule.height = 3 := by decide
#guard sketch axRule == "⅋(⊗(ax, ax))"

/-- The axiom on the right, the cut on its second formula: the left
premise is the result. -/
def ruleAx : CF [pᗮ, qᗮ, p ⊗ q] :=
  cutAdmissible (p ⊗ q) [pᗮ, qᗮ] [p ⊗ q] tensorL (ax' (p ⊗ q))
example : ruleAx.height = 2 := by decide
#guard sketch ruleAx == "⊗(ax, ax)"

/-- The axiom at `p ⊗ q` from axioms at letters, cut against itself. -/
def idId : CF [pᗮ ⅋ qᗮ, p ⊗ q] :=
  cutAdmissible (p ⊗ q) [pᗮ ⅋ qᗮ] [p ⊗ q]
    (.par pᗮ qᗮ [p ⊗ q] (.swap ..) (tensorL.exch (by decide)))
    (.par pᗮ qᗮ [p ⊗ q] (.refl _) (tensorL.exch (by decide)))
example : idId.height = 3 := by decide
#guard sketch idId == "⅋(⊗(ax, ax))"

/-! ## 4. ⊤ in a context -/

/-- The cut formula `p` is in the context of ⊤ on the left: one ⊤. -/
def topCtx : CF [⊤, q, p] :=
  cutAdmissible p [⊤, q] [p] (.top [p, q] (by decide)) (ax' p)
example : topCtx.height = 1 := by decide
#guard sketch topCtx == "⊤"

/-- ⊤ is the cut formula; `𝟎` on the right is in the context of a ⊤. -/
def topZero : CF [r, ⊤, q] :=
  cutAdmissible ⊤ [r] [⊤, q] (.top [r] (.refl _)) (.top [𝟎, q] (by decide))
example : topZero.height = 1 := by decide
#guard sketch topZero == "⊤"

/-- `𝟎` is the cut formula, on the left in the context of a ⊤. -/
def zeroTop : CF [⊤, q, r] :=
  cutAdmissible 𝟎 [⊤, q] [r] (.top [𝟎, q] (by decide)) (.top [r] (.refl _))
example : zeroTop.height = 1 := by decide
#guard sketch zeroTop == "⊤"

/-- ⊤ against the axiom `⊢ 𝟎, ⊤`. -/
def topAx : CF [r, ⊤] := cutAdmissible ⊤ [r] [⊤] (.top [r] (.refl _)) (.ax 𝟎 (.refl _))
example : topAx.height = 1 := by decide
#guard sketch topAx == "⊤"

/-! ## 5. The cut passes a rule that introduces another formula -/

/-- `⊢ p⊥, p ⊗ 𝟏`, by ⊗: `p⊥` is in the context of the first premise. -/
def tensorOne : CF [pᗮ, p ⊗ 𝟏] :=
  .tensor p 𝟏 [pᗮ] [] (by decide) (.ax p (.refl _)) (.one (.refl _))

/-- `⊢ p⊥, 𝟏 ⊗ p`, by ⊗: `p⊥` is in the context of the second premise. -/
def oneTensor : CF [pᗮ, 𝟏 ⊗ p] :=
  .tensor 𝟏 p [] [pᗮ] (by decide) (.one (.refl _)) (.ax p (.refl _))

/-- `⊢ p, p⊥ & ⊤`, by &. -/
def wthR : CF [p, pᗮ & ⊤] := .wth pᗮ ⊤ [p] (by decide) (ax' p) (.top [p] (.refl _))

/-- Past & on the left: the cut is in both premises. -/
def pastWth : CF [pᗮ & ⊤, p ⊗ 𝟏] := cutAdmissible p [pᗮ & ⊤] [p ⊗ 𝟏] wthR tensorOne
example : pastWth.height = 3 := by decide
#guard sketch pastWth == "&(⊗(ax, 1), ⊤)"

/-- Past ⊗ on the left, into its first premise. -/
def pastTensor₁ : CF [p ⊗ 𝟏, pᗮ & ⊤] := cutAdmissible pᗮ [p ⊗ 𝟏] [pᗮ & ⊤] tensorOne wthR
example : pastTensor₁.height = 3 := by decide
#guard sketch pastTensor₁ == "⊗(&(ax, ⊤), 1)"

/-- Past ⊗ on the left, into its second premise. -/
def pastTensor₂ : CF [𝟏 ⊗ p, pᗮ & ⊤] := cutAdmissible pᗮ [𝟏 ⊗ p] [pᗮ & ⊤] oneTensor wthR
example : pastTensor₂.height = 3 := by decide
#guard sketch pastTensor₂ == "⊗(1, &(ax, ⊤))"

/-- Past ⅋ and then ⊤ on the left. -/
def pastPar : CF [pᗮ ⅋ ⊤, p] :=
  cutAdmissible p [pᗮ ⅋ ⊤] [p] (.par pᗮ ⊤ [p] (by decide) (.top [pᗮ, p] (by decide))) (ax' p)
example : pastPar.height = 2 := by decide
#guard sketch pastPar == "⅋(⊤)"

/-- Past ⊥ on the right: ⊗ on the left meets ⅋ above the ⊥. -/
def pastBot : CF [pᗮ, qᗮ, ⊥, q ⊗ p] :=
  cutAdmissible (p ⊗ q) [pᗮ, qᗮ] [⊥, q ⊗ p] tensorL
    (.bot [pᗮ ⅋ qᗮ, q ⊗ p] (by decide) parR)
example : pastBot.height = 3 := by decide
#guard sketch pastBot == "⊥(⊗(ax, ax))"

/-- Past 1⊕ and 2⊕ on the right: ⊗ on the left meets ⅋ above them. -/
def pastPlus : CF [pᗮ, qᗮ, ((𝟎 ⊕ q ⊗ p) ⊕ 𝟎)] :=
  cutAdmissible (p ⊗ q) [pᗮ, qᗮ] [((𝟎 ⊕ q ⊗ p) ⊕ 𝟎)] tensorL
    (.plus₁ (𝟎 ⊕ q ⊗ p) 𝟎 [pᗮ ⅋ qᗮ] (by decide)
      (.plus₂ 𝟎 (q ⊗ p) [pᗮ ⅋ qᗮ] (by decide) (parR.exch (.swap ..))))
example : pastPlus.height = 4 := by decide
#guard sketch pastPlus == "1⊕(2⊕(⊗(ax, ax)))"

/-! ## 6. The inversions -/

example : (parInversion pᗮ qᗮ [q ⊗ p] parR).height = 2 := by decide
#guard sketch (parInversion pᗮ qᗮ [q ⊗ p] parR) == "⊗(ax, ax)"

example : (botInversion [p, pᗮ] botR).height = 1 := by decide
#guard sketch (botInversion [p, pᗮ] botR) == "ax"

example : (withInversion p ⊤ [pᗮ] wthL).1.height = 1 := by decide
#guard sketch (withInversion p ⊤ [pᗮ] wthL).1 == "ax"
#guard sketch (withInversion p ⊤ [pᗮ] wthL).2 == "⊤"

-- an inversion past another rule: ⅋ under ⊥
example : CF [pᗮ, qᗮ, ⊥, q ⊗ p] :=
  (parInversion pᗮ qᗮ [⊥, q ⊗ p] (.bot [pᗮ ⅋ qᗮ, q ⊗ p] (by decide) parR))
#guard sketch (parInversion pᗮ qᗮ [⊥, q ⊗ p] (.bot [pᗮ ⅋ qᗮ, q ⊗ p] (by decide) parR))
  == "⊥(⊗(ax, ax))"

end MALL.CutTest
