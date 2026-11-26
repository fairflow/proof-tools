/-
Tests of uniform interpolation: interpolants evaluated by the kernel and
pinned, the two properties screened against the decision procedure on
small formulas, and the theorems used.

Every pinned value was printed by Lean first.
-/
import MALL.Uniform
import MALL.Results
import LeanCertify

namespace MALL.UniformTest

open MALL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

/-! ## Interpolants, computed by the kernel -/

-- A letter: nothing without `p` implies `p` but 𝟎, and `p` implies nothing
-- without `p` but ⊤.
example : forallP 0 p = 𝟎 := by decide +kernel
example : existsP 0 p = ⊤ := by decide +kernel
-- A formula without the letter is its own interpolant.
example : forallP 0 q = q := by decide +kernel
example : existsP 0 q = q := by decide +kernel

-- `p ⅋ p⊥` holds: its ∀ is the unit of ⊗.  `p ⊗ p⊥` is its dual.
example : forallP 0 (p ⅋ pᗮ) = 𝟏 := by decide +kernel
example : existsP 0 (p ⊗ pᗮ) = ⊥ := by decide +kernel

-- Cut, as an interpolant: `p ⊸ p ⊗ q`, that is `p⊥ ⅋ (p ⊗ q)`, is implied by `q`.
example : forallP 0 ((p ⊗ q) ⅋ pᗮ) = q := by decide +kernel
example : existsP 0 ((p ⅋ q) ⊗ pᗮ) = q := by decide +kernel

-- No weakening: `∃p (p ⊗ q)` is `⊤ ⊗ q`, not `q`; `∀p (p ⅋ q)` is `𝟎 ⅋ q`.
example : existsP 0 (p ⊗ q) = ⊤ ⊗ q := by decide +kernel
example : forallP 0 (p ⅋ q) = 𝟎 ⅋ q := by decide +kernel

-- The additives: `∀p (p ⊕ q)` and `∃p (p & q)` are `q`.
example : forallP 0 (p ⊕ q) = q := by decide +kernel
example : existsP 0 (p & q) = q := by decide +kernel

example : existsP 0 ((p ⊗ q) ⊕ (pᗮ ⊗ r)) = (⊤ ⊗ q) ⊕ (⊤ ⊗ r) := by decide +kernel
example : forallP 0 ((pᗮ ⅋ q) & (p ⅋ r)) = (𝟎 ⅋ q) & (𝟎 ⅋ r) := by decide +kernel

-- The middle letter of two implications taken additively: nothing is left.
example : existsP 1 ((pᗮ ⅋ q) & (qᗮ ⅋ r)) = ⊤ := by decide +kernel

-- `p ⊸ q ⊗ (q ⊸ r)`, the letter `q`.
example : forallP 1 (pᗮ ⅋ (q ⊗ (qᗮ ⅋ r))) = ((𝟎 ⅋ pᗮ) ⊗ (𝟎 ⅋ r)) ⊕ (pᗮ ⅋ 𝟎) := by
  decide +kernel

/-! ## The two properties, against the decision procedure

Compiled evaluation.  For each of 21 formulas `A`: `∀p A ⊢ A` and
`A ⊢ ∃p A`; and for each of the 264 formulas `B` over `q`, `r` and the units
with at most one connective: `B ⊢ A` gives `B ⊢ ∀p A`, and `A ⊢ B` gives
`∃p A ⊢ B`.  This was run before the proof, as the screen of the
statement. -/

def tests : List Form := [p, pᗮ, q, p ⊗ q, p ⅋ q, p & q, p ⊕ q, p ⅋ pᗮ, p ⊗ pᗮ, (p ⊗ q) ⅋ pᗮ,
  (p ⅋ q) ⊗ pᗮ, (pᗮ ⅋ q) & (p ⅋ r), (p ⊗ q) ⊕ (pᗮ ⊗ r), pᗮ ⅋ (p ⊗ q), (p & q) ⅋ (pᗮ ⊕ r),
  p ⅋ (pᗮ ⊗ q), ⊤ ⊗ p, (p ⊗ q) & (pᗮ ⅋ q), p ⅋ p, pᗮ ⅋ (p ⊗ p), (p ⊕ q) ⅋ (pᗮ & r)]

def base : List Form := [q, qᗮ, r, rᗮ, 𝟏, ⊥, ⊤, 𝟎]

def small : List Form :=
  base ++ base.flatMap fun A => base.flatMap fun B => [A ⊗ B, A ⅋ B, A & B, A ⊕ B]

instance (Γ : List Form) : Decidable (Derivable Γ) := decDerivable Γ

#guard tests.all fun A =>
  decide (Derivable [(forallP 0 A)ᗮ, A]) && decide (Derivable [Aᗮ, existsP 0 A])

#guard tests.all fun A => small.all fun B =>
  (!decide (Derivable [Bᗮ, A]) || decide (Derivable [Bᗮ, forallP 0 A])) &&
  (!decide (Derivable [Aᗮ, B]) || decide (Derivable [(existsP 0 A)ᗮ, B]))

-- The interpolants have no `p`.
#guard tests.all fun A => !(forallP 0 A).letters.contains 0 && !(existsP 0 A).letters.contains 0

#guard small.length == 264

/-! ## The theorems, used -/

/-- From `q ⊢ p ⊸ p ⊗ q` to `q ⊢ ∀p (p ⊸ p ⊗ q)`, by the theorem. -/
example : Derivable [forallP 0 ((p ⊗ q) ⅋ pᗮ), qᗮ] :=
  (ui_spec 0 [(p ⊗ q) ⅋ pᗮ]).2.2 [qᗮ] (by decide) (by decide +kernel)

#certify_axioms MALL.uniformInterpolation
#certify_axioms MALL.uniformInterpolationForFormulas
#certify_axioms MALL.ui_spec

end MALL.UniformTest
