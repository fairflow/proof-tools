/-
Tests of the decision procedure for derivability without cut: the kernel
runs the search (`decide +kernel`), on sequents with a derivation and on
sequents without one; and the derivation found has the expected height.

Code, not theory.  The letters are written `p q r`; a dual is typed `pᗮ`.
-/
import MALL.Decide

namespace MALL.DecideTest

open MALL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

/-! ## 1. Sequents with a derivation without cut -/

example : Nonempty (CF [p, pᗮ]) := by decide +kernel
example : Nonempty (CF [𝟏]) := by decide +kernel
example : Nonempty (CF [pᗮ ⅋ p]) := by decide +kernel
example : Nonempty (CF [⊤, p, q]) := by decide +kernel
example : Nonempty (CF [⊥, 𝟏]) := by decide +kernel
example : Nonempty (CF [pᗮ ⅋ (p & p)]) := by decide +kernel
example : Nonempty (CF [(p ⊕ pᗮ), (p ⊕ pᗮ)]) := by decide +kernel
example : Nonempty (CF [p ⊗ q, pᗮ, qᗮ]) := by decide +kernel
-- ⊗ distributes over ⊕, one way
example : Nonempty (CF [(p ⊗ (q ⊕ r))ᗮ, (p ⊗ q) ⊕ (p ⊗ r)]) := by decide +kernel
-- from `p ⊗ (q & r)` to `(p ⊗ q) & (p ⊗ r)`
example : Nonempty (CF [(p ⊗ (q & r))ᗮ, (p ⊗ q) & (p ⊗ r)]) := by decide +kernel

/-! ## 2. Sequents without one -/

example : ¬ Nonempty (CF [𝟏, 𝟏]) := by decide +kernel
example : ¬ Nonempty (CF []) := by decide +kernel
example : ¬ Nonempty (CF [𝟎]) := by decide +kernel
example : ¬ Nonempty (CF [(p ⊕ pᗮ)]) := by decide +kernel
example : ¬ Nonempty (CF [pᗮ ⅋ (p ⊗ p)]) := by decide +kernel
example : ¬ Nonempty (CF [p]) := by decide +kernel
example : ¬ Nonempty (CF [⊥]) := by decide +kernel
example : ¬ Nonempty (CF [𝟏, p, pᗮ]) := by decide +kernel
-- not from `(p ⊗ q) & (p ⊗ r)` to `p ⊗ (q & r)`
example : ¬ Nonempty (CF [((p ⊗ q) & (p ⊗ r))ᗮ, p ⊗ (q & r)]) := by decide +kernel
-- no rule of mix
example : ¬ Nonempty (CF [p ⅋ pᗮ, q ⅋ qᗮ]) := by decide +kernel
example : ¬ Nonempty (CF [p ⊗ pᗮ]) := by decide +kernel

/-! ## 3. The derivation found -/

-- compiled evaluation agrees with the kernel's
#guard (searchCF [p, pᗮ]).isSome
#guard !(searchCF [p ⊗ pᗮ]).isSome
-- an axiom: height 1
#guard (searchCF [p, pᗮ]).map CF.height == some 1
#guard (searchCF [pᗮ, p]).map CF.height == some 1
-- the axiom is tried first, for every formula, not only for a letter
#guard (searchCF [p ⊗ q, pᗮ ⅋ qᗮ]).map CF.height == some 1
-- ⅋, then the axiom
#guard (searchCF [pᗮ ⅋ p]).map CF.height == some 2
-- `⊢ ⊥, 1` is itself a logical axiom (`𝟏` is `⊥ᗮ`)
#guard (searchCF [⊥, 𝟏]).map CF.height == some 1
#guard (searchCF [𝟏]).map CF.height == some 1
-- ⊥, then that axiom, in either order
#guard (searchCF [⊥, ⊥, 𝟏]).map CF.height == some 2
#guard (searchCF [⊥, 𝟏, ⊥]).map CF.height == some 2
#guard (searchCF [⊥, ⊥, ⊥, 𝟏]).map CF.height == some 3
-- two ⊗, the second above the first
#guard (searchCF [p ⊗ q, qᗮ ⊗ r, pᗮ, rᗮ]).map CF.height == some 3
example : Nonempty (CF [p ⊗ q, qᗮ ⊗ r, pᗮ, rᗮ]) := by decide +kernel
-- two ⊗ and six formulas: no derivation (every split is tried)
example : ¬ Nonempty (CF [p ⊗ q, q ⊗ r, pᗮ, qᗮ, rᗮ, qᗮ]) := by decide +kernel
-- ⊗, with an axiom above each premise
#guard (searchCF [p ⊗ q, pᗮ, qᗮ]).map CF.height == some 2
-- ⅋, &, and two axioms
#guard (searchCF [pᗮ ⅋ (p & p)]).map CF.height == some 3
-- ⅋ on the left, then & on the right, then in each branch ⊗ and an ⊕
#guard (searchCF [(p ⊗ (q & r))ᗮ, (p ⊗ q) & (p ⊗ r)]).map CF.height == some 5
#guard (searchCF [p]).map CF.height == none

end MALL.DecideTest
