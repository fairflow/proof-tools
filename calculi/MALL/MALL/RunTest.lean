/-
Tests of the Run stage: a fact by each certifier, and for each a negative
test, rejected in the kernel (rule R9 of `lean-certify`: a gate never
watched failing does not count).
-/
import MALL.Run
import MALL.Tactic

namespace MALL.RunTest

open ProofTools ProofTools.Explore MALL

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2

/-! ## For a derivation: a tree of moves, and a script -/

/-- `⊢ p ⊗ ⊤, p⊥, q, r`, by the tree of moves the lazy search returns: the
⊗ move names the split, `p⊥` with `p`, and the ⊤ of the second premise has
`q, r`, which it took back. -/
def topSlack : Fam [p ⊗ ⊤, pᗮ, q, r] :=
  treeCert.verdict _ (.mk (.tensor p ⊤ [pᗮ]) [.mk (.ax p) [], .mk .top []])

-- The lazy search's own tree for it is that tree, and so is the proved
-- search's.  (Compiled evaluation: the lazy search is `partial`, and the
-- kernel does not run it.)
#guard proveLazy [p ⊗ ⊤, pᗮ, q, r] ==
  some (.mk (.tensor p ⊤ [pᗮ]) [.mk (.ax p) [], .mk .top []])
#guard proveSearch [p ⊗ ⊤, pᗮ, q, r] ==
  some (.mk (.tensor p ⊤ [pᗮ]) [.mk (.ax p) [], .mk .top []])

/-- Two tensors: `⊢ p ⊗ q, q⊥ ⊗ r, p⊥, r⊥`, by the lazy search's tree. -/
def twoTensors : Fam [p ⊗ q, qᗮ ⊗ r, pᗮ, rᗮ] :=
  treeCert.verdict _ (.mk (.tensor p q [pᗮ]) [.mk (.ax p) [],
    .mk (.tensor qᗮ r [q]) [.mk (.ax qᗮ) [], .mk (.ax r) []]])

#guard proveLazy [p ⊗ q, qᗮ ⊗ r, pᗮ, rᗮ] ==
  some (.mk (.tensor p q [pᗮ]) [.mk (.ax p) [],
    .mk (.tensor qᗮ r [q]) [.mk (.ax qᗮ) [], .mk (.ax r) []]])

/-- The same derivation by its script. -/
def twoTensors' : Fam [p ⊗ q, qᗮ ⊗ r, pᗮ, rᗮ] :=
  scriptCert.verdict _ [⟨0, .tensor p q [pᗮ]⟩, ⟨0, .ax p⟩, ⟨0, .tensor qᗮ r [q]⟩,
    ⟨0, .ax qᗮ⟩, ⟨0, .ax r⟩]

/-- A wrong split in the tree: `r⊥` given to the first premise.  Rejected. -/
theorem bad_split_rejected :
    treeCert.check [p ⊗ q, qᗮ ⊗ r, pᗮ, rᗮ] (.mk (.tensor p q [pᗮ, rᗮ]) [.mk (.ax p) [],
      .mk (.tensor qᗮ r [q]) [.mk (.ax qᗮ) [], .mk (.ax r) []]]) = false := by
  decide +kernel

/-- A split that names a formula twice where the sequent has it once (a
contraction).  Rejected. -/
theorem contraction_rejected :
    treeCert.check [p ⊗ p, pᗮ] (.mk (.tensor p p [pᗮ]) [.mk (.ax p) [], .mk (.ax p) []])
      = false := by
  decide +kernel

/-- A ⊤ move where there is no ⊤, and an axiom with a formula left over (a
weakening).  Rejected. -/
theorem weakening_rejected :
    treeCert.check [p, pᗮ, q] (.mk (.ax p) []) = false := by
  decide +kernel

/-- A tree of moves that stops early.  Rejected. -/
theorem short_cert_rejected :
    treeCert.check [p ⊗ q, qᗮ ⊗ r, pᗮ, rᗮ] (.mk (.tensor p q [pᗮ]) [.mk (.ax p) []]) = false := by
  decide +kernel

/-- A script with a wrong line, and one that stops early.  Rejected. -/
theorem bad_script_rejected :
    scriptCert.check [p ⊗ q, qᗮ ⊗ r, pᗮ, rᗮ] [⟨0, .tensor p q [pᗮ]⟩, ⟨0, .ax p⟩,
      ⟨0, .tensor qᗮ r []⟩, ⟨0, .ax qᗮ⟩, ⟨0, .ax r⟩] = false := by
  decide +kernel

theorem short_script_rejected :
    scriptCert.check [p ⊗ q, qᗮ ⊗ r, pᗮ, rᗮ] [⟨0, .tensor p q [pᗮ]⟩, ⟨0, .ax p⟩,
      ⟨0, .tensor qᗮ r [q]⟩, ⟨0, .ax qᗮ⟩] = false := by
  decide +kernel

/-! ## Against derivability and validity: the decision, run by the kernel -/

/-- `⊢ 1, 1` has no derivation. -/
theorem one_one : ¬ Derivable [𝟏, 𝟏] := noDerivable.verdict _ ()

/-- Nor is it valid. -/
theorem one_one_not_valid : ¬ Valid [𝟏, 𝟏] := noValid.verdict _ ()

/-- "A ⊸ A ⊗ A is not derivable" (Girard, p. 5). -/
theorem p5 : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] := noDerivable.verdict _ ()

/-- The check against derivability does not accept a derivable sequent:
here, each of four. -/
theorem derivable_not_accepted :
    ([[p, pᗮ], [𝟏], [pᗮ ⅋ (p & p)], [p ⊗ q, qᗮ ⊗ r, pᗮ, rᗮ]].all
      fun Γ => !noDerivable.check Γ ()) = true := by
  decide +kernel

/-! ## The axioms of the facts -/

#certify_axioms MALL.RunTest.topSlack
#certify_axioms MALL.RunTest.twoTensors
#certify_axioms MALL.RunTest.twoTensors'
#certify_axioms MALL.RunTest.one_one
#certify_axioms MALL.RunTest.one_one_not_valid
#certify_axioms MALL.RunTest.p5

/-! ## One side always answers, on these -/

example : (∃ c, treeCert.check [𝟏, 𝟏] c = true) ∨ noDerivable.check [𝟏, 𝟏] () = true :=
  decided _

/-! ## The producer, three-valued -/

#guard (produce [p ⊗ ⊤, pᗮ, q, r] 0 matches .pass _)
#guard (produce [𝟏, 𝟏] 0 matches .fail _)

end MALL.RunTest
