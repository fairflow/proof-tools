/-
Saturated sets of sequents as certificates: the certifiers, and that for
every sequent one of the two written certificates exists.

* `noDerivableBySet.verdict Γ D : ¬ Derivable Γ` and
  `noValidBySet.verdict Γ D : ¬ Valid Γ`: the kernel checks that `Γ` is a
  member of `D` and that `D` is saturated (`MALL/Saturated.lean`).  The
  finite phase structure that `D` presents refutes `Γ`
  (`countermodel_of_refutedBy`); the kernel does not compute in it.
* `certified`: every sequent has a tree of moves that checks, or a
  saturated set that checks.  Level 3 of the Run stage, with a written
  certificate on each side.

Theory file: it ends with its bound on axioms.
-/
import MALL.Saturated
import MALL.Run

namespace MALL

open ProofTools ProofTools.Explore

/-- **Saturated sets, checked against derivability.** -/
def noDerivableBySet :
    Certify.Certifier (List Form) (List (List Form)) (fun Γ => Derivable Γ → False) where
  check Γ D := refutedBy D Γ
  sound _ _ h := not_derivable_of_refutedBy h

/-- The same against validity. -/
def noValidBySet :
    Certify.Certifier (List Form) (List (List Form)) (fun Γ => Valid Γ → False) where
  check Γ D := refutedBy D Γ
  sound _ _ h := not_valid_of_refutedBy h

#certify_structural MALL.noDerivableBySet
#certify_statement MALL.noDerivableBySet
#certify_structural MALL.noValidBySet
#certify_statement MALL.noValidBySet

/-- **Every sequent has a certificate**: a tree of moves that checks, or a
saturated set of sequents that checks. -/
theorem certified (Γ : List Form) :
    (∃ c, treeCert.check Γ c = true) ∨ (∃ D, noDerivableBySet.check Γ D = true) := by
  by_cases h : Derivable Γ
  · obtain ⟨d⟩ := h
    obtain ⟨der⟩ := famToDer Γ d
    exact .inl ⟨der.cert, Att.check_cert der⟩
  · exact .inr ⟨fullRefutation Γ, refutation_complete Γ h⟩

end MALL

#axioms_within_file [propext, Quot.sound]
