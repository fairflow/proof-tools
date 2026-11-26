/-
The invertible rules of dual intuitionistic linear logic, each by one
admissible cut against a small derivation (CCP Lemma 6), and the two
deduction theorems.

⊗L, 1L, ⊸R, &R, ⊕L and !L are invertible; !R is invertible where the
linear zone is empty, which its conclusion asks.  Theory file: it ends
with its bound on axioms.
-/
import DILL.Cut

namespace DILL

open List

namespace Cut

/-- `Γ ; A ⟹ A`. -/
def idn (Γ : List Form) (A : Form) : CF (Γ ⨾ [A] ⟹ A) := .init A (.refl _)

end Cut

open Cut in
/-- **⊗L is invertible**: a cut against `Γ ; A, B ⟹ A ⊗ B`. -/
def tensorLInv : TensorLInv := fun Γ Δ A B C d =>
  cutAdmissible Γ [A, B] Δ (A ⊗ B) C (.tensorR [A] [B] (.refl _) (idn Γ A) (idn Γ B)) d

/-- **1L is invertible**: a cut against `Γ ; · ⟹ 1`. -/
def oneLInv : OneLInv := fun Γ Δ C d =>
  cutAdmissible Γ [] Δ 𝟏 C (.oneR (.refl _)) d

open Cut in
/-- **⊸R is invertible**: a cut against `Γ ; A ⊸ B, A ⟹ B`. -/
def lolliRInv : LolliRInv := fun Γ Δ A B d =>
  (cutAdmissible Γ Δ [A] (A ⊸ B) B d
    (.lolliL A B [A] [] (.refl _) (idn Γ A) (idn Γ B))).exch (by perm_count [])

open Cut in
/-- **&R is invertible**: cuts against `Γ ; A & B ⟹ A` and
`Γ ; A & B ⟹ B`. -/
def withRInv : WithRInv := fun Γ Δ A B d =>
  ((cutAdmissible Γ Δ [] (A & B) A d (.withL₁ A B [] (.refl _) (idn Γ A))).exch
      (by perm_count []),
   (cutAdmissible Γ Δ [] (A & B) B d (.withL₂ A B [] (.refl _) (idn Γ B))).exch
      (by perm_count []))

open Cut in
/-- **⊕L is invertible**: cuts against `Γ ; A ⟹ A ⊕ B` and
`Γ ; B ⟹ A ⊕ B`. -/
def plusLInv : PlusLInv := fun Γ Δ A B C d =>
  (cutAdmissible Γ [A] Δ (A ⊕ B) C (.plusR₁ (idn Γ A)) d,
   cutAdmissible Γ [B] Δ (A ⊕ B) C (.plusR₂ (idn Γ B)) d)

open Cut in
/-- **!L is invertible**: after weakening by `A`, a cut against
`Γ, A ; · ⟹ !A`. -/
def bangLInv : BangLInv := fun Γ Δ A C d =>
  cutAdmissible (A :: Γ) [] Δ (!A) C
    (.bangR (.refl _) (.copy A (.head _) (idn (A :: Γ) A))) (d.weakenU A)

open Cut in
/-- **!R is invertible at an empty linear zone**: a cut against
`Γ ; !A ⟹ A`. -/
def bangRInv : BangRInv := fun Γ A d =>
  cutAdmissible Γ [] [] (!A) A d
    (.bangL A [] (.refl _) (.copy A (.head _) (idn (A :: Γ) A)))

/-- **The deduction theorem for a linear hypothesis**: ⊸R one way, its
inversion the other. -/
theorem deductionLinear : DeductionLinear := fun Γ Δ A B =>
  ⟨fun ⟨d⟩ => ⟨.lolliR d⟩,
   fun ⟨d⟩ => ⟨(lolliRInv Γ Δ A B (cutElimination _ d)).lift⟩⟩

/-- **The deduction theorem for a valid hypothesis**: !L one way, its
inversion the other. -/
theorem deductionUnrestricted : DeductionUnrestricted := fun Γ Δ A C =>
  ⟨fun ⟨d⟩ => ⟨.bangL A Δ (.refl _) d⟩,
   fun ⟨d⟩ => ⟨(bangLInv Γ Δ A C (cutElimination _ d)).lift⟩⟩

/-! ## Tests -/

#eval (tensorLInv [] [] (.atom 0) (.atom 1) (.atom 0 ⊗ .atom 1)
  (.tensorL (.atom 0) (.atom 1) [] (.refl _)
    (.tensorR [.atom 0] [.atom 1] (.refl _) (Cut.idn _ _) (Cut.idn _ _)))).height
#eval (bangLInv [] [] (.atom 0) (.atom 0)
  (.bangL (.atom 0) [] (.refl _) (.copy (.atom 0) (.head _) (Cut.idn _ _)))).height

end DILL

#axioms_within_file [propext, Quot.sound]
