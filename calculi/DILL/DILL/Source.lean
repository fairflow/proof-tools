/-
Derivations of what the sources assert, as terms of the family `Fam`:
each written with the family's constructors, and with no tactic of the
explorer.

Sources: CCP (Chang, Chaudhuri, Pfenning, CMU-CS-03-131R), pp. 16-18, for
the derivations it draws or describes; the usual laws of `!`, which the
sources assert and do not draw (the campaign's choice, `campaign/plan.md`,
Q4).  This file is a check of the transcription: it imports the theory
file only.  Theory file: it ends with its bound on axioms.

A derivation is at arbitrary formulas `A B` and an arbitrary unrestricted
zone `Γ` where the source's is; the laws of `!` are at the empty zone, as
they are stated.  `CF` where no cut is used.
-/
import DILL.System

namespace DILL

open List

namespace Source

variable {Γ Δ : List Form} {A B : Form}

/-! ## The derivations of CCP, pp. 16-18 -/

/-- CCP p. 16: `Γ, A ; · ⟹ A`, by init and then copy.  The valid
hypothesis is copied into the linear zone, where init uses it. -/
def copyInit : CF (A :: Γ ⨾ [] ⟹ A) :=
  .copy A (.head _)                    -- Γ, A ; A ⟹ A
    (.init A (.refl _))

/-- The same at any member of the unrestricted zone: the figure's `Γ, A`
is read through membership. -/
def copyInitMem (h : A ∈ Γ) : CF (Γ ⨾ [] ⟹ A) :=
  .copy A h (.init A (.refl _))

/-- CCP p. 16: `Γ ; A, A ⊸ B ⟹ B`, by init twice and ⊸L.  The linear
zone of the first premise is `A`, that of the second is empty. -/
def modusPonens : CF (Γ ⨾ [A, A ⊸ B] ⟹ B) :=
  .lolliL A B [A] [] (.swap _ _ _)
    (.init A (.refl _))                -- Γ ; A ⟹ A
    (.init B (.refl _))                -- Γ ; B ⟹ B

/-- CCP p. 17: `Γ ; A & B ⟹ A`, by init and &L₁. -/
def withFst : CF (Γ ⨾ [A & B] ⟹ A) :=
  .withL₁ A B [] (.refl _)
    (.init A (.refl _))                -- Γ ; A ⟹ A

/-- The other projection, `Γ ; A & B ⟹ B`, by init and &L₂. -/
def withSnd : CF (Γ ⨾ [A & B] ⟹ B) :=
  .withL₂ A B [] (.refl _)
    (.init B (.refl _))

/-- CCP p. 18, the inversion of ⊸R by cut (Lemma 6): from a derivation of
`Γ ; Δ ⟹ A ⊸ B`, a derivation with cut of `Γ ; Δ, A ⟹ B`.  The cut is on
`A ⊸ B`, against `Γ ; A ⊸ B, A ⟹ B`, which is `modusPonens` with the two
hypotheses in the other order. -/
def lolliRInv (d : Fam true (Γ ⨾ Δ ⟹ A ⊸ B)) : Fam true (Γ ⨾ A :: Δ ⟹ B) :=
  .cut rfl (A ⊸ B) Δ [A] (perm_append_singleton A Δ).symm
    d                                  -- Γ ; Δ ⟹ A ⊸ B
    (.lolliL A B [A] [] (.refl _)      -- Γ ; A ⊸ B, A ⟹ B
      (.init A (.refl _))
      (.init B (.refl _)))

/-! ## The laws of `!`

Derivations of what the sources assert and do not draw (Barber's
Lemma 2.3 is the equivalence of `!` with the unrestricted zone; the laws
are the usual ones).  Each begins with !L, which moves `A` to the
unrestricted zone; from there `A` is copied as often as it is wanted, or
not at all. -/

/-- `· ; !A ⟹ A` (dereliction): !L, then `copyInit`. -/
def bangDerelict : CF ([] ⨾ [!A] ⟹ A) :=
  .bangL A [] (.refl _)                -- A ; · ⟹ A
    (.copy A (.head _) (.init A (.refl _)))

/-- `· ; !A ⟹ !!A` (digging): after !L the linear zone is empty, so !R
applies, twice. -/
def bangDig : CF ([] ⨾ [!A] ⟹ !(!A)) :=
  .bangL A [] (.refl _)                -- A ; · ⟹ !!A
    (.bangR (.refl _)                  -- A ; · ⟹ !A
      (.bangR (.refl _)                -- A ; · ⟹ A
        (.copy A (.head _) (.init A (.refl _)))))

/-- `· ; !A ⟹ !A ⊗ !A` (contraction): the valid hypothesis `A` is in both
premises of ⊗R, and the linear zone divided is empty. -/
def bangContract : CF ([] ⨾ [!A] ⟹ (!A) ⊗ (!A)) :=
  .bangL A [] (.refl _)                -- A ; · ⟹ !A ⊗ !A
    (.tensorR [] [] (.refl _)
      (.bangR (.refl _) (.copy A (.head _) (.init A (.refl _))))
      (.bangR (.refl _) (.copy A (.head _) (.init A (.refl _)))))

/-- `· ; !A ⟹ 1` (weakening): the valid hypothesis `A` is not used. -/
def bangWeaken : CF ([] ⨾ [!A] ⟹ 𝟏) :=
  .bangL A [] (.refl _)                -- A ; · ⟹ 1
    (.oneR (.refl _))

/-- `· ; !(A & B) ⟹ !A ⊗ !B`: `A & B` is copied once for each premise of
⊗R, and projected. -/
def bangWithTensor : CF ([] ⨾ [!(A & B)] ⟹ (!A) ⊗ (!B)) :=
  .bangL (A & B) [] (.refl _)          -- A & B ; · ⟹ !A ⊗ !B
    (.tensorR [] [] (.refl _)
      (.bangR (.refl _)                -- A & B ; · ⟹ A
        (.copy (A & B) (.head _) (.withL₁ A B [] (.refl _) (.init A (.refl _)))))
      (.bangR (.refl _)                -- A & B ; · ⟹ B
        (.copy (A & B) (.head _) (.withL₂ A B [] (.refl _) (.init B (.refl _))))))

/-- `· ; !A ⊗ !B ⟹ !(A & B)`: ⊗L, !L twice, and then the linear zone is
empty, so !R applies. -/
def bangTensorWith : CF ([] ⨾ [(!A) ⊗ (!B)] ⟹ !(A & B)) :=
  .tensorL (!A) (!B) [] (.refl _)      -- · ; !A, !B ⟹ !(A & B)
    (.bangL A [!B] (.refl _)           -- A ; !B ⟹ !(A & B)
      (.bangL B [] (.refl _)           -- B, A ; · ⟹ !(A & B)
        (.bangR (.refl _)              -- B, A ; · ⟹ A & B
          (.withR
            (.copy A (.tail _ (.head _)) (.init A (.refl _)))
            (.copy B (.head _) (.init B (.refl _)))))))

/-- `· ; !A, !(A ⊸ B) ⟹ !B` (`!` is a functor, in the form with two
hypotheses): !L twice, !R, then the valid `A ⊸ B` is copied and ⊸L has
`A` from a copy. -/
def bangMap : CF ([] ⨾ [!A, !(A ⊸ B)] ⟹ !B) :=
  .bangL A [!(A ⊸ B)] (.refl _)        -- A ; !(A ⊸ B) ⟹ !B
    (.bangL (A ⊸ B) [] (.refl _)       -- A ⊸ B, A ; · ⟹ !B
      (.bangR (.refl _)                -- A ⊸ B, A ; · ⟹ B
        (.copy (A ⊸ B) (.head _)       -- A ⊸ B, A ; A ⊸ B ⟹ B
          (.lolliL A B [] [] (.refl _)
            (.copy A (.tail _ (.head _)) (.init A (.refl _)))
            (.init B (.refl _))))))

/-! ## The same at letters, and their heights -/

/-- The letter `p`. -/
abbrev p : Form := .atom 0
/-- The letter `q`. -/
abbrev q : Form := .atom 1

example : (copyInit : CF ([p] ⨾ [] ⟹ p)).height = 2 := rfl
example : (modusPonens : CF ([] ⨾ [p, p ⊸ q] ⟹ q)).height = 2 := rfl
example : (bangTensorWith : CF ([] ⨾ [(!p) ⊗ (!q)] ⟹ !(p & q))).height = 7 := rfl
example : (bangMap : CF ([] ⨾ [!p, !(p ⊸ q)] ⟹ !q)).height = 7 := rfl

/-- The inversion of ⊸R, applied: from `· ; · ⟹ p ⊸ p` (⊸R, init) a
derivation with cut of `· ; p ⟹ p`. -/
example : Fam true ([] ⨾ [p] ⟹ p) :=
  lolliRInv (.lolliR (.init p (.refl _)))

/-- A derivation without cut is one of the calculus with cut. -/
example : Fam true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := bangContract.lift

end Source

end DILL

#axioms_within_file [propext, Quot.sound]
