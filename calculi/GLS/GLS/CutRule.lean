/-
GLS with the cut rule, and the elimination of cut.

Source: I. Shillito, *New Foundations for the Proof Theory of
Bi-Intuitionistic and Provability Logics Mechanized in Coq* (PhD thesis,
ANU, 2023), section 12.4, p. 171: "we recall the additive cut rule …

    Γ ⇒ ∆, ϕ      ϕ, Γ ⇒ ∆
    ─────────────────────── (cut)
            Γ ⇒ ∆

By adding the rule (cut) to GLS, giving us the calculus GLS + (cut) …";
and Theorem 12.7.2, p. 186: "The additive cut rule is eliminable from
GLS + (cut)", in Coq `forall s, (GLS_cut_prv s) -> (GLS_prv s)`.  Theory
file: it ends with its bound on axioms.
-/
import GLS.Completeness
import GLS.Cut

namespace GLS

/-- **GLS + (cut)** (the thesis, p. 171 and p. 186, `GLS_cut_rules`): the
five rules of GLS, and the additive cut. -/
inductive FamCut : Seq → Type where
  /-- IdP. -/
  | idP {Γ Δ : List Form} (p : Nat) (hΓ : Form.var p ∈ Γ) (hΔ : Form.var p ∈ Δ) : FamCut (Γ ⇒ Δ)
  /-- BotL. -/
  | botL {Γ Δ : List Form} (h : ⊥ ∈ Γ) : FamCut (Γ ⇒ Δ)
  /-- ImpR. -/
  | impR {Γ Δ : List Form} (A B : Form) (h : A ⟶ B ∈ Δ)
      (d : FamCut (A :: Γ ⇒ B :: Δ.erase (A ⟶ B))) : FamCut (Γ ⇒ Δ)
  /-- ImpL. -/
  | impL {Γ Δ : List Form} (A B : Form) (h : A ⟶ B ∈ Γ)
      (d₁ : FamCut (Γ.erase (A ⟶ B) ⇒ A :: Δ)) (d₂ : FamCut (B :: Γ.erase (A ⟶ B) ⇒ Δ)) :
      FamCut (Γ ⇒ Δ)
  /-- GLR. -/
  | glr {Γ Δ : List Form} (A : Form) (h : □A ∈ Δ) (d : FamCut (xbox Γ ++ [□A] ⇒ [A])) :
      FamCut (Γ ⇒ Δ)
  /-- (cut), p. 171: from `Γ ⇒ ∆, ϕ` and `ϕ, Γ ⇒ ∆` to `Γ ⇒ ∆`. -/
  | cut {Γ Δ : List Form} (A : Form) (d₁ : FamCut (Γ ⇒ A :: Δ)) (d₂ : FamCut (A :: Γ ⇒ Δ)) :
      FamCut (Γ ⇒ Δ)

#rules GLS.FamCut
#slime GLS.FamCut

/-- **Cut elimination** (the thesis, Theorem 12.7.2), the statement: a
derivation in GLS + (cut) gives a derivation in GLS. -/
abbrev CutElimination : Type := (s : Seq) → FamCut s → Fam s

/-- A derivation of GLS is one of GLS + (cut). -/
def Fam.toCut : {s : Seq} → Fam s → FamCut s
  | _, .idP p hΓ hΔ => .idP p hΓ hΔ
  | _, .botL h => .botL h
  | _, .impR A B h d => .impR A B h d.toCut
  | _, .impL A B h d₁ d₂ => .impL A B h d₁.toCut d₂.toCut
  | _, .glr A h d => .glr A h d.toCut

/-- Cut elimination from a function that makes a cut admissible: by
recursion on the derivation, as in the source ("If the last rule applied
is (cut), then we use the induction hypothesis on both premises and then
Theorem 12.7.1"). -/
def FamCut.elim (cut : CutAdmissible) : {s : Seq} → FamCut s → Fam s
  | _, .idP p hΓ hΔ => .idP p hΓ hΔ
  | _, .botL h => .botL h
  | _, .impR A B h d => .impR A B h (d.elim cut)
  | _, .impL A B h d₁ d₂ => .impL A B h (d₁.elim cut) (d₂.elim cut)
  | _, .glr A h d => .glr A h (d.elim cut)
  | _, @FamCut.cut Γ Δ A d₁ d₂ => cut A [] Γ [] Δ (d₁.elim cut) (d₂.elim cut)

/-- **Cut elimination, by the source's construction**: each cut is removed
by `cutBySource`, which makes its derivation from the two given ones. -/
def cutElimination : CutElimination := fun _ d => d.elim cutBySource

/-- **Cut elimination, by the semantic route**: each cut is removed by
`cutAdmissible`, which searches for a derivation of its conclusion. -/
def cutEliminationBySearch : CutElimination := fun _ d => d.elim cutAdmissible

end GLS

#axioms_within_file [propext, Quot.sound]
