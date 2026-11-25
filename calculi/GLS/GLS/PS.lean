/-
Goal 5: GLS and PSGLS derive the same sequents.

Source: the Coq file `GL/GLS_PSGLS_calcs.v` of `ianshil/CE_GLS` (the two
systems), and `GL/PSGLS_termination.v`, `GL/GLS_der_dec.v` where the
source passes from one to the other.  From GLS to PSGLS, an instance of GLR
whose conclusion is an instance of IdP, BotL or IdB is replaced by that
axiom of PSGLS: which it is, is decided as data.  From PSGLS to GLS, IdB is
the identity on a boxed formula (`Fam.id`).  Theory file: it ends with its
bound on axioms.
-/
import GLS.Search

namespace GLS

/-- **From GLS to PSGLS**, by matching on the derivation.  At GLR: the
axiom of PSGLS of which the conclusion is an instance, if it is one; PSGLR
if it is none. -/
def Fam.toPS : {s : Seq} → Fam s → PSFam s
  | _, .idP p hΓ hΔ => .idP p hΓ hΔ
  | _, .botL h => .botL h
  | _, .impR A B h d => .impR A B h d.toPS
  | _, .impL A B h d₁ d₂ => .impL A B h d₁.toPS d₂.toPS
  | _, @Fam.glr Γ Δ A h d =>
      match hP : findIdP Γ Δ with
      | some p => .idP p (findIdP_some hP).1 (findIdP_some hP).2
      | none =>
        if hBot : ⊥ ∈ Γ then .botL hBot else
        match hB : findIdB Γ Δ with
        | some B => .idB B (findIdB_some hB).1 (findIdB_some hB).2
        | none => .glr A (findIdP_none hP) (findIdB_none hB) hBot h d.toPS

/-- **From PSGLS to GLS**, by matching on the derivation.  IdB is the
identity on a boxed formula. -/
def PSFam.toFam : {s : Seq} → PSFam s → Fam s
  | _, .idP p hΓ hΔ => .idP p hΓ hΔ
  | _, .idB A hΓ hΔ => Fam.id (□A) hΓ hΔ
  | _, .botL h => .botL h
  | _, .impR A B h d => .impR A B h d.toFam
  | _, .impL A B h d₁ d₂ => .impL A B h d₁.toFam d₂.toFam
  | _, .glr A _ _ _ h d => .glr A h d.toFam

/-- **Goal 5, the two systems derive the same sequents.** -/
def psEquivalent : PSEquivalent := fun _ => (Fam.toPS, PSFam.toFam)

end GLS

#axioms_within_file [propext, Quot.sound]
