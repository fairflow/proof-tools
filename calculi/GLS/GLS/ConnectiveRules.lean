/-
The rules that the defined connectives of `GLS/Connectives.lean` obtain in
GLS: a left and a right rule for each of `∧`, `∨`, `¬`, `⊤`, `◇`, with
their inverses; the exchange of sides by negation; and the reading of a
sequent as one formula, `⋀Γ → ⋁Δ`.

Each rule below is **derived**: a derivation of its conclusion is built
from derivations of its premises by rules of GLS, with at most a
height-preserving weakening by `⊥` on the right (`GLS/Structural.lean`).
Each inverse is **admissible**: it uses the inversion of ImpR and ImpL
(`GLS/Invert.lean`), and, to remove a `⊥` from a succedent, the source's
cut (`GLS/Cut.lean`).  Theory file: it ends with its bound on axioms.
-/
import GLS.Interpolation
import GLS.Invert
import GLS.Cut

namespace GLS

/-! ## The rules of GLS with the principal formula first -/

/-- ImpR, with the implication first in the succedent. -/
def Fam.impRHead (A B : Form) {Γ Δ : List Form} (d : Fam (A :: Γ ⇒ B :: Δ)) :
    Fam (Γ ⇒ (A ⟶ B) :: Δ) :=
  .impR A B (List.mem_cons_self ..) (by rw [List.erase_cons_head]; exact d)

/-- ImpL, with the implication first in the antecedent. -/
def Fam.impLHead (A B : Form) {Γ Δ : List Form} (d₁ : Fam (Γ ⇒ A :: Δ))
    (d₂ : Fam (B :: Γ ⇒ Δ)) : Fam ((A ⟶ B) :: Γ ⇒ Δ) :=
  .impL A B (List.mem_cons_self ..) (by rw [List.erase_cons_head]; exact d₁)
    (by rw [List.erase_cons_head]; exact d₂)

/-- BotL, with `⊥` first. -/
def Fam.botHead {Γ Δ : List Form} : Fam (⊥ :: Γ ⇒ Δ) := .botL (List.mem_cons_self ..)

/-- Weakening by `⊥` on the right, first. -/
def Fam.wkBot {Γ Δ : List Form} (d : Fam (Γ ⇒ Δ)) : Fam (Γ ⇒ ⊥ :: Δ) :=
  (d.wk [] [⊥] _ _ (by perm_count []) (by perm_count [])).1

/-- Exchange of the first two formulas of the antecedent. -/
def Fam.swapL {A B : Form} {Γ Δ : List Form} (d : Fam (A :: B :: Γ ⇒ Δ)) :
    Fam (B :: A :: Γ ⇒ Δ) :=
  (d.le.ex (by perm_count []) (.refl _)).1

/-- **`⊥` on the right can be removed** (admissible: a cut on `⊥` with
BotL). -/
def Fam.botRElim {Γ Δ : List Form} (d : Fam (Γ ⇒ ⊥ :: Δ)) : Fam (Γ ⇒ Δ) :=
  cutBySource ⊥ [] Γ [] Δ d Fam.botHead

/-! ## The derived rules -/

/-- **¬L**: from `Γ ⇒ A, Δ` to `¬A, Γ ⇒ Δ`. -/
def Fam.negL (A : Form) {Γ Δ : List Form} (d : Fam (Γ ⇒ A :: Δ)) : Fam (A.neg :: Γ ⇒ Δ) :=
  Fam.impLHead A ⊥ d Fam.botHead

/-- **¬R**: from `A, Γ ⇒ Δ` to `Γ ⇒ ¬A, Δ`. -/
def Fam.negR (A : Form) {Γ Δ : List Form} (d : Fam (A :: Γ ⇒ Δ)) : Fam (Γ ⇒ A.neg :: Δ) :=
  Fam.impRHead A ⊥ d.wkBot

/-- **⊤R**: `Γ ⇒ ⊤, Δ`. -/
def Fam.topR {Γ Δ : List Form} : Fam (Γ ⇒ Form.top :: Δ) := Fam.impRHead ⊥ ⊥ Fam.botHead

/-- **∧L**: from `A, B, Γ ⇒ Δ` to `A ∧ B, Γ ⇒ Δ`. -/
def Fam.andL (A B : Form) {Γ Δ : List Form} (d : Fam (A :: B :: Γ ⇒ Δ)) :
    Fam ((A ⋏ B) :: Γ ⇒ Δ) :=
  Fam.impLHead (A ⟶ (B ⟶ ⊥)) ⊥ (Fam.impRHead A (B ⟶ ⊥) (Fam.impRHead B ⊥ d.swapL.wkBot))
    Fam.botHead

/-- **∧R**: from `Γ ⇒ A, Δ` and `Γ ⇒ B, Δ` to `Γ ⇒ A ∧ B, Δ`: two premises,
on the right. -/
def Fam.andR (A B : Form) {Γ Δ : List Form} (d₁ : Fam (Γ ⇒ A :: Δ)) (d₂ : Fam (Γ ⇒ B :: Δ)) :
    Fam (Γ ⇒ (A ⋏ B) :: Δ) :=
  Fam.impRHead (A ⟶ (B ⟶ ⊥)) ⊥
    (Fam.impLHead A (B ⟶ ⊥) ((d₁.wk [] [⊥] Γ (A :: ⊥ :: Δ) (by perm_count []) (by perm_count [])).1)
      (Fam.impLHead B ⊥ ((d₂.wk [] [⊥] Γ (B :: ⊥ :: Δ) (by perm_count []) (by perm_count [])).1)
        Fam.botHead))

/-- **∨L**: from `A, Γ ⇒ Δ` and `B, Γ ⇒ Δ` to `A ∨ B, Γ ⇒ Δ`: two premises,
on the left. -/
def Fam.orL (A B : Form) {Γ Δ : List Form} (d₁ : Fam (A :: Γ ⇒ Δ)) (d₂ : Fam (B :: Γ ⇒ Δ)) :
    Fam ((A ⋎ B) :: Γ ⇒ Δ) :=
  Fam.impLHead (A ⟶ ⊥) B (Fam.impRHead A ⊥ d₁.wkBot) d₂

/-- **∨R**: from `Γ ⇒ A, B, Δ` to `Γ ⇒ A ∨ B, Δ`. -/
def Fam.orR (A B : Form) {Γ Δ : List Form} (d : Fam (Γ ⇒ A :: B :: Δ)) :
    Fam (Γ ⇒ (A ⋎ B) :: Δ) :=
  Fam.impRHead (A ⟶ ⊥) B (Fam.impLHead A ⊥ d Fam.botHead)

/-- **◇L**, the dual of GLR: from `A, xbox Γ, □¬A ⇒` to `◇A, Γ ⇒ Δ`.  The
premise carries `□¬A`: the diamond's witness can be taken to be a last
world where `A` holds. -/
def Fam.diaL (A : Form) {Γ Δ : List Form} (d : Fam (A :: (xbox Γ ++ [□(A ⟶ ⊥)]) ⇒ [])) :
    Fam (A.dia :: Γ ⇒ Δ) :=
  Fam.impLHead (□(A ⟶ ⊥)) ⊥
    (.glr (A ⟶ ⊥) (List.mem_cons_self ..) (Fam.impRHead A ⊥ d.wkBot))
    Fam.botHead

/-- **◇R**: from `□¬A, Γ ⇒ Δ` to `Γ ⇒ ◇A, Δ`.  A diamond on the right is a
box on the left, and GLS acts on a boxed antecedent formula only as side
formula of GLR: so no rule of the modal kind is to be had here. -/
def Fam.diaR (A : Form) {Γ Δ : List Form} (d : Fam (□A.neg :: Γ ⇒ Δ)) : Fam (Γ ⇒ A.dia :: Δ) :=
  Fam.impRHead (□(A ⟶ ⊥)) ⊥ d.wkBot

/-! ## The inverses, admissible -/

/-- The inverse of ¬L. -/
def Fam.negLInv (A : Form) {Γ Δ : List Form} (d : Fam (A.neg :: Γ ⇒ Δ)) : Fam (Γ ⇒ A :: Δ) :=
  (d.invL A ⊥ Γ (.refl _)).1.1

/-- The inverse of ¬R. -/
def Fam.negRInv (A : Form) {Γ Δ : List Form} (d : Fam (Γ ⇒ A.neg :: Δ)) : Fam (A :: Γ ⇒ Δ) :=
  (d.invR A ⊥ Δ (.refl _)).1.botRElim

/-- The inverse of ∧L. -/
def Fam.andLInv (A B : Form) {Γ Δ : List Form} (d : Fam ((A ⋏ B) :: Γ ⇒ Δ)) :
    Fam (A :: B :: Γ ⇒ Δ) :=
  let d₁ := (d.invL (A ⟶ (B ⟶ ⊥)) ⊥ Γ (.refl _)).1.1
  let d₂ := (d₁.invR A (B ⟶ ⊥) Δ (.refl _)).1
  let d₃ := (d₂.invR B ⊥ Δ (.refl _)).1
  d₃.botRElim.swapL

/-- The inverses of ∧R. -/
def Fam.andRInv (A B : Form) {Γ Δ : List Form} (d : Fam (Γ ⇒ (A ⋏ B) :: Δ)) :
    Fam (Γ ⇒ A :: Δ) × Fam (Γ ⇒ B :: Δ) :=
  let d₁ := (d.invR (A ⟶ (B ⟶ ⊥)) ⊥ Δ (.refl _)).1.botRElim
  let p := d₁.invL A (B ⟶ ⊥) Γ (.refl _)
  (p.1.1, (p.2.1.invL B ⊥ Γ (.refl _)).1.1)

/-- The inverses of ∨L. -/
def Fam.orLInv (A B : Form) {Γ Δ : List Form} (d : Fam ((A ⋎ B) :: Γ ⇒ Δ)) :
    Fam (A :: Γ ⇒ Δ) × Fam (B :: Γ ⇒ Δ) :=
  let p := d.invL (A ⟶ ⊥) B Γ (.refl _)
  (Fam.negRInv A p.1.1, p.2.1)

/-- The inverse of ∨R. -/
def Fam.orRInv (A B : Form) {Γ Δ : List Form} (d : Fam (Γ ⇒ (A ⋎ B) :: Δ)) :
    Fam (Γ ⇒ A :: B :: Δ) :=
  Fam.negLInv A (d.invR (A ⟶ ⊥) B Δ (.refl _)).1

/-- The inverse of ◇R. -/
def Fam.diaRInv (A : Form) {Γ Δ : List Form} (d : Fam (Γ ⇒ A.dia :: Δ)) : Fam (□A.neg :: Γ ⇒ Δ) :=
  (d.invR (□(A ⟶ ⊥)) ⊥ Δ (.refl _)).1.botRElim

/-! ## Changing sides -/

/-- **A formula changes sides by negation**, both ways: `Γ ⇒ A, Δ` is
derivable iff `¬A, Γ ⇒ Δ` is. -/
def switchRL (A : Form) {Γ Δ : List Form} : (Fam (Γ ⇒ A :: Δ) → Fam (A.neg :: Γ ⇒ Δ)) ×
    (Fam (A.neg :: Γ ⇒ Δ) → Fam (Γ ⇒ A :: Δ)) :=
  (Fam.negL A, Fam.negLInv A)

/-- **And from left to right**: `A, Γ ⇒ Δ` is derivable iff `Γ ⇒ ¬A, Δ` is. -/
def switchLR (A : Form) {Γ Δ : List Form} : (Fam (A :: Γ ⇒ Δ) → Fam (Γ ⇒ A.neg :: Δ)) ×
    (Fam (Γ ⇒ A.neg :: Δ) → Fam (A :: Γ ⇒ Δ)) :=
  (Fam.negR A, Fam.negRInv A)

/-! ## A sequent read as one formula -/

theorem refuted_formula {Γ Δ : List Form} {t : Tree} :
    ([] ⇒ [conjL Γ ⟶ disjL Δ]).refutedAt t = true ↔ (Γ ⇒ Δ).refutedAt t = true := by
  rw [refutedAt_iff, refutedAt_iff]
  constructor
  · rintro ⟨_, h⟩
    have h1 := h _ (List.mem_singleton.2 rfl)
    rw [holds_imp, Bool.or_eq_false_iff, Bool.not_eq_false'] at h1
    refine ⟨(holds_conjL Γ t).1 h1.1, fun B hB => ?_⟩
    cases hB' : B.holds t with
    | false => rfl
    | true =>
      have := (holds_disjL Δ t).2 ⟨B, hB, hB'⟩
      rw [h1.2] at this; cases this
  · rintro ⟨h1, h2⟩
    refine ⟨(fun _ h => nomatch h), fun B hB => ?_⟩
    rw [List.mem_singleton.1 hB, holds_imp, (holds_conjL Γ t).2 h1]
    cases hd : (disjL Δ).holds t with
    | false => rfl
    | true =>
      obtain ⟨C, hC, hCt⟩ := (holds_disjL Δ t).1 hd
      rw [h2 C hC] at hCt; cases hCt

/-- **The comma is `∧` on the left and `∨` on the right**: `Γ ⇒ Δ` is
derivable iff `⇒ ⋀Γ → ⋁Δ` is (both by the search). -/
def seqFormula (Γ Δ : List Form) :
    (Fam (Γ ⇒ Δ) → Fam ([] ⇒ [conjL Γ ⟶ disjL Δ])) × (Fam ([] ⇒ [conjL Γ ⟶ disjL Δ]) → Fam (Γ ⇒ Δ)) :=
  (fun d => famOfNoRefutation _ fun t h => not_refuted_of_fam d t (refuted_formula.1 h),
   fun d => famOfNoRefutation _ fun t h => not_refuted_of_fam d t (refuted_formula.2 h))

/-! ## The calculus is classical -/

/-- **Peirce's law**, `((p → q) → p) → p`, derived in GLS: the second
succedent formula `p`, kept while `p → q` is proved, is where the
calculus is classical rather than minimal or intuitionistic. -/
def peirce (p q : Nat) : Fam ([] ⇒ [((Form.var p ⟶ Form.var q) ⟶ Form.var p) ⟶ Form.var p]) :=
  Fam.impRHead _ _
    (Fam.impLHead _ _
      (Fam.impRHead _ _ (.idP p (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      (.idP p (List.mem_cons_self ..) (List.mem_cons_self ..)))

end GLS

#axioms_within_file [propext, Quot.sound]
