/-
GLS as a proof system of the explorer: the moves, the function `step`,
the soundness of the moves for the family (S1), and that `step` allows
every instance of every rule (S2).

Theory file: it ends with its bound on axioms.
-/
import ProofTools.Explore
import GLS.System

namespace GLS

open ProofTools ProofTools.Explore

/-- **A move**: a rule of GLS, named by its principal formula. -/
inductive Move where
  /-- IdP on the variable numbered `p`. -/
  | idP (p : Nat)
  /-- BotL. -/
  | botL
  /-- ImpR on an occurrence of `A ⟶ B` in the succedent. -/
  | impR (A B : Form)
  /-- ImpL on an occurrence of `A ⟶ B` in the antecedent. -/
  | impL (A B : Form)
  /-- GLR on an occurrence of `□A` in the succedent. -/
  | glr (A : Form)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- What a move asks of a sequent, what it leaves, and what to say when it
does not apply. -/
structure Rule where
  /-- The side conditions hold. -/
  ok : Bool
  /-- The premises. -/
  prems : List Seq
  /-- What to say when they do not. -/
  why : String

/-- **The rule of a move at a sequent**: the side conditions and the
premises are those of the constructor of `Fam` of the same name. -/
def Move.rule (j : Seq) : Move → Rule
  | .idP p => ⟨decide (Form.var p ∈ j.ant) && decide (Form.var p ∈ j.suc), [],
      "IdP: the variable is not on both sides of the sequent"⟩
  | .botL => ⟨decide (⊥ ∈ j.ant), [], "BotL: ⊥ is not in the antecedent"⟩
  | .impR A B => ⟨decide (A ⟶ B ∈ j.suc), [A :: j.ant ⇒ B :: j.suc.erase (A ⟶ B)],
      "ImpR: the implication is not in the succedent"⟩
  | .impL A B => ⟨decide (A ⟶ B ∈ j.ant),
      [j.ant.erase (A ⟶ B) ⇒ A :: j.suc, B :: j.ant.erase (A ⟶ B) ⇒ j.suc],
      "ImpL: the implication is not in the antecedent"⟩
  | .glr A => ⟨decide (□A ∈ j.suc), [xbox j.ant ++ [□A] ⇒ [A]],
      "GLR: the boxed formula is not in the succedent"⟩

/-- **One step**: the premises of the move at the sequent, or why it does
not apply. -/
def step (m : Move) (j : Seq) : Except String (List Seq) :=
  if (m.rule j).ok then .ok (m.rule j).prems else .error (m.rule j).why

/-- **GLS as a proof system.** -/
abbrev S : ProofSystem where
  Judg := Seq
  Move := Move
  step := step

theorem step_of {m : Move} {j : Seq} (h : (m.rule j).ok = true) :
    S.step m j = .ok (m.rule j).prems := by
  show step m j = _
  simp [step, h]

theorem step_ok {m : Move} {j : Seq} {ps : List Seq} (h : S.step m j = .ok ps) :
    (m.rule j).ok = true ∧ ps = (m.rule j).prems := by
  have h' : step m j = .ok ps := h
  unfold step at h'
  split at h'
  · next hok => exact ⟨hok, (Except.ok.inj h').symm⟩
  · cases h'

/-- **S1.  The soundness of the moves**: each move that applies is a rule
of `Fam`, applied to the derivations of its premises.  This is not the
source's soundness theorem. -/
def step_sound : S.SoundT Fam := fun m j _ h e =>
  have hok : (m.rule j).ok = true := (step_ok h).1
  let e' : Each Fam (m.rule j).prems := (step_ok h).2 ▸ e
  match m, j, hok, e' with
  | .idP p, ⟨_, _⟩, hok, _ =>
      .idP p (of_decide_eq_true (Bool.and_eq_true_iff.1 hok).1)
        (of_decide_eq_true (Bool.and_eq_true_iff.1 hok).2)
  | .botL, ⟨_, _⟩, hok, _ => .botL (of_decide_eq_true hok)
  | .impR A B, ⟨_, _⟩, hok, e' => .impR A B (of_decide_eq_true hok) e'.1
  | .impL A B, ⟨_, _⟩, hok, e' => .impL A B (of_decide_eq_true hok) e'.1 e'.2.1
  | .glr A, ⟨_, _⟩, hok, e' => .glr A (of_decide_eq_true hok) e'.1

/-- **The map out**: a derivation of the proof system, as a derivation of
GLS as the source states it. -/
def famOfDer {j : Seq} (d : Der S j) : Fam j := Der.mapOut step_sound d

/-- There is a derivation in GLS. -/
def Derivable (j : Seq) : Prop := Nonempty (Fam j)

theorem step_sound_derivable : S.Sound Derivable := step_sound.nonempty

/-- **S2**, the statement: every derivation of the family is one of the
proof system. -/
def FamToDer : Prop := ∀ j : Seq, Fam j → Nonempty (Der S j)

/-- **S2**: `step` allows every instance of every rule.  A node for each
constructor. -/
theorem famToDer : FamToDer := by
  intro j d
  induction d with
  | idP p hΓ hΔ =>
    exact ⟨.node (.idP p) _ (step_of (by simp [Move.rule, hΓ, hΔ])) .nil⟩
  | botL h =>
    exact ⟨.node .botL _ (step_of (by simp [Move.rule, h])) .nil⟩
  | impR A B h _ ih =>
    let ⟨d⟩ := ih
    exact ⟨.node (.impR A B) _ (step_of (by simp [Move.rule, h])) (.cons d .nil)⟩
  | impL A B h _ _ ih₁ ih₂ =>
    let ⟨d₁⟩ := ih₁
    let ⟨d₂⟩ := ih₂
    exact ⟨.node (.impL A B) _ (step_of (by simp [Move.rule, h])) (.cons d₁ (.cons d₂ .nil))⟩
  | glr A h _ ih =>
    let ⟨d⟩ := ih
    exact ⟨.node (.glr A) _ (step_of (by simp [Move.rule, h])) (.cons d .nil)⟩

end GLS

#axioms_within_file [propext, Quot.sound]
