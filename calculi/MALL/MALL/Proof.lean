/-
MALL as a proof system of the explorer: the moves, the function `step`,
the soundness of the moves for the family (S1), and that `step` allows
every instance of every rule (S2).

Theory file: it ends with its bound on axioms.
-/
import ProofTools.Explore
import MALL.System

namespace MALL

open ProofTools ProofTools.Explore List

/-- **A move**: a rule of Definition 1.15, named by its principal formula;
the two rules that split the context (⊗ and cut) also name the context of
their first premise. -/
inductive Move where
  /-- The logical axiom `⊢ A, A⊥`. -/
  | ax (A : Form)
  /-- Cut on `A`, with `Γ` the context of the premise `⊢ A, Γ`; the rest
  of the sequent goes with `A⊥`. -/
  | cut (A : Form) (Γ : List Form)
  /-- The axiom ⊤. -/
  | top
  /-- & on an occurrence of `A & B`. -/
  | wth (A B : Form)
  /-- 1⊕ on an occurrence of `A ⊕ B`. -/
  | plus₁ (A B : Form)
  /-- 2⊕ on an occurrence of `A ⊕ B`. -/
  | plus₂ (A B : Form)
  /-- The axiom `⊢ 1`. -/
  | one
  /-- ⊥ on an occurrence of `⊥`. -/
  | bot
  /-- ⊗ on an occurrence of `A ⊗ B`, with `Γ` the context of the premise
  `⊢ A, Γ`; the rest of the sequent goes with `B`. -/
  | tensor (A B : Form) (Γ : List Form)
  /-- ⅋ on an occurrence of `A ⅋ B`. -/
  | par (A B : Form)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- What a move asks of a sequent, what it leaves, and what to say when it
does not apply. -/
structure Rule where
  /-- The side conditions hold. -/
  ok : Bool
  /-- The premises. -/
  prems : List (List Form)
  /-- What to say when they do not. -/
  why : String

/-- **The rule of a move at a sequent.**  A rule with a principal formula
asks that it be in the sequent, and its premises have the rest
(`List.erase`); a rule that splits asks that the context named be part of
what is to be split, and its second premise has what is left (`sub`). -/
def Move.rule (j : List Form) : Move → Rule
  | .ax A => ⟨permB j [A, Aᗮ], [], "ax: the sequent is not ⊢ A, A⊥"⟩
  | .cut A Γ => ⟨permB j (Γ ++ sub j Γ), [A :: Γ, Aᗮ :: sub j Γ],
      "cut: the context named for the first premise is not part of the sequent"⟩
  | .top => ⟨decide (⊤ ∈ j), [], "⊤: ⊤ is not in the sequent"⟩
  | .wth A B => ⟨decide (A & B ∈ j), [A :: j.erase (A & B), B :: j.erase (A & B)],
      "&: the formula is not in the sequent"⟩
  | .plus₁ A B => ⟨decide ((A ⊕ B) ∈ j), [A :: j.erase (A ⊕ B)],
      "1⊕: the formula is not in the sequent"⟩
  | .plus₂ A B => ⟨decide ((A ⊕ B) ∈ j), [B :: j.erase (A ⊕ B)],
      "2⊕: the formula is not in the sequent"⟩
  | .one => ⟨decide (j = [𝟏]), [], "1: the sequent is not ⊢ 1"⟩
  | .bot => ⟨decide (⊥ ∈ j), [j.erase ⊥], "⊥: ⊥ is not in the sequent"⟩
  | .tensor A B Γ =>
      ⟨decide (A ⊗ B ∈ j) && permB (j.erase (A ⊗ B)) (Γ ++ sub (j.erase (A ⊗ B)) Γ),
        [A :: Γ, B :: sub (j.erase (A ⊗ B)) Γ],
        "⊗: the formula is not in the sequent, or the context named for the first premise \
         is not part of the rest"⟩
  | .par A B => ⟨decide (A ⅋ B ∈ j), [A :: B :: j.erase (A ⅋ B)],
      "⅋: the formula is not in the sequent"⟩

/-- **One step**: the premises of the move at the sequent, or why it does
not apply. -/
def step (m : Move) (j : List Form) : Except String (List (List Form)) :=
  if (m.rule j).ok then .ok (m.rule j).prems else .error (m.rule j).why

/-- **MALL as a proof system.** -/
abbrev S : ProofSystem where
  Judg := List Form
  Move := Move
  step := step

theorem step_of {m : Move} {j : List Form} (h : (m.rule j).ok = true) :
    S.step m j = .ok (m.rule j).prems := by
  show step m j = _
  simp [step, h]

theorem step_ok {m : Move} {j : List Form} {ps : List (List Form)} (h : S.step m j = .ok ps) :
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
  match m, hok, e' with
  | .ax A, hok, _ => .ax A (permB_iff.1 hok)
  | .cut A Γ, hok, e' => .cut A Γ (sub j Γ) (permB_iff.1 hok) e'.1 e'.2.1
  | .top, hok, _ => .top (j.erase ⊤) (perm_cons_erase (of_decide_eq_true hok))
  | .wth A B, hok, e' =>
      .wth A B (j.erase (A & B)) (perm_cons_erase (of_decide_eq_true hok)) e'.1 e'.2.1
  | .plus₁ A B, hok, e' =>
      .plus₁ A B (j.erase (A ⊕ B)) (perm_cons_erase (of_decide_eq_true hok)) e'.1
  | .plus₂ A B, hok, e' =>
      .plus₂ A B (j.erase (A ⊕ B)) (perm_cons_erase (of_decide_eq_true hok)) e'.1
  | .one, hok, _ => .one (of_decide_eq_true hok ▸ .refl _)
  | .bot, hok, e' => .bot (j.erase ⊥) (perm_cons_erase (of_decide_eq_true hok)) e'.1
  | .tensor A B Γ, hok, e' =>
      .tensor A B Γ (sub (j.erase (A ⊗ B)) Γ)
        ((perm_cons_erase (of_decide_eq_true (Bool.and_eq_true_iff.1 hok).1)).trans
          ((permB_iff.1 (Bool.and_eq_true_iff.1 hok).2).cons _))
        e'.1 e'.2.1
  | .par A B, hok, e' =>
      .par A B (j.erase (A ⅋ B)) (perm_cons_erase (of_decide_eq_true hok)) e'.1

/-- **The map out**: a derivation of the proof system, as a derivation of
the calculus. -/
def famOfDer {j : List Form} (d : Der S j) : Fam j := Der.mapOut step_sound d

theorem step_sound_derivable : S.Sound Derivable := step_sound.nonempty

/-- **S2**, the statement: every derivation of the family is one of the
proof system. -/
def FamToDer : Prop := ∀ Γ : List Form, Fam Γ → Nonempty (Der S Γ)

/-- S2, for every permutation of the sequent: the move's premises are
those of the rule up to a permutation, so the induction carries one. -/
theorem famToDer_perm {Ξ : List Form} (d : Fam Ξ) :
    ∀ Ξ' : List Form, Ξ ~ Ξ' → Nonempty (Der S Ξ') := by
  induction d with
  | ax A h =>
    intro Ξ' e
    exact ⟨.node (.ax A) _ (step_of (permB_iff.2 (e.symm.trans h))) .nil⟩
  | cut A Γ Δ h _ _ ih₁ ih₂ =>
    intro Ξ' e
    have hΔ : (sub Ξ' Γ) ~ Δ := sub_perm (e.symm.trans h)
    let ⟨d₁⟩ := ih₁ _ (.refl _)
    let ⟨d₂⟩ := ih₂ (Aᗮ :: sub Ξ' Γ) (hΔ.symm.cons _)
    exact ⟨.node (.cut A Γ) _ (step_of (permB_iff.2 (by perm_count [e, h, hΔ])))
      (.cons d₁ (.cons d₂ .nil))⟩
  | top Γ h =>
    intro Ξ' e
    have hm : ⊤ ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    exact ⟨.node .top _ (step_of (decide_eq_true hm)) .nil⟩
  | wth A B Γ h _ _ ih₁ ih₂ =>
    intro Ξ' e
    have hm : A & B ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase (A & B)) ~ Γ := perm_erase_of_cons (e.symm.trans h)
    let ⟨d₁⟩ := ih₁ (A :: Ξ'.erase (A & B)) (hr.symm.cons _)
    let ⟨d₂⟩ := ih₂ (B :: Ξ'.erase (A & B)) (hr.symm.cons _)
    exact ⟨.node (.wth A B) _ (step_of (decide_eq_true hm)) (.cons d₁ (.cons d₂ .nil))⟩
  | plus₁ A B Γ h _ ih =>
    intro Ξ' e
    have hm : (A ⊕ B) ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase (A ⊕ B)) ~ Γ := perm_erase_of_cons (e.symm.trans h)
    let ⟨d⟩ := ih (A :: Ξ'.erase (A ⊕ B)) (hr.symm.cons _)
    exact ⟨.node (.plus₁ A B) _ (step_of (decide_eq_true hm)) (.cons d .nil)⟩
  | plus₂ A B Γ h _ ih =>
    intro Ξ' e
    have hm : (A ⊕ B) ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase (A ⊕ B)) ~ Γ := perm_erase_of_cons (e.symm.trans h)
    let ⟨d⟩ := ih (B :: Ξ'.erase (A ⊕ B)) (hr.symm.cons _)
    exact ⟨.node (.plus₂ A B) _ (step_of (decide_eq_true hm)) (.cons d .nil)⟩
  | one h =>
    intro Ξ' e
    have : Ξ' = [𝟏] := perm_singleton_eq (e.symm.trans h)
    exact ⟨.node .one _ (step_of (decide_eq_true this)) .nil⟩
  | bot Γ h _ ih =>
    intro Ξ' e
    have hm : ⊥ ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase ⊥) ~ Γ := perm_erase_of_cons (e.symm.trans h)
    let ⟨d⟩ := ih (Ξ'.erase ⊥) hr.symm
    exact ⟨.node .bot _ (step_of (decide_eq_true hm)) (.cons d .nil)⟩
  | tensor A B Γ Δ h _ _ ih₁ ih₂ =>
    intro Ξ' e
    have hm : A ⊗ B ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase (A ⊗ B)) ~ Γ ++ Δ := perm_erase_of_cons (e.symm.trans h)
    have hΔ : (sub (Ξ'.erase (A ⊗ B)) Γ) ~ Δ := sub_perm hr
    let ⟨d₁⟩ := ih₁ _ (.refl _)
    let ⟨d₂⟩ := ih₂ (B :: sub (Ξ'.erase (A ⊗ B)) Γ) (hΔ.symm.cons _)
    have hok : (Move.rule Ξ' (.tensor A B Γ)).ok = true :=
      Bool.and_eq_true_iff.2 ⟨decide_eq_true hm, permB_iff.2 (by perm_count [hr, hΔ])⟩
    exact ⟨.node (.tensor A B Γ) _ (step_of hok) (.cons d₁ (.cons d₂ .nil))⟩
  | par A B Γ h _ ih =>
    intro Ξ' e
    have hm : A ⅋ B ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase (A ⅋ B)) ~ Γ := perm_erase_of_cons (e.symm.trans h)
    let ⟨d⟩ := ih (A :: B :: Ξ'.erase (A ⅋ B)) ((hr.symm.cons _).cons _)
    exact ⟨.node (.par A B) _ (step_of (decide_eq_true hm)) (.cons d .nil)⟩

/-- **S2**: `step` allows every instance of every rule. -/
theorem famToDer : FamToDer := fun _ d => famToDer_perm d _ (.refl _)

end MALL

#axioms_within_file [propext, Quot.sound]
