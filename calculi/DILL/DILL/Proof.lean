/-
DILL as a proof system of the explorer: the moves, the function `step`,
the soundness of the moves for the family with cut (S1), and that `step`
allows every instance of every rule (S2).

Theory file: it ends with its bound on axioms.
-/
import ProofTools.Explore
import DILL.System

namespace DILL

open ProofTools ProofTools.Explore List

/-- **A move**: a rule of CCP's Figure 2, or one of the two cuts, named by
its principal formula.  The three rules that divide the linear zone (⊗R,
⊸L and cut) also name the part of it that goes to their first premise;
the rest goes to the second. -/
inductive Move where
  /-- init, at `Γ ; A ⟹ A`. -/
  | init
  /-- copy of `A`, a member of the unrestricted zone. -/
  | copy (A : Form)
  /-- ⊗L on an occurrence of `A ⊗ B` in the linear zone. -/
  | tensorL (A B : Form)
  /-- ⊗R at the conclusion `A ⊗ B`, with `Δ` the linear zone of the
  premise for `A`. -/
  | tensorR (A B : Form) (Δ : List Form)
  /-- 1L on an occurrence of `1`. -/
  | oneL
  /-- 1R, at `Γ ; · ⟹ 1`. -/
  | oneR
  /-- ⊸L on an occurrence of `A ⊸ B`, with `Δ` the linear zone of the
  premise for `A`. -/
  | lolliL (A B : Form) (Δ : List Form)
  /-- ⊸R at the conclusion `A ⊸ B`. -/
  | lolliR (A B : Form)
  /-- &L₁ on an occurrence of `A & B`. -/
  | withL₁ (A B : Form)
  /-- &L₂ on an occurrence of `A & B`. -/
  | withL₂ (A B : Form)
  /-- &R at the conclusion `A & B`. -/
  | withR (A B : Form)
  /-- ⊤R. -/
  | topR
  /-- 0L. -/
  | zeroL
  /-- ⊕L on an occurrence of `A ⊕ B`. -/
  | plusL (A B : Form)
  /-- ⊕R₁ at the conclusion `A ⊕ B`. -/
  | plusR₁ (A B : Form)
  /-- ⊕R₂ at the conclusion `A ⊕ B`. -/
  | plusR₂ (A B : Form)
  /-- !L on an occurrence of `!A`. -/
  | bangL (A : Form)
  /-- !R at the conclusion `!A`, the linear zone empty. -/
  | bangR (A : Form)
  /-- Cut on the linear formula `A`, with `Δ` the linear zone of the
  premise that proves `A`. -/
  | cut (A : Form) (Δ : List Form)
  /-- Cut on the valid formula `A` (cut!). -/
  | cutU (A : Form)
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

/-- **The rule of a move at a sequent.**  A left rule asks that its
principal formula be in the linear zone, and its premises have the rest
(`List.erase`); a right rule asks that the conclusion be its formula; a
rule that divides the linear zone asks that the part named be part of
what is to be divided, and its second premise has what is left (`sub`). -/
def Move.rule (j : Seq) : Move → Rule
  | .init => ⟨decide (j.lin = [j.goal]), [],
      "init: the linear zone is not exactly the conclusion"⟩
  | .copy A => ⟨decide (A ∈ j.unr), [j.unr ⨾ A :: j.lin ⟹ j.goal],
      "copy: the formula is not in the unrestricted zone"⟩
  | .tensorL A B => ⟨decide (A ⊗ B ∈ j.lin),
      [j.unr ⨾ A :: B :: j.lin.erase (A ⊗ B) ⟹ j.goal],
      "⊗L: the formula is not in the linear zone"⟩
  | .tensorR A B Δ => ⟨decide (j.goal = A ⊗ B) && permB j.lin (Δ ++ sub j.lin Δ),
      [j.unr ⨾ Δ ⟹ A, j.unr ⨾ sub j.lin Δ ⟹ B],
      if decide (j.goal = A ⊗ B) then
        "⊗R: the zone named for the first premise is not part of the linear zone"
      else "⊗R: the conclusion is not this tensor"⟩
  | .oneL => ⟨decide (𝟏 ∈ j.lin), [j.unr ⨾ j.lin.erase 𝟏 ⟹ j.goal],
      "1L: 1 is not in the linear zone"⟩
  | .oneR => ⟨decide (j.goal = 𝟏) && decide (j.lin = []), [],
      if decide (j.goal = 𝟏) then "1R: the linear zone is not empty"
      else "1R: the conclusion is not 1"⟩
  | .lolliL A B Δ =>
      ⟨decide (A ⊸ B ∈ j.lin) &&
          permB (j.lin.erase (A ⊸ B)) (Δ ++ sub (j.lin.erase (A ⊸ B)) Δ),
        [j.unr ⨾ Δ ⟹ A, j.unr ⨾ B :: sub (j.lin.erase (A ⊸ B)) Δ ⟹ j.goal],
        if decide (A ⊸ B ∈ j.lin) then
          "⊸L: the zone named for the first premise is not part of the rest of the linear zone"
        else "⊸L: the formula is not in the linear zone"⟩
  | .lolliR A B => ⟨decide (j.goal = A ⊸ B), [j.unr ⨾ A :: j.lin ⟹ B],
      "⊸R: the conclusion is not this implication"⟩
  | .withL₁ A B => ⟨decide (A & B ∈ j.lin), [j.unr ⨾ A :: j.lin.erase (A & B) ⟹ j.goal],
      "&L₁: the formula is not in the linear zone"⟩
  | .withL₂ A B => ⟨decide (A & B ∈ j.lin), [j.unr ⨾ B :: j.lin.erase (A & B) ⟹ j.goal],
      "&L₂: the formula is not in the linear zone"⟩
  | .withR A B => ⟨decide (j.goal = A & B), [j.unr ⨾ j.lin ⟹ A, j.unr ⨾ j.lin ⟹ B],
      "&R: the conclusion is not this formula"⟩
  | .topR => ⟨decide (j.goal = ⊤), [], "⊤R: the conclusion is not ⊤"⟩
  | .zeroL => ⟨decide (𝟎 ∈ j.lin), [], "0L: 0 is not in the linear zone"⟩
  | .plusL A B => ⟨decide ((A ⊕ B) ∈ j.lin),
      [j.unr ⨾ A :: j.lin.erase (A ⊕ B) ⟹ j.goal, j.unr ⨾ B :: j.lin.erase (A ⊕ B) ⟹ j.goal],
      "⊕L: the formula is not in the linear zone"⟩
  | .plusR₁ A B => ⟨decide (j.goal = (A ⊕ B)), [j.unr ⨾ j.lin ⟹ A],
      "⊕R₁: the conclusion is not this formula"⟩
  | .plusR₂ A B => ⟨decide (j.goal = (A ⊕ B)), [j.unr ⨾ j.lin ⟹ B],
      "⊕R₂: the conclusion is not this formula"⟩
  | .bangL A => ⟨decide ((!A) ∈ j.lin), [A :: j.unr ⨾ j.lin.erase (!A) ⟹ j.goal],
      "!L: the formula is not in the linear zone"⟩
  | .bangR A => ⟨decide (j.goal = !A) && decide (j.lin = []), [j.unr ⨾ [] ⟹ A],
      if decide (j.goal = !A) then "!R: the linear zone is not empty"
      else "!R: the conclusion is not this formula"⟩
  | .cut A Δ => ⟨permB j.lin (Δ ++ sub j.lin Δ),
      [j.unr ⨾ Δ ⟹ A, j.unr ⨾ A :: sub j.lin Δ ⟹ j.goal],
      "cut: the zone named for the first premise is not part of the linear zone"⟩
  | .cutU A => ⟨true, [j.unr ⨾ [] ⟹ A, A :: j.unr ⨾ j.lin ⟹ j.goal], "cut!: always applies"⟩

/-- **The rule of a move, as it is run.**  The same rule with each test
written for the kernel: a formula is looked for, and taken out, with the
numbers of the formulas compared first (`eqH`), and the part named at a
rule that divides the zone is checked in one pass (`subAllH`), where
`Move.rule` counts every formula of the zone.  `Move.ruleF_eq` says the
two are one function. -/
def Move.ruleF (j : Seq) : Move → Rule
  | .init => ⟨decide (j.lin = [j.goal]), [],
      "init: the linear zone is not exactly the conclusion"⟩
  | .copy A => ⟨memH (A) j.unr, [j.unr ⨾ A :: j.lin ⟹ j.goal],
      "copy: the formula is not in the unrestricted zone"⟩
  | .tensorL A B => ⟨memH (A ⊗ B) j.lin,
      [j.unr ⨾ A :: B :: eraseH (A ⊗ B) j.lin ⟹ j.goal],
      "⊗L: the formula is not in the linear zone"⟩
  | .tensorR A B Δ => ⟨decide (j.goal = A ⊗ B) && subAllH j.lin Δ,
      [j.unr ⨾ Δ ⟹ A, j.unr ⨾ subH j.lin Δ ⟹ B],
      if decide (j.goal = A ⊗ B) then
        "⊗R: the zone named for the first premise is not part of the linear zone"
      else "⊗R: the conclusion is not this tensor"⟩
  | .oneL => ⟨memH (𝟏) j.lin, [j.unr ⨾ eraseH 𝟏 j.lin ⟹ j.goal],
      "1L: 1 is not in the linear zone"⟩
  | .oneR => ⟨decide (j.goal = 𝟏) && decide (j.lin = []), [],
      if decide (j.goal = 𝟏) then "1R: the linear zone is not empty"
      else "1R: the conclusion is not 1"⟩
  | .lolliL A B Δ =>
      ⟨memH (A ⊸ B) j.lin &&
          subAllH (eraseH (A ⊸ B) j.lin) Δ,
        [j.unr ⨾ Δ ⟹ A, j.unr ⨾ B :: subH (eraseH (A ⊸ B) j.lin) Δ ⟹ j.goal],
        if decide (A ⊸ B ∈ j.lin) then
          "⊸L: the zone named for the first premise is not part of the rest of the linear zone"
        else "⊸L: the formula is not in the linear zone"⟩
  | .lolliR A B => ⟨decide (j.goal = A ⊸ B), [j.unr ⨾ A :: j.lin ⟹ B],
      "⊸R: the conclusion is not this implication"⟩
  | .withL₁ A B => ⟨memH (A & B) j.lin, [j.unr ⨾ A :: eraseH (A & B) j.lin ⟹ j.goal],
      "&L₁: the formula is not in the linear zone"⟩
  | .withL₂ A B => ⟨memH (A & B) j.lin, [j.unr ⨾ B :: eraseH (A & B) j.lin ⟹ j.goal],
      "&L₂: the formula is not in the linear zone"⟩
  | .withR A B => ⟨decide (j.goal = A & B), [j.unr ⨾ j.lin ⟹ A, j.unr ⨾ j.lin ⟹ B],
      "&R: the conclusion is not this formula"⟩
  | .topR => ⟨decide (j.goal = ⊤), [], "⊤R: the conclusion is not ⊤"⟩
  | .zeroL => ⟨memH (𝟎) j.lin, [], "0L: 0 is not in the linear zone"⟩
  | .plusL A B => ⟨memH ((A ⊕ B)) j.lin,
      [j.unr ⨾ A :: eraseH (A ⊕ B) j.lin ⟹ j.goal, j.unr ⨾ B :: eraseH (A ⊕ B) j.lin ⟹ j.goal],
      "⊕L: the formula is not in the linear zone"⟩
  | .plusR₁ A B => ⟨decide (j.goal = (A ⊕ B)), [j.unr ⨾ j.lin ⟹ A],
      "⊕R₁: the conclusion is not this formula"⟩
  | .plusR₂ A B => ⟨decide (j.goal = (A ⊕ B)), [j.unr ⨾ j.lin ⟹ B],
      "⊕R₂: the conclusion is not this formula"⟩
  | .bangL A => ⟨memH ((!A)) j.lin, [A :: j.unr ⨾ eraseH (!A) j.lin ⟹ j.goal],
      "!L: the formula is not in the linear zone"⟩
  | .bangR A => ⟨decide (j.goal = !A) && decide (j.lin = []), [j.unr ⨾ [] ⟹ A],
      if decide (j.goal = !A) then "!R: the linear zone is not empty"
      else "!R: the conclusion is not this formula"⟩
  | .cut A Δ => ⟨subAllH j.lin Δ,
      [j.unr ⨾ Δ ⟹ A, j.unr ⨾ A :: subH j.lin Δ ⟹ j.goal],
      "cut: the zone named for the first premise is not part of the linear zone"⟩
  | .cutU A => ⟨true, [j.unr ⨾ [] ⟹ A, A :: j.unr ⨾ j.lin ⟹ j.goal], "cut!: always applies"⟩

theorem Move.ruleF_eq (m : Move) (j : Seq) : m.ruleF j = m.rule j := by
  cases m <;>
    simp only [Move.ruleF, Move.rule, memH_eq, eraseH_eq, subAllH_eq, subH_eq, subAll_eq_permB]

/-- **One step**: the premises of the move at the sequent, or why it does
not apply. -/
def step (m : Move) (j : Seq) : Except String (List Seq) :=
  if (m.ruleF j).ok then .ok (m.ruleF j).prems else .error (m.ruleF j).why

/-- **DILL as a proof system.** -/
abbrev S : ProofSystem where
  Judg := Seq
  Move := Move
  step := step

theorem step_of {m : Move} {j : Seq} (h : (m.rule j).ok = true) :
    S.step m j = .ok (m.rule j).prems := by
  show step m j = _
  simp [step, Move.ruleF_eq, h]

theorem step_ok {m : Move} {j : Seq} {ps : List Seq} (h : S.step m j = .ok ps) :
    (m.rule j).ok = true ∧ ps = (m.rule j).prems := by
  have h' : step m j = .ok ps := h
  unfold step at h'
  rw [Move.ruleF_eq] at h'
  split at h'
  · next hok => exact ⟨hok, (Except.ok.inj h').symm⟩
  · cases h'

/-- **S1.  The soundness of the moves**: each move that applies is a rule
of the calculus with cut, applied to the derivations of its premises.
This is not the soundness theorem for the semantics. -/
def step_sound : S.SoundT (Fam true) := fun m j _ h e =>
  have hok : (m.rule j).ok = true := (step_ok h).1
  let e' : Each (Fam true) (m.rule j).prems := (step_ok h).2 ▸ e
  match j, m, hok, e' with
  | ⟨_, _, C⟩, .init, hok, _ => .init C (of_decide_eq_true hok ▸ .refl _)
  | ⟨_, _, _⟩, .copy A, hok, e' => .copy A (of_decide_eq_true hok) e'.1
  | ⟨_, Ξ, _⟩, .tensorL A B, hok, e' =>
      .tensorL A B (Ξ.erase (A ⊗ B)) (perm_cons_erase (of_decide_eq_true hok)) e'.1
  | ⟨_, Ξ, C⟩, .tensorR A B Δ, hok, e' =>
      have hg : C = A ⊗ B := of_decide_eq_true (Bool.and_eq_true_iff.1 hok).1
      hg ▸ .tensorR Δ (sub Ξ Δ) (permB_iff.1 (Bool.and_eq_true_iff.1 hok).2) e'.1 e'.2.1
  | ⟨_, Ξ, _⟩, .oneL, hok, e' =>
      .oneL (Ξ.erase 𝟏) (perm_cons_erase (of_decide_eq_true hok)) e'.1
  | ⟨_, _, C⟩, .oneR, hok, _ =>
      have hg : C = 𝟏 := of_decide_eq_true (Bool.and_eq_true_iff.1 hok).1
      hg ▸ .oneR (of_decide_eq_true (Bool.and_eq_true_iff.1 hok).2 ▸ .refl _)
  | ⟨_, Ξ, _⟩, .lolliL A B Δ, hok, e' =>
      .lolliL A B Δ (sub (Ξ.erase (A ⊸ B)) Δ)
        ((perm_cons_erase (of_decide_eq_true (Bool.and_eq_true_iff.1 hok).1)).trans
          ((permB_iff.1 (Bool.and_eq_true_iff.1 hok).2).cons _))
        e'.1 e'.2.1
  | ⟨_, _, C⟩, .lolliR A B, hok, e' =>
      have hg : C = A ⊸ B := of_decide_eq_true hok
      hg ▸ .lolliR e'.1
  | ⟨_, Ξ, _⟩, .withL₁ A B, hok, e' =>
      .withL₁ A B (Ξ.erase (A & B)) (perm_cons_erase (of_decide_eq_true hok)) e'.1
  | ⟨_, Ξ, _⟩, .withL₂ A B, hok, e' =>
      .withL₂ A B (Ξ.erase (A & B)) (perm_cons_erase (of_decide_eq_true hok)) e'.1
  | ⟨_, _, C⟩, .withR A B, hok, e' =>
      have hg : C = A & B := of_decide_eq_true hok
      hg ▸ .withR e'.1 e'.2.1
  | ⟨_, _, C⟩, .topR, hok, _ =>
      have hg : C = ⊤ := of_decide_eq_true hok
      hg ▸ .topR
  | ⟨_, Ξ, _⟩, .zeroL, hok, _ =>
      .zeroL (Ξ.erase 𝟎) (perm_cons_erase (of_decide_eq_true hok))
  | ⟨_, Ξ, _⟩, .plusL A B, hok, e' =>
      .plusL A B (Ξ.erase (A ⊕ B)) (perm_cons_erase (of_decide_eq_true hok)) e'.1 e'.2.1
  | ⟨_, _, C⟩, .plusR₁ A B, hok, e' =>
      have hg : C = (A ⊕ B) := of_decide_eq_true hok
      hg ▸ .plusR₁ e'.1
  | ⟨_, _, C⟩, .plusR₂ A B, hok, e' =>
      have hg : C = (A ⊕ B) := of_decide_eq_true hok
      hg ▸ .plusR₂ e'.1
  | ⟨_, Ξ, _⟩, .bangL A, hok, e' =>
      .bangL A (Ξ.erase (!A)) (perm_cons_erase (of_decide_eq_true hok)) e'.1
  | ⟨_, _, C⟩, .bangR A, hok, e' =>
      have hg : C = !A := of_decide_eq_true (Bool.and_eq_true_iff.1 hok).1
      hg ▸ .bangR (of_decide_eq_true (Bool.and_eq_true_iff.1 hok).2 ▸ .refl _) e'.1
  | ⟨_, Ξ, _⟩, .cut A Δ, hok, e' =>
      .cut rfl A Δ (sub Ξ Δ) (permB_iff.1 hok) e'.1 e'.2.1
  | ⟨_, _, _⟩, .cutU A, _, e' => .cutU rfl A e'.1 e'.2.1

/-- **The map out**: a derivation of the proof system, as a derivation of
the calculus with cut. -/
def famOfDer {j : Seq} (d : Der S j) : Fam true j := Der.mapOut step_sound d

theorem step_sound_derivable : S.Sound Derivable := step_sound.nonempty

/-- **S2**, the statement: every derivation of the family is one of the
proof system. -/
def FamToDer : Prop := ∀ j : Seq, Fam true j → Nonempty (Der S j)

/-- S2, for every permutation of the linear zone: the move's premises are
those of the rule up to a permutation, so the induction carries one. -/
theorem famToDer_perm {j : Seq} (d : Fam true j) :
    ∀ Ξ' : List Form, j.lin ~ Ξ' → Nonempty (Der S (j.unr ⨾ Ξ' ⟹ j.goal)) := by
  induction d with
  | init A h =>
    intro Ξ' e
    have : Ξ' = [A] := perm_singleton_eq (e.symm.trans h)
    exact ⟨.node .init _ (step_of (decide_eq_true this)) .nil⟩
  | copy A hΓ _ ih =>
    intro Ξ' e
    let ⟨d⟩ := ih (A :: Ξ') (e.cons _)
    exact ⟨.node (.copy A) _ (step_of (decide_eq_true hΓ)) (.cons d .nil)⟩
  | tensorL A B Δ h _ ih =>
    intro Ξ' e
    have hm : A ⊗ B ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase (A ⊗ B)) ~ Δ := perm_erase_of_cons (e.symm.trans h)
    let ⟨d⟩ := ih (A :: B :: Ξ'.erase (A ⊗ B)) ((hr.symm.cons _).cons _)
    exact ⟨.node (.tensorL A B) _ (step_of (decide_eq_true hm)) (.cons d .nil)⟩
  | @tensorR Γ Ξ A B Δ Δ' h _ _ ih₁ ih₂ =>
    intro Ξ' e
    have hΔ : (sub Ξ' Δ) ~ Δ' := sub_perm (e.symm.trans h)
    let ⟨d₁⟩ := ih₁ _ (.refl _)
    let ⟨d₂⟩ := ih₂ (sub Ξ' Δ) hΔ.symm
    have hok : (Move.rule (Γ ⨾ Ξ' ⟹ A ⊗ B) (.tensorR A B Δ)).ok = true :=
      Bool.and_eq_true_iff.2 ⟨decide_eq_true rfl, permB_iff.2 (by perm_count [e, h, hΔ])⟩
    exact ⟨.node (.tensorR A B Δ) _ (step_of hok) (.cons d₁ (.cons d₂ .nil))⟩
  | oneL Δ h _ ih =>
    intro Ξ' e
    have hm : 𝟏 ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase 𝟏) ~ Δ := perm_erase_of_cons (e.symm.trans h)
    let ⟨d⟩ := ih (Ξ'.erase 𝟏) hr.symm
    exact ⟨.node .oneL _ (step_of (decide_eq_true hm)) (.cons d .nil)⟩
  | @oneR Γ Ξ h =>
    intro Ξ' e
    have : Ξ' = [] := perm_nil_eq (e.symm.trans h)
    have hok : (Move.rule (Γ ⨾ Ξ' ⟹ 𝟏) .oneR).ok = true :=
      Bool.and_eq_true_iff.2 ⟨decide_eq_true (p := Form.one = Form.one) rfl, decide_eq_true this⟩
    exact ⟨.node .oneR _ (step_of hok) .nil⟩
  | @lolliL Γ Ξ C A B Δ Δ' h _ _ ih₁ ih₂ =>
    intro Ξ' e
    have hm : A ⊸ B ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase (A ⊸ B)) ~ Δ ++ Δ' := perm_erase_of_cons (e.symm.trans h)
    have hΔ : (sub (Ξ'.erase (A ⊸ B)) Δ) ~ Δ' := sub_perm hr
    let ⟨d₁⟩ := ih₁ _ (.refl _)
    let ⟨d₂⟩ := ih₂ (B :: sub (Ξ'.erase (A ⊸ B)) Δ) (hΔ.symm.cons _)
    have hok : (Move.rule (Γ ⨾ Ξ' ⟹ C) (.lolliL A B Δ)).ok = true :=
      Bool.and_eq_true_iff.2 ⟨decide_eq_true hm, permB_iff.2 (by perm_count [hr, hΔ])⟩
    exact ⟨.node (.lolliL A B Δ) _ (step_of hok) (.cons d₁ (.cons d₂ .nil))⟩
  | @lolliR Γ Ξ A B _ ih =>
    intro Ξ' e
    let ⟨d⟩ := ih (A :: Ξ') (e.cons _)
    have hok : (Move.rule (Γ ⨾ Ξ' ⟹ A ⊸ B) (.lolliR A B)).ok = true := decide_eq_true rfl
    exact ⟨.node (.lolliR A B) _ (step_of hok) (.cons d .nil)⟩
  | withL₁ A B Δ h _ ih =>
    intro Ξ' e
    have hm : A & B ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase (A & B)) ~ Δ := perm_erase_of_cons (e.symm.trans h)
    let ⟨d⟩ := ih (A :: Ξ'.erase (A & B)) (hr.symm.cons _)
    exact ⟨.node (.withL₁ A B) _ (step_of (decide_eq_true hm)) (.cons d .nil)⟩
  | withL₂ A B Δ h _ ih =>
    intro Ξ' e
    have hm : A & B ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase (A & B)) ~ Δ := perm_erase_of_cons (e.symm.trans h)
    let ⟨d⟩ := ih (B :: Ξ'.erase (A & B)) (hr.symm.cons _)
    exact ⟨.node (.withL₂ A B) _ (step_of (decide_eq_true hm)) (.cons d .nil)⟩
  | @withR Γ Ξ A B _ _ ih₁ ih₂ =>
    intro Ξ' e
    let ⟨d₁⟩ := ih₁ Ξ' e
    let ⟨d₂⟩ := ih₂ Ξ' e
    have hok : (Move.rule (Γ ⨾ Ξ' ⟹ A & B) (.withR A B)).ok = true := decide_eq_true rfl
    exact ⟨.node (.withR A B) _ (step_of hok) (.cons d₁ (.cons d₂ .nil))⟩
  | @topR Γ Ξ =>
    intro Ξ' _
    have hok : (Move.rule (Γ ⨾ Ξ' ⟹ ⊤) .topR).ok = true :=
      decide_eq_true (p := Form.top = Form.top) rfl
    exact ⟨.node .topR _ (step_of hok) .nil⟩
  | zeroL Δ h =>
    intro Ξ' e
    have hm : 𝟎 ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    exact ⟨.node .zeroL _ (step_of (decide_eq_true hm)) .nil⟩
  | plusL A B Δ h _ _ ih₁ ih₂ =>
    intro Ξ' e
    have hm : (A ⊕ B) ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase (A ⊕ B)) ~ Δ := perm_erase_of_cons (e.symm.trans h)
    let ⟨d₁⟩ := ih₁ (A :: Ξ'.erase (A ⊕ B)) (hr.symm.cons _)
    let ⟨d₂⟩ := ih₂ (B :: Ξ'.erase (A ⊕ B)) (hr.symm.cons _)
    exact ⟨.node (.plusL A B) _ (step_of (decide_eq_true hm)) (.cons d₁ (.cons d₂ .nil))⟩
  | @plusR₁ Γ Ξ A B _ ih =>
    intro Ξ' e
    let ⟨d⟩ := ih Ξ' e
    have hok : (Move.rule (Γ ⨾ Ξ' ⟹ A ⊕ B) (.plusR₁ A B)).ok = true := decide_eq_true rfl
    exact ⟨.node (.plusR₁ A B) _ (step_of hok) (.cons d .nil)⟩
  | @plusR₂ Γ Ξ A B _ ih =>
    intro Ξ' e
    let ⟨d⟩ := ih Ξ' e
    have hok : (Move.rule (Γ ⨾ Ξ' ⟹ A ⊕ B) (.plusR₂ A B)).ok = true := decide_eq_true rfl
    exact ⟨.node (.plusR₂ A B) _ (step_of hok) (.cons d .nil)⟩
  | bangL A Δ h _ ih =>
    intro Ξ' e
    have hm : (!A) ∈ Ξ' := (e.symm.trans h).mem_iff.2 (mem_cons_self ..)
    have hr : (Ξ'.erase (!A)) ~ Δ := perm_erase_of_cons (e.symm.trans h)
    let ⟨d⟩ := ih (Ξ'.erase (!A)) hr.symm
    exact ⟨.node (.bangL A) _ (step_of (decide_eq_true hm)) (.cons d .nil)⟩
  | @bangR Γ Ξ A h _ ih =>
    intro Ξ' e
    have : Ξ' = [] := perm_nil_eq (e.symm.trans h)
    let ⟨d⟩ := ih [] (.refl _)
    have hok : (Move.rule (Γ ⨾ Ξ' ⟹ !A) (.bangR A)).ok = true :=
      Bool.and_eq_true_iff.2 ⟨decide_eq_true rfl, decide_eq_true this⟩
    exact ⟨.node (.bangR A) _ (step_of hok) (.cons d .nil)⟩
  | @cut Γ Ξ C _ A Δ Δ' h _ _ ih₁ ih₂ =>
    intro Ξ' e
    have hΔ : (sub Ξ' Δ) ~ Δ' := sub_perm (e.symm.trans h)
    let ⟨d₁⟩ := ih₁ _ (.refl _)
    let ⟨d₂⟩ := ih₂ (A :: sub Ξ' Δ) (hΔ.symm.cons _)
    have hok : (Move.rule (Γ ⨾ Ξ' ⟹ C) (.cut A Δ)).ok = true :=
      permB_iff.2 (by perm_count [e, h, hΔ])
    exact ⟨.node (.cut A Δ) _ (step_of hok) (.cons d₁ (.cons d₂ .nil))⟩
  | @cutU Γ Ξ C _ A _ _ ih₁ ih₂ =>
    intro Ξ' e
    let ⟨d₁⟩ := ih₁ [] (.refl _)
    let ⟨d₂⟩ := ih₂ Ξ' e
    have hok : (Move.rule (Γ ⨾ Ξ' ⟹ C) (.cutU A)).ok = true := rfl
    exact ⟨.node (.cutU A) _ (step_of hok) (.cons d₁ (.cons d₂ .nil))⟩

/-- **S2**: `step` allows every instance of every rule. -/
theorem famToDer : FamToDer := fun _ d => famToDer_perm d _ (.refl _)

end DILL

#axioms_within_file [propext, Quot.sound]
