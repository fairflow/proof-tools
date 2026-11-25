/-
Goal 4, first part: exchange and weakening for GLS, with heights.

Source: the Coq files `GL/GLS_exch.v` (`GLS_hpadm_list_exch_L`,
`GLS_hpadm_list_exch_R`) and `GL/GLS_wkn.v` (`GLS_wkn_L`, `GLS_wkn_R`) of
`ianshil/CE_GLS`.  Here the two are one function, `Fam.wk`: a derivation of
`Γ ⇒ Δ` gives one no higher of any sequent whose two lists are, up to a
permutation, `Γ` and `Δ` with more formulas.  It is written by matching on
the derivation.

The lists are read as multisets, and a permutation is proved by counting
(`perm_count`).  Theory file: it ends with its bound on axioms.
-/
import GLS.Lemmas

namespace GLS

/-! ## Permutations, by counting -/

/-- One if the two formulas are the same, zero if not. -/
def ind (b a : Form) : Nat := if b == a then 1 else 0

theorem ind_self (a : Form) : ind a a = 1 := by simp [ind]

theorem count_cons' (a b : Form) (l : List Form) : (b :: l).count a = l.count a + ind b a :=
  List.count_cons

/-- Two lists in which every formula occurs the same number of times are
permutations of each other.  (Core Lean's `List.perm_iff_count` uses
`Classical.choice` on Lean v4.31.0.) -/
theorem perm_of_count {l₁ l₂ : List Form} (h : ∀ a, l₁.count a = l₂.count a) : l₁.Perm l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact List.Perm.nil
    | cons b l₂ =>
      have := h b
      rw [count_cons', ind_self, List.count_nil] at this
      exact absurd this (Nat.succ_ne_zero _).symm
  | cons a l₁ ih =>
    have ha : a ∈ l₂ := by
      apply List.count_pos_iff.1
      have := h a
      rw [count_cons', ind_self] at this
      omega
    have hp := perm_cons_erase ha
    refine (List.Perm.cons a (ih fun b => ?_)).trans hp.symm
    have h1 := h b
    have h2 := hp.count_eq b
    rw [count_cons'] at h1 h2
    omega

theorem xbox_nil : xbox [] = [] := rfl

theorem xbox_cons (A : Form) (Γ : List Form) : xbox (A :: Γ) = A.xb ++ xbox Γ := by
  simp [xbox]

theorem xb_box (B : Form) : (□B).xb = [B, □B] := rfl

theorem xb_imp (A B : Form) : (A ⟶ B).xb = [] := rfl

theorem xb_var (p : Nat) : (Form.var p).xb = [] := rfl

theorem xb_bot : (⊥ : Form).xb = [] := rfl

open Lean in
/-- **A permutation, by counting.**  `perm_count [h₁, …, hₙ]` closes a goal
`l₁.Perm l₂` where the `hᵢ` are proofs of permutations: it counts the
occurrences of a formula `x` in every list, and leaves the arithmetic to
`omega`.  A list `l.erase a` is counted through `perm_cons_erase`, given as
one of the `hᵢ`. -/
macro "perm_count" "[" hs:term,* "]" : tactic => do
  let x := mkIdent `x
  let mut tac ← `(tactic| ((try simp only [count_cons', List.count_append, List.count_nil,
    xbox_append, xbox_cons, xbox_nil, xb_box, xb_imp, xb_var, xb_bot] at *) <;> omega))
  for h in hs.getElems.reverse do
    tac ← `(tactic| (have := List.Perm.count_eq $h $x; $tac))
  `(tactic| (refine perm_of_count (fun $x => ?_); $tac))

/-! ## Derivations with a bound on the height -/

/-- A derivation of `s` of height at most `n`. -/
abbrev FamLe (s : Seq) (n : Nat) : Type := { d : Fam s // d.height ≤ n }

/-- A bound on the height can be raised. -/
def FamLe.mono {s : Seq} {n m : Nat} (d : FamLe s n) (h : n ≤ m) : FamLe s m :=
  ⟨d.1, Nat.le_trans d.2 h⟩

/-- ImpR, with heights. -/
def FamLe.impR (A B : Form) {Γ Δ : List Form} {n : Nat} (h : A ⟶ B ∈ Δ)
    (d : FamLe (A :: Γ ⇒ B :: Δ.erase (A ⟶ B)) n) : FamLe (Γ ⇒ Δ) (n + 1) :=
  ⟨.impR A B h d.1, Nat.succ_le_succ d.2⟩

/-- ImpL, with heights. -/
def FamLe.impL (A B : Form) {Γ Δ : List Form} {n₁ n₂ : Nat} (h : A ⟶ B ∈ Γ)
    (d₁ : FamLe (Γ.erase (A ⟶ B) ⇒ A :: Δ) n₁) (d₂ : FamLe (B :: Γ.erase (A ⟶ B) ⇒ Δ) n₂) :
    FamLe (Γ ⇒ Δ) (max n₁ n₂ + 1) :=
  ⟨.impL A B h d₁.1 d₂.1, Nat.succ_le_succ (by have := d₁.2; have := d₂.2; omega)⟩

/-- GLR, with heights. -/
def FamLe.glr (A : Form) {Γ Δ : List Form} {n : Nat} (h : □A ∈ Δ)
    (d : FamLe (xbox Γ ++ [□A] ⇒ [A]) n) : FamLe (Γ ⇒ Δ) (n + 1) :=
  ⟨.glr A h d.1, Nat.succ_le_succ d.2⟩

/-! ## Weakening, up to a permutation -/

/-- Weakening and exchange in one (`Fam.wk`), by matching on the
derivation.  The sequent is a variable `s`, so that the recursion is on a
part of the derivation: Lean's structural recursion asks that the index of
the family be a variable.  At GLR the premise is weakened by `xbox Ξ` on
the left and by nothing on the right. -/
def Fam.wkAux : {s : Seq} → (d : Fam s) → (Ξ Ξ' Γ' Δ' : List Form) →
    Γ'.Perm (s.ant ++ Ξ) → Δ'.Perm (s.suc ++ Ξ') → FamLe (Γ' ⇒ Δ') d.height
  | _, .idP p hΓ hΔ, _, _, _, _, hΓ', hΔ' =>
      ⟨.idP p (hΓ'.mem_iff.2 (List.mem_append_left _ hΓ))
        (hΔ'.mem_iff.2 (List.mem_append_left _ hΔ)), Nat.le_refl _⟩
  | _, .botL h, _, _, _, _, hΓ', _ =>
      ⟨.botL (hΓ'.mem_iff.2 (List.mem_append_left _ h)), Nat.le_refl _⟩
  | _, .impR A B h d, Ξ, Ξ', Γ', Δ', hΓ', hΔ' =>
      have h' : A ⟶ B ∈ Δ' := hΔ'.mem_iff.2 (List.mem_append_left _ h)
      .impR A B h' (d.wkAux Ξ Ξ' (A :: Γ') (B :: Δ'.erase (A ⟶ B)) (by perm_count [hΓ'])
        (by perm_count [hΔ', perm_cons_erase h, perm_cons_erase h']))
  | _, .impL A B h d₁ d₂, Ξ, Ξ', Γ', Δ', hΓ', hΔ' =>
      have h' : A ⟶ B ∈ Γ' := hΓ'.mem_iff.2 (List.mem_append_left _ h)
      .impL A B h'
        (d₁.wkAux Ξ Ξ' (Γ'.erase (A ⟶ B)) (A :: Δ')
          (by perm_count [hΓ', perm_cons_erase h, perm_cons_erase h']) (by perm_count [hΔ']))
        (d₂.wkAux Ξ Ξ' (B :: Γ'.erase (A ⟶ B)) Δ'
          (by perm_count [hΓ', perm_cons_erase h, perm_cons_erase h']) hΔ')
  | _, .glr A h d, Ξ, _, Γ', _, hΓ', hΔ' =>
      .glr A (hΔ'.mem_iff.2 (List.mem_append_left _ h))
        (d.wkAux (xbox Ξ) [] (xbox Γ' ++ [□A]) [A] (by perm_count [xbox_perm hΓ'])
          (by perm_count []))

/-- **Weakening and exchange in one**: a derivation of `Γ ⇒ Δ` gives one no
higher of `Γ' ⇒ Δ'`, where `Γ'` is a permutation of `Γ` with `Ξ` and `Δ'`
one of `Δ` with `Ξ'`. -/
def Fam.wk {Γ Δ : List Form} (d : Fam (Γ ⇒ Δ)) (Ξ Ξ' Γ' Δ' : List Form)
    (hΓ : Γ'.Perm (Γ ++ Ξ)) (hΔ : Δ'.Perm (Δ ++ Ξ')) : FamLe (Γ' ⇒ Δ') d.height :=
  d.wkAux Ξ Ξ' Γ' Δ' hΓ hΔ

/-- Weakening and exchange in one, for a derivation with a bound on its
height. -/
def FamLe.wk {Γ Δ Γ' Δ' : List Form} {n : Nat} (d : FamLe (Γ ⇒ Δ) n) (Ξ Ξ' : List Form)
    (hΓ : Γ'.Perm (Γ ++ Ξ)) (hΔ : Δ'.Perm (Δ ++ Ξ')) : FamLe (Γ' ⇒ Δ') n :=
  (d.1.wk Ξ Ξ' Γ' Δ' hΓ hΔ).mono d.2

/-- Exchange, for a derivation with a bound on its height. -/
def FamLe.ex {Γ Δ Γ' Δ' : List Form} {n : Nat} (d : FamLe (Γ ⇒ Δ) n)
    (hΓ : Γ.Perm Γ') (hΔ : Δ.Perm Δ') : FamLe (Γ' ⇒ Δ') n :=
  d.wk [] [] (by perm_count [hΓ]) (by perm_count [hΔ])

/-- A derivation, with its height as the bound. -/
def Fam.le {s : Seq} (d : Fam s) : FamLe s d.height := ⟨d, Nat.le_refl _⟩

/-! ## The statements -/

/-- **Goal 4, exchange**, with heights. -/
def exchange : Exchange := fun d hΓ hΔ => d.le.ex hΓ hΔ

/-- **Goal 4, weakening on the left**, with heights. -/
def weakeningL : WeakeningL := fun A _ _ _ d =>
  d.wk [A] [] _ _ (by perm_count []) (by perm_count [])

/-- **Goal 4, weakening on the right**, with heights. -/
def weakeningR : WeakeningR := fun A _ _ _ d =>
  d.wk [] [A] _ _ (by perm_count []) (by perm_count [])

end GLS

#axioms_within_file [propext, Quot.sound]
