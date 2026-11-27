/-
The check of a saturated set, as it is run.

`refutedBy D j` (`DILL/Saturated.lean`) is the definition: `j` is a member
of `D` and `D` is saturated.  Run as it is written it asks, for each
premise that a rule needs, every member of `D` in turn whether it is that
premise, and each time by counting every formula of both linear zones.
On a set of 200 sequents that is 2 057 questions, 214 663 pairs of
sequents and 49 726 countings, and the kernel takes 16 s and 5.7 GB for
them (`campaign/measurements-sat.md`, "The cost of the check").

`refutedFast D j` asks the same questions of a set that answers each
without going through its members:

* every linear zone is kept in one order (`sortH`: by the numbers of the
  formulas, `hashF`), and a premise is built in that order (`insH` where
  the definition has `::`), so that two sequents that are one up to the
  order of the zone are equal as lists;
* the members are kept in a binary tree (`BT`), each at the leaf that the
  binary digits of a number computed from it lead to (`keyOf`); a
  question goes down the tree by the digits of the number of the premise
  and compares the premise, as a sequent, with the few members at the
  leaf (`sameB`: exact equality, the numbers compared first).

What is proved is that the check is sound: `refutedFast D j = true →
refutedBy (D.map canon) j = true`, where `D.map canon` is `D` with every
zone in the one order.  Nothing rests on the numbers: a member found is
a member compared formula by formula.  The converse is not claimed, and
does not hold in general: two formulas of one zone with the same number
can be put in two orders, and a set that is saturated is then refused.
The certifiers of `DILL/SatRun.lean` check by `refutedFast`.

Written for the kernel: no instance is unfolded in the loops (`bif`,
`Nat.beq`, `Nat.ble`), and the depth of the tree is the number of binary
digits of the size of the set.  Theory file: it ends with its bound on
axioms.
-/
import DILL.Saturated

namespace DILL

open List

namespace Sat

/-! ## Zones in one order -/

/-- `A` put into a list that is in the order of the numbers. -/
def insH (A : Form) : List Form → List Form
  | [] => [A]
  | B :: l => bif Nat.ble (hashF A) (hashF B) then A :: B :: l else B :: insH A l

theorem insH_perm (A : Form) (l : List Form) : insH A l ~ A :: l := by
  induction l with
  | nil => exact .refl _
  | cons B l ih =>
    cases h : Nat.ble (hashF A) (hashF B)
    · have e : insH A (B :: l) = B :: insH A l := by simp [insH, h]
      rw [e]
      exact (ih.cons B).trans (.swap A B l)
    · have e : insH A (B :: l) = A :: B :: l := by simp [insH, h]
      rw [e]

/-- A list in the order of the numbers. -/
def sortH (l : List Form) : List Form := l.foldr insH []

theorem sortH_perm (l : List Form) : sortH l ~ l := by
  induction l with
  | nil => exact .refl _
  | cons A l ih =>
    show insH A (sortH l) ~ A :: l
    exact (insH_perm A (sortH l)).trans (ih.cons A)

/-- A sequent with its linear zone in the one order. -/
def canon (k : Seq) : Seq := k.unr ⨾ sortH k.lin ⟹ k.goal

theorem canon_equiv (k : Seq) : Equiv (canon k) k :=
  ⟨rfl, sortH_perm _, fun _ h => h, fun _ h => h⟩

/-! ## Two sequents that are one -/

/-- Two lists of formulas are equal, formula by formula. -/
def eqL : List Form → List Form → Bool
  | [], [] => true
  | a :: l, b :: m => eqH a b && eqL l m
  | [], _ :: _ => false
  | _ :: _, [] => false

theorem eqL_eq : ∀ {l m : List Form}, eqL l m = true → l = m
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    have h' : (eqH a b && eqL l m) = true := h
    have h₁ := (Bool.and_eq_true_iff.1 h').1
    have h₂ := (Bool.and_eq_true_iff.1 h').2
    rw [eqH_eq] at h₁
    rw [of_decide_eq_true h₁, eqL_eq h₂]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- The same conclusion and the same linear zone, as a list. -/
def sameB (k x : Seq) : Bool := eqH k.goal x.goal && eqL k.lin x.lin

theorem sameB_eq {k x : Seq} (h : sameB k x = true) : k.goal = x.goal ∧ k.lin = x.lin := by
  have h₁ := (Bool.and_eq_true_iff.1 h).1
  have h₂ := (Bool.and_eq_true_iff.1 h).2
  rw [eqH_eq] at h₁
  exact ⟨of_decide_eq_true h₁, eqL_eq h₂⟩

/-- One of the list is the sequent. -/
def anyS (x : Seq) : List Seq → Bool
  | [] => false
  | k :: ks => sameB k x || anyS x ks

theorem anyS_sound {x : Seq} : ∀ {ks : List Seq}, anyS x ks = true → ∃ k, k ∈ ks ∧ sameB k x = true
  | [], h => by cases h
  | k :: ks, h => by
    have h' : (sameB k x || anyS x ks) = true := h
    cases hk : sameB k x with
    | true => exact ⟨k, List.mem_cons_self .., hk⟩
    | false =>
      rw [hk] at h'
      have ⟨e, he, hs⟩ := anyS_sound (ks := ks) h'
      exact ⟨e, List.mem_cons_of_mem _ he, hs⟩

/-! ## The members in a binary tree -/

/-- A binary tree with lists of sequents at its leaves. -/
inductive BT where
  | leaf (xs : List Seq)
  | node (l r : BT)

/-- The sequents of a tree. -/
def BT.elems : BT → List Seq
  | .leaf xs => xs
  | .node l r => l.elems ++ r.elems

/-- A sequent put at the leaf that the first `d` binary digits of `k`
lead to, the lowest digit first. -/
def BT.ins : Nat → Nat → Seq → BT → BT
  | 0, _, c, .leaf xs => .leaf (c :: xs)
  | 0, _, _, .node l r => .node l r
  | d + 1, k, c, .leaf xs =>
    bif Nat.beq (k % 2) 0 then .node (BT.ins d (k / 2) c (.leaf xs)) (.leaf [])
    else .node (.leaf []) (BT.ins d (k / 2) c (.leaf xs))
  | d + 1, k, c, .node l r =>
    bif Nat.beq (k % 2) 0 then .node (BT.ins d (k / 2) c l) r else .node l (BT.ins d (k / 2) c r)

/-- The sequent is at the leaf that the digits of `k` lead to. -/
def BT.has : BT → Nat → Seq → Bool
  | .leaf xs, _, x => anyS x xs
  | .node l r, k, x => bif Nat.beq (k % 2) 0 then BT.has l (k / 2) x else BT.has r (k / 2) x

theorem BT.has_sound : ∀ (t : BT) (k : Nat) (x : Seq), t.has k x = true →
    ∃ e, e ∈ t.elems ∧ sameB e x = true
  | .leaf xs, _, x, h => anyS_sound (ks := xs) h
  | .node l r, k, x, h => by
    have h' : (bif Nat.beq (k % 2) 0 then BT.has l (k / 2) x else BT.has r (k / 2) x) = true := h
    cases hb : Nat.beq (k % 2) 0 with
    | true =>
      rw [hb] at h'
      have ⟨e, he, hs⟩ := BT.has_sound l (k / 2) x h'
      exact ⟨e, List.mem_append.2 (.inl he), hs⟩
    | false =>
      rw [hb] at h'
      have ⟨e, he, hs⟩ := BT.has_sound r (k / 2) x h'
      exact ⟨e, List.mem_append.2 (.inr he), hs⟩

theorem BT.ins_elems : ∀ (d k : Nat) (c : Seq) (t : BT) (e : Seq),
    e ∈ (BT.ins d k c t).elems → e = c ∨ e ∈ t.elems
  | 0, _, c, .leaf xs, e, h => by
    have h' : e ∈ c :: xs := h
    rcases List.mem_cons.1 h' with h' | h'
    · exact .inl h'
    · exact .inr h'
  | 0, _, _, .node _ _, _, h => .inr h
  | d + 1, k, c, .leaf xs, e, h => by
    cases hb : Nat.beq (k % 2) 0 with
    | true =>
      have h' : e ∈ (BT.ins d (k / 2) c (.leaf xs)).elems ++ [] := by
        have e₁ : BT.ins (d + 1) k c (.leaf xs) =
            .node (BT.ins d (k / 2) c (.leaf xs)) (.leaf []) := by simp [BT.ins, hb]
        rw [e₁] at h
        exact h
      rw [List.append_nil] at h'
      exact BT.ins_elems d (k / 2) c (.leaf xs) e h'
    | false =>
      have h' : e ∈ [] ++ (BT.ins d (k / 2) c (.leaf xs)).elems := by
        have e₁ : BT.ins (d + 1) k c (.leaf xs) =
            .node (.leaf []) (BT.ins d (k / 2) c (.leaf xs)) := by simp [BT.ins, hb]
        rw [e₁] at h
        exact h
      rw [List.nil_append] at h'
      exact BT.ins_elems d (k / 2) c (.leaf xs) e h'
  | d + 1, k, c, .node l r, e, h => by
    cases hb : Nat.beq (k % 2) 0 with
    | true =>
      have h' : e ∈ (BT.ins d (k / 2) c l).elems ++ r.elems := by
        have e₁ : BT.ins (d + 1) k c (.node l r) = .node (BT.ins d (k / 2) c l) r := by
          simp [BT.ins, hb]
        rw [e₁] at h
        exact h
      rcases List.mem_append.1 h' with h' | h'
      · rcases BT.ins_elems d (k / 2) c l e h' with h' | h'
        · exact .inl h'
        · exact .inr (List.mem_append.2 (.inl h'))
      · exact .inr (List.mem_append.2 (.inr h'))
    | false =>
      have h' : e ∈ l.elems ++ (BT.ins d (k / 2) c r).elems := by
        have e₁ : BT.ins (d + 1) k c (.node l r) = .node l (BT.ins d (k / 2) c r) := by
          simp [BT.ins, hb]
        rw [e₁] at h
        exact h
      rcases List.mem_append.1 h' with h' | h'
      · exact .inr (List.mem_append.2 (.inl h'))
      · rcases BT.ins_elems d (k / 2) c r e h' with h' | h'
        · exact .inl h'
        · exact .inr (List.mem_append.2 (.inr h'))

/-- The number of a sequent: from the numbers of its conclusion and of
the formulas of its linear zone, in their order. -/
def keyOf (g : Form) : List Form → Nat
  | [] => hashF g
  | A :: l => keyOf g l * 31 + hashF A

/-- The tree of a list of sequents, of depth `d`. -/
def build (d : Nat) (D : List Seq) : BT :=
  D.foldl (fun t k => BT.ins d (keyOf k.goal k.lin) k t) (.leaf [])

theorem foldl_elems (d : Nat) : ∀ (D : List Seq) (t : BT) (e : Seq),
    e ∈ (D.foldl (fun t k => BT.ins d (keyOf k.goal k.lin) k t) t).elems → e ∈ D ∨ e ∈ t.elems
  | [], _, _, h => .inr h
  | k :: D, t, e, h => by
    rcases foldl_elems d D (BT.ins d (keyOf k.goal k.lin) k t) e h with h | h
    · exact .inl (List.mem_cons_of_mem _ h)
    · rcases BT.ins_elems d _ k t e h with h | h
      · exact .inl (h ▸ List.mem_cons_self ..)
      · exact .inr h

theorem build_elems {d : Nat} {D : List Seq} {e : Seq} (h : e ∈ (build d D).elems) : e ∈ D := by
  rcases foldl_elems d D (.leaf []) e h with h | h
  · exact h
  · cases h

/-- **A sequent is a member**, asked of the tree: its unrestricted zone
is empty, and it is at its leaf. -/
def memF (t : BT) (x : Seq) : Bool := x.unr.isEmpty && t.has (keyOf x.goal x.lin) x

theorem memS_congr {D : List Seq} {x y : Seq} (e : Equiv x y) (h : memS D x = true) :
    memS D y = true :=
  let ⟨k, hk, hkx⟩ := memS_iff.1 h
  memS_iff.2 ⟨k, hk, hkx.trans e⟩

theorem memF_sound {D : List Seq} (hu : ∀ k, k ∈ D → k.unr = []) {d : Nat} {x : Seq}
    (h : memF (build d D) x = true) : memS D x = true := by
  have h₁ := (Bool.and_eq_true_iff.1 h).1
  have h₂ := (Bool.and_eq_true_iff.1 h).2
  have hx : x.unr = [] := List.isEmpty_iff.1 h₁
  have ⟨e, he, hs⟩ := BT.has_sound _ _ _ h₂
  have heD : e ∈ D := build_elems he
  have hg := (sameB_eq hs).1
  have hl := (sameB_eq hs).2
  refine memS_iff.2 ⟨e, heD, ⟨hg, ?_, ?_, ?_⟩⟩
  · rw [hl]
  · intro B hB
    rw [hu e heD] at hB
    cases hB
  · intro B hB
    rw [hx] at hB
    cases hB

/-! ## The condition at a member, with its two parts as parameters

`satAtW List.cons (memS D)` is `satAt D` (`satAtW_cons`): the definition.
`satAtW insH (memF t)` is what is run. -/

/-- `satR`, with the membership test and the way a formula is put into a
zone as parameters. -/
def satRW (cons : Form → List Form → List Form) (mem : Seq → Bool) (Γ Δ : List Form) :
    Form → Bool
  | .lolli A B => mem (Γ ⨾ cons A Δ ⟹ B)
  | .wth A B => mem (Γ ⨾ Δ ⟹ A) || mem (Γ ⨾ Δ ⟹ B)
  | .plus A B => mem (Γ ⨾ Δ ⟹ A) && mem (Γ ⨾ Δ ⟹ B)
  | .bang A => !Δ.isEmpty || mem (Γ ⨾ [] ⟹ A)
  | .tensor A B => (Dec.splits Δ).all fun p => mem (Γ ⨾ p.1 ⟹ A) || mem (Γ ⨾ p.2 ⟹ B)
  | .atom _ => true
  | .one => true
  | .top => true
  | .zero => true

/-- `satL`, in the same way. -/
def satLW (cons : Form → List Form → List Form) (mem : Seq → Bool) (Γ : List Form) (C : Form) :
    Form → List Form → Bool
  | .tensor A B, Δ => mem (Γ ⨾ cons A (cons B Δ) ⟹ C)
  | .one, Δ => mem (Γ ⨾ Δ ⟹ C)
  | .bang A, Δ => mem (A :: Γ ⨾ Δ ⟹ C)
  | .plus A B, Δ => mem (Γ ⨾ cons A Δ ⟹ C) || mem (Γ ⨾ cons B Δ ⟹ C)
  | .wth A B, Δ => mem (Γ ⨾ cons A Δ ⟹ C) && mem (Γ ⨾ cons B Δ ⟹ C)
  | .lolli A B, Δ =>
      (Dec.splits Δ).all fun p => mem (Γ ⨾ p.1 ⟹ A) || mem (Γ ⨾ cons B p.2 ⟹ C)
  | .atom _, _ => true
  | .top, _ => true
  | .zero, _ => true

/-- `satAt`, in the same way. -/
def satAtW (cons : Form → List Form → List Form) (mem : Seq → Bool) (k : Seq) : Bool :=
  !isAxiom k &&
    ((k.unr.all fun A => mem (k.unr ⨾ cons A k.lin ⟹ k.goal)) &&
      (satRW cons mem k.unr k.lin k.goal &&
        (Dec.picks k.lin).all fun p => satLW cons mem k.unr k.goal p.1 p.2))

theorem satRW_cons (D : List Seq) (Γ Δ : List Form) (C : Form) :
    satRW List.cons (memS D) Γ Δ C = satR D Γ Δ C := by
  cases C <;> rfl

theorem satLW_cons (D : List Seq) (Γ : List Form) (C X : Form) (Δ : List Form) :
    satLW List.cons (memS D) Γ C X Δ = satL D Γ C X Δ := by
  cases X <;> rfl

/-- With `::` and the membership of the definition, the condition is the
definition's. -/
theorem satAtW_cons (D : List Seq) (k : Seq) : satAtW List.cons (memS D) k = satAt D k := by
  unfold satAtW satAt
  rw [satRW_cons]
  simp only [satLW_cons]

section sound

variable {D : List Seq} {mem : Seq → Bool} (hm : ∀ x, mem x = true → memS D x = true)
include hm

/-- A premise built with `insH` and found by `mem` is, built with `::`, a
member in the definition's sense. -/
theorem mem_ins {Γ Δ : List Form} {A C : Form} (h : mem (Γ ⨾ insH A Δ ⟹ C) = true) :
    memS D (Γ ⨾ A :: Δ ⟹ C) = true :=
  memS_congr (x := Γ ⨾ insH A Δ ⟹ C) (y := Γ ⨾ A :: Δ ⟹ C)
    ⟨rfl, insH_perm A Δ, fun _ h => h, fun _ h => h⟩ (hm _ h)

theorem satRW_sound {Γ Δ : List Form} : ∀ (C : Form),
    satRW insH mem Γ Δ C = true → satR D Γ Δ C = true
  | .lolli _ _, h => mem_ins hm h
  | .wth A B, h => by
    have h' : (mem (Γ ⨾ Δ ⟹ A) || mem (Γ ⨾ Δ ⟹ B)) = true := h
    show (memS D (Γ ⨾ Δ ⟹ A) || memS D (Γ ⨾ Δ ⟹ B)) = true
    simp only [Bool.or_eq_true] at h' ⊢
    exact h'.imp (hm _) (hm _)
  | .plus A B, h => by
    have h' : (mem (Γ ⨾ Δ ⟹ A) && mem (Γ ⨾ Δ ⟹ B)) = true := h
    show (memS D (Γ ⨾ Δ ⟹ A) && memS D (Γ ⨾ Δ ⟹ B)) = true
    simp only [Bool.and_eq_true] at h' ⊢
    exact ⟨hm _ h'.1, hm _ h'.2⟩
  | .bang A, h => by
    have h' : (!Δ.isEmpty || mem (Γ ⨾ [] ⟹ A)) = true := h
    show (!Δ.isEmpty || memS D (Γ ⨾ [] ⟹ A)) = true
    simp only [Bool.or_eq_true] at h' ⊢
    exact h'.imp id (hm _)
  | .tensor A B, h => by
    have h' : ((Dec.splits Δ).all fun p => mem (Γ ⨾ p.1 ⟹ A) || mem (Γ ⨾ p.2 ⟹ B)) = true := h
    show ((Dec.splits Δ).all fun p => memS D (Γ ⨾ p.1 ⟹ A) || memS D (Γ ⨾ p.2 ⟹ B)) = true
    refine List.all_eq_true.2 fun p hp => ?_
    have hp' := List.all_eq_true.1 h' p hp
    simp only [Bool.or_eq_true] at hp' ⊢
    exact hp'.imp (hm _) (hm _)
  | .atom _, _ => rfl
  | .one, _ => rfl
  | .top, _ => rfl
  | .zero, _ => rfl

theorem satLW_sound {Γ : List Form} {C : Form} : ∀ (X : Form) (Δ : List Form),
    satLW insH mem Γ C X Δ = true → satL D Γ C X Δ = true
  | .tensor A B, Δ, h =>
    memS_congr (x := Γ ⨾ insH A (insH B Δ) ⟹ C) (y := Γ ⨾ A :: B :: Δ ⟹ C)
      ⟨rfl, (insH_perm A _).trans ((insH_perm B Δ).cons A), fun _ h => h, fun _ h => h⟩
      (hm _ h)
  | .one, _, h => hm _ h
  | .bang _, _, h => hm _ h
  | .plus A B, Δ, h => by
    have h' : (mem (Γ ⨾ insH A Δ ⟹ C) || mem (Γ ⨾ insH B Δ ⟹ C)) = true := h
    show (memS D (Γ ⨾ A :: Δ ⟹ C) || memS D (Γ ⨾ B :: Δ ⟹ C)) = true
    simp only [Bool.or_eq_true] at h' ⊢
    exact h'.imp (mem_ins hm) (mem_ins hm)
  | .wth A B, Δ, h => by
    have h' : (mem (Γ ⨾ insH A Δ ⟹ C) && mem (Γ ⨾ insH B Δ ⟹ C)) = true := h
    show (memS D (Γ ⨾ A :: Δ ⟹ C) && memS D (Γ ⨾ B :: Δ ⟹ C)) = true
    simp only [Bool.and_eq_true] at h' ⊢
    exact ⟨mem_ins hm h'.1, mem_ins hm h'.2⟩
  | .lolli A B, Δ, h => by
    have h' : ((Dec.splits Δ).all fun p =>
        mem (Γ ⨾ p.1 ⟹ A) || mem (Γ ⨾ insH B p.2 ⟹ C)) = true := h
    show ((Dec.splits Δ).all fun p =>
        memS D (Γ ⨾ p.1 ⟹ A) || memS D (Γ ⨾ B :: p.2 ⟹ C)) = true
    refine List.all_eq_true.2 fun p hp => ?_
    have hp' := List.all_eq_true.1 h' p hp
    simp only [Bool.or_eq_true] at hp' ⊢
    exact hp'.imp (hm _) (mem_ins hm)
  | .atom _, _, _ => rfl
  | .top, _, _ => rfl
  | .zero, _, _ => rfl

/-- What is run implies the definition, at a member. -/
theorem satAtW_sound (k : Seq) (h : satAtW insH mem k = true) : satAt D k = true := by
  unfold satAtW at h
  unfold satAt
  have h₁ := (Bool.and_eq_true_iff.1 h).1
  have h₂ := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).2).1
  have h₃ := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).2).2).1
  have h₄ := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).2).2).2
  refine Bool.and_eq_true_iff.2 ⟨h₁, Bool.and_eq_true_iff.2 ⟨?_, Bool.and_eq_true_iff.2 ⟨?_, ?_⟩⟩⟩
  · exact List.all_eq_true.2 fun A hA => mem_ins hm (List.all_eq_true.1 h₂ A hA)
  · exact satRW_sound hm _ h₃
  · exact List.all_eq_true.2 fun p hp => satLW_sound hm _ _ (List.all_eq_true.1 h₄ p hp)

end sound

/-- The number of binary digits of `n`, with `f` at least `n`. -/
def digits : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => bif Nat.ble n 1 then 0 else digits f (n / 2) + 1

/-- The tree of a set: its members with their zones in the one order, at
a depth of the number of binary digits of the size of the set and one. -/
def treeOf (D : List Seq) : BT := build (digits D.length D.length + 1) (D.map canon)

/-- **The first part of the check**: every unrestricted zone of the set
is empty, and the sequent is a member. -/
def headOk (D : List Seq) (j : Seq) : Bool :=
  D.all (fun k => k.unr.isEmpty) && memF (treeOf D) (canon j)

/-- **The condition at each sequent of a list**, asked of the tree of
`D`.  The check is `headOk D j` and `restOk D (D.map canon)`; the second
can be computed a part of the list at a time (`restOk_step`), each part
a run of the kernel of its own. -/
def restOk (D : List Seq) (l : List Seq) : Bool := l.all (satAtW insH (memF (treeOf D)))

/-- The condition holds on a list where it holds on its first `c`
sequents and on the rest. -/
theorem restOk_step (D : List Seq) (c : Nat) {l : List Seq}
    (h₁ : restOk D (l.take c) = true) (h₂ : restOk D (l.drop c) = true) : restOk D l = true := by
  unfold restOk at *
  have e : l.all (satAtW insH (memF (treeOf D))) =
      (l.take c ++ l.drop c).all (satAtW insH (memF (treeOf D))) := by
    rw [List.take_append_drop]
  rw [e, List.all_append, h₁, h₂]
  rfl

end Sat

/-- **The check of the certificate, as it is run**: every unrestricted
zone of the set is empty (a saturated set has no other member,
`Sat.unr_nil`); and, with the zones in one order and the members in a
tree, the sequent is a member and the condition holds at each member. -/
def refutedFast (D : List Seq) (j : Seq) : Bool :=
  Sat.headOk D j && Sat.restOk D (D.map Sat.canon)

/-- The check from its parts. -/
theorem refutedFast_of_parts {D : List Seq} {j : Seq} (h₀ : Sat.headOk D j = true)
    (h : Sat.restOk D (D.map Sat.canon) = true) : refutedFast D j = true :=
  Bool.and_eq_true_iff.2 ⟨h₀, h⟩

/-- **The check that is run is sound for the definition**: what it
accepts is, with every zone put in the one order, a saturated set of
which the sequent is a member. -/
theorem refutedFast_sound {D : List Seq} {j : Seq} (h : refutedFast D j = true) :
    refutedBy (D.map Sat.canon) j = true := by
  have h₀ := (Bool.and_eq_true_iff.1 h).1
  have hall : (D.map Sat.canon).all (Sat.satAtW Sat.insH (Sat.memF (Sat.treeOf D))) = true :=
    (Bool.and_eq_true_iff.1 h).2
  have hu := (Bool.and_eq_true_iff.1 h₀).1
  have hmj := (Bool.and_eq_true_iff.1 h₀).2
  have hu' : ∀ k, k ∈ D.map Sat.canon → k.unr = [] := by
    intro k hk
    have ⟨k₀, hk₀, e⟩ := List.mem_map.1 hk
    rw [← e]
    exact List.isEmpty_iff.1 (List.all_eq_true.1 hu k₀ hk₀)
  have hm : ∀ x, Sat.memF (Sat.treeOf D) x = true → Sat.memS (D.map Sat.canon) x = true :=
    fun _ hx => Sat.memF_sound hu' hx
  exact Bool.and_eq_true_iff.2 ⟨Sat.memS_congr (Sat.canon_equiv j) (hm _ hmj),
    List.all_eq_true.2 fun k hk => Sat.satAtW_sound hm k (List.all_eq_true.1 hall k hk)⟩

/-- **No derivation without cut**, from the check that is run. -/
theorem not_cf_of_refutedFast (D : List Seq) (j : Seq) (h : refutedFast D j = true) :
    Nonempty (CF j) → False :=
  not_cf_of_refutedBy (D.map Sat.canon) j (refutedFast_sound h)

end DILL

#axioms_within_file [propext, Quot.sound]
