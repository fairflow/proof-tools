/-
Uniform interpolation for GL, through GLS: for every sequent `Γ ⇒ Δ` and
variable `p`, a formula `E` without `p`, computed from `Γ ⇒ Δ` and `p`
alone, such that

    Γ ⇒ Δ, E                                  is derivable, and
    Γ, Υ ⇒ Δ, Ξ derivable  implies  E, Υ ⇒ Ξ derivable,
                                  for every Υ, Ξ without p.

`E` is the classical `∃p (⋀Γ ∧ ¬⋁Δ)`.  For a formula `A`, `∃p.A` is `E` for
the sequent `A ⇒`, and `∀p.A := ¬∃p.¬A`.

**The construction** (not from the literature: `campaign/2026-11-26-ui.md`
says how it was found and how it compares).  `E` is defined by recursion
along the search of `GLS/Search.lean`, in the style of Pitts (1992): an
axiom gives `⊥`; an implication rule gives what its premises give, joined
by `∨` for ImpL; a sequent where only GLR applies, with `Γb` the bodies of
the boxed formulas of `Γ`, gives

    ⋀(literals of Γ ⇒ Δ other than p)
      ∧ □E(xbox □(H ++ Γb) ⇒ ; H ++ Γb)       -- unless Γb ⊆ H: then ⊤
      ∧ ⋀ { ◇E(xbox Γ, □C ⇒ C ; H)  |  □C ∈ Δ }

The extra argument `H` is a list of formulas that hold, with their boxes,
at every world below: it is the loop check that makes the recursion stop.
The proof that `E` does its work is semantic, on the finite trees of
`GLS/TreeModel.lean`: `E` is true at a tree iff some tree bisimilar to it
(ignoring `p`) refutes `Γ ⇒ Δ`.  The syntactic statements then follow
from soundness and the search's completeness.  Theory file: it ends with
its bound on axioms.
-/
import GLS.Connectives
import GLS.Search
import GLS.Soundness

namespace GLS

/-! ## Occurrence of a variable -/

/-- The variable numbered `p` occurs in the formula. -/
def Form.occ (p : Nat) : Form → Bool
  | .var q => decide (q = p)
  | ⊥ => false
  | A ⟶ B => A.occ p || B.occ p
  | □A => A.occ p

/-! ## The interpolant -/

/-- The literals of a sequent other than `p`: `q` for each variable `q` of
the antecedent, `¬q` for each of the succedent. -/
def lits (p : Nat) (Γ Δ : List Form) : List Form :=
  ((Γ.filterMap Form.var?).filter (· != p)).map Form.var ++
    ((Δ.filterMap Form.var?).filter (· != p)).map (fun q => (Form.var q).neg)

/-- **The interpolant, with a number of steps allowed**, given `bx`, what
the box part is for a list `H'`.  `H` is the list of formulas that hold,
boxed and unboxed, at every world below. -/
def itpIn (p : Nat) (bx : List Form → Form) : Nat → List Form → List Form → List Form → Form
  | 0, _, _, _ => ⊥
  | n + 1, Γ, Δ, H =>
    match classify (Γ ⇒ Δ) with
    | .idP .. => ⊥
    | .botL _ => ⊥
    | .idB .. => ⊥
    | .impR A B _ => itpIn p bx n (A :: Γ) (B :: Δ.erase (A ⟶ B)) H
    | .impL A B _ =>
      itpIn p bx n (Γ.erase (A ⟶ B)) (A :: Δ) H ⋎ itpIn p bx n (B :: Γ.erase (A ⟶ B)) Δ H
    | .prime .. =>
      conjL (lits p Γ Δ) ⋏
        (if (Γ.filterMap Form.unbox?).all (fun B => H.contains B) then Form.top
         else □(bx (H ++ Γ.filterMap Form.unbox?))) ⋏
        conjL ((Δ.filterMap Form.unbox?).map fun C => (itpIn p bx n (xbox Γ ++ [□C]) [C] H).dia)

/-- **The interpolant, with `k` box steps allowed**: the number of steps
for each sequent is its measure relative to `U`, plus one. -/
def itpK (p : Nat) (U : List Form) : Nat → List Form → List Form → List Form → Form
  | 0, _, _, _ => ⊥
  | k + 1, Γ, Δ, H =>
    itpIn p (fun H' => itpK p U k (xbox (H'.map Form.box)) [] H') (weight U (Γ ⇒ Δ) + 1) Γ Δ H

/-- A list without repetitions, with the same members. -/
def nub : List Form → List Form
  | [] => []
  | a :: l => if a ∈ nub l then nub l else a :: nub l

/-- The boxed subformulas of a sequent, each once. -/
def Seq.boxes (s : Seq) : List Form := nub s.boxSubs

/-- **The uniform interpolant of a sequent** with respect to `p`: the
classical `∃p (⋀Γ ∧ ¬⋁Δ)`. -/
def uiSeq (p : Nat) (Γ Δ : List Form) : Form :=
  itpK p (Γ ⇒ Δ).boxes ((Γ ⇒ Δ).boxes.length + 1) Γ Δ []

/-- **`∃p.A`**, the uniform interpolant of `A ⇒`. -/
def uiExists (p : Nat) (A : Form) : Form := uiSeq p [A] []

/-- **`∀p.A := ¬∃p.¬A`**: the negation of the uniform interpolant of `⇒ A`. -/
def uiForall (p : Nat) (A : Form) : Form := (uiSeq p [] [A]).neg


/-! ## Bisimulation, ignoring `p` -/

/-- **A bisimulation ignoring `p`**, for the relation proper descendant: related
trees agree on every variable but `p`, and each proper descendant of one is
related to a proper descendant of the other. -/
def IsBisim (p : Nat) (R : Tree → Tree → Prop) : Prop :=
  ∀ a b, R a b → (∀ q, q ≠ p → (q ∈ a.val ↔ q ∈ b.val)) ∧
    (∀ u ∈ a.desc, ∃ u' ∈ b.desc, R u u') ∧ (∀ u' ∈ b.desc, ∃ u ∈ a.desc, R u u')

/-- **Bisimilar trees, ignoring `p`**: related by a bisimulation ignoring `p`. -/
def Bisim (p : Nat) (a b : Tree) : Prop := ∃ R, IsBisim p R ∧ R a b

theorem Bisim.unfold {p : Nat} {a b : Tree} (h : Bisim p a b) :
    (∀ q, q ≠ p → (q ∈ a.val ↔ q ∈ b.val)) ∧
    (∀ u ∈ a.desc, ∃ u' ∈ b.desc, Bisim p u u') ∧ (∀ u' ∈ b.desc, ∃ u ∈ a.desc, Bisim p u u') := by
  obtain ⟨R, hR, hab⟩ := h
  obtain ⟨h1, h2, h3⟩ := hR a b hab
  refine ⟨h1, fun u hu => ?_, fun u' hu' => ?_⟩
  · obtain ⟨u', hu', hr⟩ := h2 u hu; exact ⟨u', hu', R, hR, hr⟩
  · obtain ⟨u, hu, hr⟩ := h3 u' hu'; exact ⟨u, hu, R, hR, hr⟩

theorem Bisim.fold {p : Nat} {a b : Tree} (h1 : ∀ q, q ≠ p → (q ∈ a.val ↔ q ∈ b.val))
    (h2 : ∀ u ∈ a.desc, ∃ u' ∈ b.desc, Bisim p u u')
    (h3 : ∀ u' ∈ b.desc, ∃ u ∈ a.desc, Bisim p u u') : Bisim p a b := by
  refine ⟨fun x y => (x = a ∧ y = b) ∨ Bisim p x y, ?_, .inl ⟨rfl, rfl⟩⟩
  intro x y hxy
  rcases hxy with ⟨rfl, rfl⟩ | hxy
  · refine ⟨h1, fun u hu => ?_, fun u' hu' => ?_⟩
    · obtain ⟨u', h, hb⟩ := h2 u hu; exact ⟨u', h, .inr hb⟩
    · obtain ⟨u, h, hb⟩ := h3 u' hu'; exact ⟨u, h, .inr hb⟩
  · obtain ⟨g1, g2, g3⟩ := hxy.unfold
    refine ⟨g1, fun u hu => ?_, fun u' hu' => ?_⟩
    · obtain ⟨u', h, hb⟩ := g2 u hu; exact ⟨u', h, .inr hb⟩
    · obtain ⟨u, h, hb⟩ := g3 u' hu'; exact ⟨u, h, .inr hb⟩

theorem Bisim.refl (p : Nat) (t : Tree) : Bisim p t t :=
  ⟨Eq, fun a b h => by
    subst h
    exact ⟨fun _ _ => Iff.rfl, fun u hu => ⟨u, hu, rfl⟩, fun u hu => ⟨u, hu, rfl⟩⟩, rfl⟩

theorem contains_eq_of_iff {l l' : List Nat} {q : Nat} (h : q ∈ l ↔ q ∈ l') :
    l.contains q = l'.contains q := by
  cases h1 : l.contains q <;> cases h2 : l'.contains q
  · rfl
  · exact absurd (h.2 (List.contains_iff_mem.1 h2)) (fun hm => by
      rw [List.contains_iff_mem.2 hm] at h1; cases h1)
  · exact absurd (h.1 (List.contains_iff_mem.1 h1)) (fun hm => by
      rw [List.contains_iff_mem.2 hm] at h2; cases h2)
  · rfl

/-- **A formula without `p` has the same truth at bisimilar trees.** -/
theorem holds_bisim {p : Nat} (B : Form) (hB : B.occ p = false) :
    ∀ {a b : Tree}, Bisim p a b → B.holds a = B.holds b := by
  induction B with
  | var q =>
    intro a b h
    have hq : q ≠ p := of_decide_eq_false hB
    exact contains_eq_of_iff (h.unfold.1 q hq)
  | bot => intro _ _ _; rfl
  | imp A B ihA ihB =>
    intro a b h
    have hAB : (A.occ p || B.occ p) = false := hB
    have hA : A.occ p = false := by
      cases hA : A.occ p
      · rfl
      · rw [hA, Bool.true_or] at hAB; cases hAB
    have hB' : B.occ p = false := by
      cases h' : B.occ p
      · rfl
      · rw [h', Bool.or_true] at hAB; cases hAB
    show (!A.holds a || B.holds a) = (!A.holds b || B.holds b)
    rw [ihA hA h, ihB hB' h]
  | box A ih =>
    intro a b h
    have hA : A.occ p = false := hB
    obtain ⟨_, h2, h3⟩ := h.unfold
    show a.desc.all (fun u => A.holds u) = b.desc.all (fun u => A.holds u)
    cases ha : a.desc.all (fun u => A.holds u) <;> cases hb : b.desc.all (fun u => A.holds u)
    · rfl
    · obtain ⟨u, hu, hf⟩ := exists_of_all_false ha
      obtain ⟨u', hu', hb'⟩ := h2 u hu
      have := List.all_eq_true.1 hb u' hu'
      rw [← ih hA hb', hf] at this; cases this
    · obtain ⟨u', hu', hf⟩ := exists_of_all_false hb
      obtain ⟨u, hu, hb'⟩ := h3 u' hu'
      have := List.all_eq_true.1 ha u hu
      rw [ih hA hb', hf] at this; cases this
    · rfl

/-! ## The interpolant does not contain `p` -/

theorem occ_and {p : Nat} {A B : Form} (hA : A.occ p = false) (hB : B.occ p = false) :
    (A ⋏ B).occ p = false := by simp [Form.and, Form.occ, hA, hB]

theorem occ_or {p : Nat} {A B : Form} (hA : A.occ p = false) (hB : B.occ p = false) :
    (A ⋎ B).occ p = false := by simp [Form.or, Form.occ, hA, hB]

theorem occ_dia {p : Nat} {A : Form} (hA : A.occ p = false) : A.dia.occ p = false := by
  simp [Form.dia, Form.occ, hA]

theorem occ_neg {p : Nat} {A : Form} (hA : A.occ p = false) : A.neg.occ p = false := by
  simp [Form.neg, Form.occ, hA]

theorem occ_top (p : Nat) : Form.top.occ p = false := rfl

theorem occ_conjL {p : Nat} {As : List Form} (h : ∀ A ∈ As, A.occ p = false) :
    (conjL As).occ p = false := by
  induction As with
  | nil => rfl
  | cons A As ih =>
    exact occ_and (h A (List.mem_cons_self ..)) (ih fun B hB => h B (List.mem_cons_of_mem _ hB))

theorem occ_lits (p : Nat) (Γ Δ : List Form) : ∀ A ∈ lits p Γ Δ, A.occ p = false := by
  intro A hA
  unfold lits at hA
  rcases List.mem_append.1 hA with hA | hA
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hA
    have := (List.mem_filter.1 hq).2
    simpa [Form.occ] using this
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hA
    have := (List.mem_filter.1 hq).2
    apply occ_neg
    simpa [Form.occ] using this

theorem itpIn_free {p : Nat} {bx : List Form → Form} (hbx : ∀ H', (bx H').occ p = false) :
    ∀ (n : Nat) (Γ Δ H : List Form), (itpIn p bx n Γ Δ H).occ p = false := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro Γ Δ H
    simp only [itpIn]
    split
    · rfl
    · rfl
    · rfl
    · exact ih _ _ _
    · exact occ_or (ih _ _ _) (ih _ _ _)
    · refine occ_and (occ_and (occ_conjL (occ_lits p Γ Δ)) ?_) (occ_conjL ?_)
      · split
        · rfl
        · exact hbx _
      · intro A hA
        obtain ⟨C, _, rfl⟩ := List.mem_map.1 hA
        exact occ_dia (ih _ _ _)

theorem itpK_free (p : Nat) (U : List Form) :
    ∀ (k : Nat) (Γ Δ H : List Form), (itpK p U k Γ Δ H).occ p = false := by
  intro k
  induction k with
  | zero => intro _ _ _; rfl
  | succ k ih => intro Γ Δ H; exact itpIn_free (fun H' => ih _ _ _) _ _ _ _

/-- **The interpolant of a sequent does not contain `p`.** -/
theorem uiSeq_free (p : Nat) (Γ Δ : List Form) : (uiSeq p Γ Δ).occ p = false :=
  itpK_free p _ _ _ _ _

/-! ## Invariants, and lemmas on trees -/

/-- `U` holds every boxed subformula of `□B`, for each `B` of `H`. -/
def HOK (U H : List Form) : Prop := ∀ B ∈ H, ∀ C ∈ (□B).boxSubs, C ∈ U

/-- Every formula of `H` holds at `u`, and its box. -/
def Good (H : List Form) (u : Tree) : Prop := ∀ B ∈ H, B.holds u = true ∧ (□B).holds u = true

/-- Every proper descendant of `t` satisfies `H`. -/
def Ctx0 (H : List Form) (t : Tree) : Prop := ∀ u ∈ t.desc, Good H u

/-- Every proper descendant of `t` is bisimilar, ignoring `p`, to a tree that
satisfies `H`. -/
def Ctx (p : Nat) (H : List Form) (t : Tree) : Prop :=
  ∀ u ∈ t.desc, ∃ u', Bisim p u u' ∧ Good H u'

theorem mem_map_box {H : List Form} {B : Form} : □B ∈ H.map Form.box ↔ B ∈ H := by
  rw [List.mem_map]
  constructor
  · rintro ⟨C, hC, h⟩; cases h; exact hC
  · intro h; exact ⟨B, h, rfl⟩

theorem good_iff {H : List Form} {u : Tree} :
    (xbox (H.map Form.box) ⇒ []).refutedAt u = true ↔ Good H u := by
  rw [refutedAt_iff]
  constructor
  · rintro ⟨h, _⟩ B hB
    exact ⟨h B (body_mem_xbox (mem_map_box.2 hB)), h (□B) (box_mem_xbox (mem_map_box.2 hB))⟩
  · intro h
    refine ⟨fun A hA => ?_, fun _ hB => nomatch hB⟩
    rcases mem_xbox.1 hA with hA | ⟨hA, _⟩
    · exact (h A (mem_map_box.1 hA)).1
    · obtain ⟨B, hB, rfl⟩ := List.mem_map.1 hA
      exact (h B hB).2

theorem closed_xbox {U H : List Form} (hH : HOK U H) : Closed U (xbox (H.map Form.box) ⇒ []) := by
  rintro A (hA | hA) C hC
  · rcases mem_xbox.1 hA with hA | ⟨hA, _⟩
    · exact hH A (mem_map_box.1 hA) C (boxSubs_box hC)
    · obtain ⟨B, hB, rfl⟩ := List.mem_map.1 hA
      exact hH B hB C hC
  · cases hA

theorem desc_trans' {t u v : Tree} (hu : u ∈ t.desc) (hv : v ∈ u.desc) : v ∈ t.desc :=
  Tree.desc_trans t.size t u v (Nat.le_refl _) hu hv

theorem size_desc' {t u : Tree} (hu : u ∈ t.desc) : u.size < t.size :=
  Tree.size_desc t.size t u (Nat.le_refl _) hu

theorem mem_desc_node {v : List Nat} {ks : List Tree} {u : Tree} :
    u ∈ (Tree.node v ks).desc ↔ ∃ k ∈ ks, u = k ∨ u ∈ k.desc := by
  rw [Tree.desc_node, Tree.mem_descL]

/-- A list of choices, without choice: for each member of `l` a related
element, and each element related to a member. -/
theorem list_choose {α β : Type} {P : α → β → Prop} : ∀ (l : List α), (∀ a ∈ l, ∃ b, P a b) →
    ∃ l' : List β, (∀ a ∈ l, ∃ b ∈ l', P a b) ∧ (∀ b ∈ l', ∃ a ∈ l, P a b)
  | [], _ => ⟨[], (fun _ h => by cases h), (fun _ h => by cases h)⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨l', h1, h2⟩ := list_choose l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨b :: l', fun x hx => ?_, fun y hy => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨b, List.mem_cons_self .., hb⟩
      · obtain ⟨y, hy, hp⟩ := h1 x hx; exact ⟨y, List.mem_cons_of_mem _ hy, hp⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨a, List.mem_cons_self .., hb⟩
      · obtain ⟨x, hx, hp⟩ := h2 y hy; exact ⟨x, List.mem_cons_of_mem _ hx, hp⟩

/-- **A last world where `C` fails** (the converse of the relation is
well-founded): below a world where `C` fails there is one where `C` fails
and holds at every proper descendant. -/
theorem last_failure (C : Form) : ∀ (m : Nat) (t u : Tree), u.size < m → u ∈ t.desc →
    C.holds u = false → ∃ w ∈ t.desc, C.holds w = false ∧ ∀ x ∈ w.desc, C.holds x = true := by
  intro m
  induction m with
  | zero => intro _ _ h; cases h
  | succ m ih =>
    intro t u hm hu hC
    cases hall : u.desc.all (fun x => C.holds x) with
    | true => exact ⟨u, hu, hC, fun x hx => List.all_eq_true.1 hall x hx⟩
    | false =>
      obtain ⟨x, hx, hf⟩ := exists_of_all_false hall
      exact ih t x (by have := size_desc' hx; omega) (desc_trans' hu hx) hf

theorem refuted_impR_inv {Γ Δ : List Form} {A B : Form} {t : Tree} (h : A ⟶ B ∈ Δ)
    (hr : (Γ ⇒ Δ).refutedAt t = true) : (A :: Γ ⇒ B :: Δ.erase (A ⟶ B)).refutedAt t = true := by
  rw [refutedAt_iff] at hr ⊢
  obtain ⟨h1, h2⟩ := hr
  have hAB := h2 _ h
  simp only [holds_imp, Bool.or_eq_false_iff, Bool.not_eq_false'] at hAB
  refine ⟨fun C hC => ?_, fun C hC => ?_⟩
  · rcases List.mem_cons.1 hC with rfl | hC
    · exact hAB.1
    · exact h1 C hC
  · rcases List.mem_cons.1 hC with rfl | hC
    · exact hAB.2
    · exact h2 C (List.mem_of_mem_erase hC)

theorem refuted_impL_inv {Γ Δ : List Form} {A B : Form} {t : Tree} (h : A ⟶ B ∈ Γ)
    (hr : (Γ ⇒ Δ).refutedAt t = true) :
    (Γ.erase (A ⟶ B) ⇒ A :: Δ).refutedAt t = true ∨
      (B :: Γ.erase (A ⟶ B) ⇒ Δ).refutedAt t = true := by
  rw [refutedAt_iff] at hr
  obtain ⟨h1, h2⟩ := hr
  have hAB := h1 _ h
  cases hA : A.holds t with
  | false =>
    left
    rw [refutedAt_iff]
    refine ⟨fun C hC => h1 C (List.mem_of_mem_erase hC), fun C hC => ?_⟩
    rcases List.mem_cons.1 hC with rfl | hC
    · exact hA
    · exact h2 C hC
  | true =>
    right
    rw [refutedAt_iff]
    have hB : B.holds t = true := by simpa [hA] using hAB
    refine ⟨fun C hC => ?_, h2⟩
    rcases List.mem_cons.1 hC with rfl | hC
    · exact hB
    · exact h1 C (List.mem_of_mem_erase hC)

/-- Adding to `H` the bodies `Γb` of the boxed formulas of `Γ`, not all of
which are in `H`, lowers the count. -/
theorem ub_append_lt {U Γ Δ H : List Form} (hC : Closed U (Γ ⇒ Δ))
    (hn : ¬ ((Γ.filterMap Form.unbox?).all (fun B => H.contains B)) = true) :
    ub U ((H ++ Γ.filterMap Form.unbox?).map Form.box) < ub U (H.map Form.box) := by
  have hf : (Γ.filterMap Form.unbox?).all (fun B => H.contains B) = false := by
    cases h : (Γ.filterMap Form.unbox?).all (fun B => H.contains B)
    · rfl
    · exact absurd h hn
  obtain ⟨B, hB, hBH⟩ := exists_of_all_false hf
  have hBΓ := mem_unboxes.1 hB
  refine ub_lt (A := B) (fun C _ hC => ?_) (hC _ (.inl hBΓ) _ (boxSubs_self B)) ?_ ?_
  · rw [List.map_append]; exact List.mem_append_left _ hC
  · intro h
    have := List.contains_iff_mem.2 (mem_map_box.1 h)
    rw [this] at hBH; cases hBH
  · rw [List.map_append]; exact List.mem_append_right _ (mem_map_box.2 hB)

theorem hok_append {U Γ Δ H : List Form} (hH : HOK U H) (hC : Closed U (Γ ⇒ Δ)) :
    HOK U (H ++ Γ.filterMap Form.unbox?) := by
  intro B hB C hc
  rcases List.mem_append.1 hB with hB | hB
  · exact hH B hB C hc
  · exact hC _ (.inl (mem_unboxes.1 hB)) C hc

/-! ## A tree that refutes the sequent satisfies the interpolant -/

/-- What a sequent refuted at `t` gives at the proper descendants of `t`:
each boxed formula of the antecedent holds there, and its body. -/
theorem good_below {Γ Δ : List Form} {t : Tree} (hr : (Γ ⇒ Δ).refutedAt t = true) :
    ∀ u ∈ t.desc, Good (Γ.filterMap Form.unbox?) u := by
  intro u hu B hB
  have hbox : (□B).holds t = true := (refutedAt_iff.1 hr).1 _ (mem_unboxes.1 hB)
  have hall := List.all_eq_true.1 hbox
  exact ⟨hall u hu, List.all_eq_true.2 fun v hv => hall v (desc_trans' hu hv)⟩

theorem good_append {H H' : List Form} {u : Tree} (h : Good H u) (h' : Good H' u) :
    Good (H ++ H') u := by
  intro B hB
  rcases List.mem_append.1 hB with hB | hB
  · exact h B hB
  · exact h' B hB

theorem itpIn_a {p : Nat} {U : List Form} {bx : List Form → Form} {H : List Form}
    (hH : HOK U H)
    (hbx : ∀ H', HOK U H' → ub U (H'.map Form.box) < ub U (H.map Form.box) →
      ∀ u, Good H' u → Ctx0 H' u → (bx H').holds u = true) :
    ∀ (n : Nat) (Γ Δ : List Form), Closed U (Γ ⇒ Δ) → weight U (Γ ⇒ Δ) < n →
      ∀ t, (Γ ⇒ Δ).refutedAt t = true → Ctx0 H t → (itpIn p bx n Γ Δ H).holds t = true := by
  intro n
  induction n with
  | zero => intro _ _ _ h; cases h
  | succ n ih =>
    intro Γ Δ hC hw t hr hctx
    have hr' := refutedAt_iff.1 hr
    simp only [itpIn]
    split
    · next q hΓ hΔ _ =>
      have h1 := hr'.1 _ hΓ; have h2 := hr'.2 _ hΔ
      rw [h1] at h2; cases h2
    · next h _ => have := hr'.1 _ h; cases this
    · next A hΓ hΔ _ =>
      have h1 := hr'.1 _ hΓ; have h2 := hr'.2 _ hΔ
      rw [h1] at h2; cases h2
    · next A B h _ =>
      obtain ⟨hC', hlt⟩ := PSPrem.step (.impR A B h rfl) hC
      exact ih _ _ hC' (by omega) t (refuted_impR_inv h hr) hctx
    · next A B h _ =>
      obtain ⟨hC1, hlt1⟩ := PSPrem.step (.impL₁ A B h rfl) hC
      obtain ⟨hC2, hlt2⟩ := PSPrem.step (.impL₂ A B h rfl) hC
      rw [holds_or, Bool.or_eq_true]
      rcases refuted_impL_inv h hr with h1 | h2
      · exact .inl (ih _ _ hC1 (by omega) t h1 hctx)
      · exact .inr (ih _ _ hC2 (by omega) t h2 hctx)
    · next nP nBot nB nR nL _ =>
      rw [holds_and, holds_and, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- the literals
        rw [holds_conjL]
        intro L hL
        unfold lits at hL
        rcases List.mem_append.1 hL with hL | hL
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hL
          exact hr'.1 _ (mem_vars.1 (List.mem_filter.1 hq).1)
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hL
          rw [holds_neg, hr'.2 _ (mem_vars.1 (List.mem_filter.1 hq).1)]; rfl
      · -- the box part
        split
        · exact holds_top t
        · next hn =>
          rw [holds_box, List.all_eq_true]
          intro u hu
          have hg := good_below hr
          refine hbx _ (hok_append hH hC) (ub_append_lt hC hn) u
            (good_append (hctx u hu) (hg u hu)) ?_
          intro v hv
          exact good_append (hctx v (desc_trans' hu hv)) (hg v (desc_trans' hu hv))
      · -- the diamonds
        rw [holds_conjL]
        intro D hD
        obtain ⟨C, hCm, rfl⟩ := List.mem_map.1 hD
        have hCΔ := mem_unboxes.1 hCm
        obtain ⟨hC', hlt⟩ := PSPrem.step (.glr C nP nB nBot hCΔ rfl) hC
        have hbf : (□C).holds t = false := hr'.2 _ hCΔ
        obtain ⟨u, hu, hCu⟩ := exists_of_all_false hbf
        obtain ⟨w, hw, hCw, hbelow⟩ := last_failure C (u.size + 1) t u (Nat.lt_succ_self _) hu hCu
        rw [holds_dia]
        refine ⟨w, hw, ih _ _ hC' (by omega) w ?_ (fun v hv => hctx v (desc_trans' hw hv))⟩
        rw [refutedAt_iff]
        refine ⟨fun A hA => ?_, fun A hA => ?_⟩
        · rcases List.mem_append.1 hA with hA | hA
          · rcases mem_xbox.1 hA with hA | ⟨hA, B, rfl⟩
            · exact List.all_eq_true.1 (hr'.1 _ hA) w hw
            · have := List.all_eq_true.1 (hr'.1 _ hA)
              exact List.all_eq_true.2 fun v hv => this v (desc_trans' hw hv)
          · rw [List.mem_singleton] at hA; subst hA
            exact List.all_eq_true.2 hbelow
        · rw [List.mem_singleton] at hA; subst hA; exact hCw

/-! ## A tree that satisfies the interpolant is bisimilar to one that refutes the sequent -/

/-- **Below a box, by induction along the converse of the relation**: if
`bx` holds at every proper descendant of `t`, and a tree where `bx` holds
whose proper descendants are bisimilar to trees satisfying `H'` is itself
bisimilar to one, then every proper descendant of `t` is. -/
theorem ctx_build {p : Nat} {H' : List Form} {X : Form} {t : Tree}
    (hall : ∀ u ∈ t.desc, X.holds u = true)
    (hstep : ∀ u, X.holds u = true → Ctx p H' u → ∃ u', Bisim p u u' ∧ Good H' u') :
    ∀ u ∈ t.desc, ∃ u', Bisim p u u' ∧ Good H' u' := by
  have key : ∀ (m : Nat) (u : Tree), u.size < m → u ∈ t.desc → ∃ u', Bisim p u u' ∧ Good H' u' := by
    intro m
    induction m with
    | zero => intro _ h; cases h
    | succ m ih =>
      intro u hm hu
      exact hstep u (hall u hu) fun w hw =>
        ih w (by have := size_desc' hw; omega) (desc_trans' hu hw)
  exact fun u hu => key _ u (Nat.lt_succ_self _) hu

/-- The valuation of the new root: the variables of `t` other than `p`,
and `p` if it is in the antecedent. -/
def newVal (p : Nat) (Γ : List Form) (t : Tree) : List Nat :=
  t.val.filter (· != p) ++ (if Form.var p ∈ Γ then [p] else [])

theorem mem_newVal_of_ne {p q : Nat} {Γ : List Form} {t : Tree} (hq : q ≠ p) :
    q ∈ newVal p Γ t ↔ q ∈ t.val := by
  unfold newVal
  rw [List.mem_append, List.mem_filter]
  constructor
  · rintro (⟨h, _⟩ | h)
    · exact h
    · split at h
      · rw [List.mem_singleton] at h; exact absurd h hq
      · cases h
  · intro h; exact .inl ⟨h, by simpa using hq⟩

theorem itpIn_b {p : Nat} {U : List Form} {bx : List Form → Form} {H : List Form}
    (hH : HOK U H)
    (hbx : ∀ H', HOK U H' → ub U (H'.map Form.box) < ub U (H.map Form.box) →
      ∀ u, (bx H').holds u = true → Ctx p H' u → ∃ u', Bisim p u u' ∧ Good H' u') :
    ∀ (n : Nat) (Γ Δ : List Form), Closed U (Γ ⇒ Δ) → weight U (Γ ⇒ Δ) < n →
      ∀ t, (itpIn p bx n Γ Δ H).holds t = true → Ctx p H t →
        ∃ t', Bisim p t t' ∧ (Γ ⇒ Δ).refutedAt t' = true := by
  intro n
  induction n with
  | zero => intro _ _ _ h; cases h
  | succ n ih =>
    intro Γ Δ hC hw t he hctx
    simp only [itpIn] at he
    split at he
    · cases he
    · cases he
    · cases he
    · next A B h _ =>
      obtain ⟨hC', hlt⟩ := PSPrem.step (.impR A B h rfl) hC
      obtain ⟨t', hb, hr⟩ := ih _ _ hC' (by omega) t he hctx
      exact ⟨t', hb, refuted_impR h hr⟩
    · next A B h _ =>
      obtain ⟨hC1, hlt1⟩ := PSPrem.step (.impL₁ A B h rfl) hC
      obtain ⟨hC2, hlt2⟩ := PSPrem.step (.impL₂ A B h rfl) hC
      rw [holds_or, Bool.or_eq_true] at he
      rcases he with he | he
      · obtain ⟨t', hb, hr⟩ := ih _ _ hC1 (by omega) t he hctx
        exact ⟨t', hb, refuted_impL₁ h hr⟩
      · obtain ⟨t', hb, hr⟩ := ih _ _ hC2 (by omega) t he hctx
        exact ⟨t', hb, refuted_impL₂ h hr⟩
    · next nP nBot nB nR nL _ =>
      rw [holds_and, holds_and, Bool.and_eq_true, Bool.and_eq_true] at he
      obtain ⟨⟨hlits, hbox⟩, hdia⟩ := he
      rw [holds_conjL] at hlits hdia
      -- every proper descendant: bisimilar to a tree where the boxes of Γ hold
      have hD : ∀ u ∈ t.desc, ∃ u', Bisim p u u' ∧ Good (Γ.filterMap Form.unbox?) u' := by
        split at hbox
        · next hall =>
          intro u hu
          obtain ⟨u', hb, hg⟩ := hctx u hu
          refine ⟨u', hb, fun B hB => hg B ?_⟩
          exact List.contains_iff_mem.1 (List.all_eq_true.1 hall B hB)
        · next hn =>
          rw [holds_box, List.all_eq_true] at hbox
          have := ctx_build hbox (hbx _ (hok_append hH hC) (ub_append_lt hC hn))
          intro u hu
          obtain ⟨u', hb, hg⟩ := this u hu
          exact ⟨u', hb, fun B hB => hg B (List.mem_append_right _ hB)⟩
      -- each boxed formula of Δ: a witness
      have hW : ∀ C ∈ Δ.filterMap Form.unbox?, ∃ w, (∃ u ∈ t.desc, Bisim p u w) ∧
          (xbox Γ ++ [□C] ⇒ [C]).refutedAt w = true := by
        intro C hCm
        have hCΔ := mem_unboxes.1 hCm
        obtain ⟨hC', hlt⟩ := PSPrem.step (.glr C nP nB nBot hCΔ rfl) hC
        have := hdia _ (List.mem_map.2 ⟨C, hCm, rfl⟩)
        obtain ⟨u, hu, hEu⟩ := (holds_dia _ _).1 this
        obtain ⟨w, hb, hr⟩ := ih _ _ hC' (by omega) u hEu
          (fun v hv => hctx v (desc_trans' hu hv))
        exact ⟨w, ⟨u, hu, hb⟩, hr⟩
      obtain ⟨L1, hL1a, hL1b⟩ := list_choose t.desc hD
      obtain ⟨L2, hL2a, hL2b⟩ := list_choose _ hW
      -- the new tree
      have hk : ∀ k ∈ L1 ++ L2, ∃ u ∈ t.desc, Bisim p u k := by
        intro k hk
        rcases List.mem_append.1 hk with hk | hk
        · obtain ⟨u, hu, hb, _⟩ := hL1b k hk; exact ⟨u, hu, hb⟩
        · obtain ⟨_, _, hu, _⟩ := hL2b k hk; exact hu
      have hgood : ∀ k ∈ L1 ++ L2, Good (Γ.filterMap Form.unbox?) k := by
        intro k hk B hB
        rcases List.mem_append.1 hk with hk | hk
        · obtain ⟨_, _, _, hg⟩ := hL1b k hk; exact hg B hB
        · obtain ⟨_, _, _, hr⟩ := hL2b k hk
          have hr' := (refutedAt_iff.1 hr).1
          have hΓ := mem_unboxes.1 hB
          exact ⟨hr' _ (List.mem_append_left _ (body_mem_xbox hΓ)),
            hr' _ (List.mem_append_left _ (box_mem_xbox hΓ))⟩
      refine ⟨Tree.node (newVal p Γ t) (L1 ++ L2), ?_, ?_⟩
      · refine Bisim.fold (fun q hq => (mem_newVal_of_ne hq).symm) (fun u hu => ?_) (fun u' hu' => ?_)
        · obtain ⟨u', hu', hb, _⟩ := hL1a u hu
          exact ⟨u', mem_desc_node.2 ⟨u', List.mem_append_left _ hu', .inl rfl⟩, hb⟩
        · obtain ⟨k, hkm, hku⟩ := mem_desc_node.1 hu'
          obtain ⟨u, hu, hb⟩ := hk k hkm
          rcases hku with rfl | hku
          · exact ⟨u, hu, hb⟩
          · obtain ⟨w, hw, hb'⟩ := hb.unfold.2.2 u' hku
            exact ⟨w, desc_trans' hu hw, hb'⟩
      · rw [refutedAt_iff]
        refine ⟨fun A hA => ?_, fun A hA => ?_⟩
        · cases A with
          | var q =>
            show (newVal p Γ t).contains q = true
            apply List.contains_iff_mem.2
            by_cases hq : q = p
            · subst hq
              unfold newVal
              rw [if_pos hA]
              exact List.mem_append_right _ (List.mem_singleton.2 rfl)
            · apply (mem_newVal_of_ne hq).2
              have : (Form.var q).holds t = true := hlits _ (List.mem_append_left _
                (List.mem_map.2 ⟨q, List.mem_filter.2 ⟨mem_vars.2 hA, by simpa using hq⟩, rfl⟩))
              exact List.contains_iff_mem.1 this
          | bot => exact absurd hA nBot
          | imp _ _ => exact absurd hA (nL _ _)
          | box B =>
            rw [holds_box, List.all_eq_true]
            intro w hw
            obtain ⟨k, hkm, hkw⟩ := mem_desc_node.1 hw
            obtain ⟨h1, h2⟩ := hgood k hkm B (mem_unboxes.2 hA)
            rcases hkw with rfl | hkw
            · exact h1
            · exact List.all_eq_true.1 h2 w hkw
        · cases A with
          | var q =>
            show (newVal p Γ t).contains q = false
            cases hc : (newVal p Γ t).contains q with
            | false => rfl
            | true =>
              exfalso
              have hm := List.contains_iff_mem.1 hc
              by_cases hq : q = p
              · subst hq
                unfold newVal at hm
                rcases List.mem_append.1 hm with hm | hm
                · have := (List.mem_filter.1 hm).2; simp at this
                · split at hm
                  · next hΓ => exact nP ⟨q, hΓ, hA⟩
                  · cases hm
              · have : (Form.var q).neg.holds t = true := hlits _ (List.mem_append_right _
                  (List.mem_map.2 ⟨q, List.mem_filter.2 ⟨mem_vars.2 hA, by simpa using hq⟩, rfl⟩))
                rw [holds_neg, holds_var, List.contains_iff_mem.2 ((mem_newVal_of_ne hq).1 hm)] at this
                cases this
          | bot => rfl
          | imp _ _ => exact absurd hA (nR _ _)
          | box C =>
            obtain ⟨w, hwm, _, hr⟩ := hL2a C (mem_unboxes.2 hA)
            have hCw : C.holds w = false := (refutedAt_iff.1 hr).2 C (List.mem_singleton.2 rfl)
            cases hall : (□C).holds (Tree.node (newVal p Γ t) (L1 ++ L2)) with
            | false => rfl
            | true =>
              rw [holds_box, List.all_eq_true] at hall
              have := hall w (mem_desc_node.2 ⟨w, List.mem_append_right _ hwm, .inl rfl⟩)
              rw [hCw] at this; cases this

/-! ## The box steps, and the interpolant of a sequent -/

theorem itpK_a {p : Nat} {U : List Form} : ∀ (k : Nat) (Γ Δ H : List Form), HOK U H →
    ub U (H.map Form.box) < k → Closed U (Γ ⇒ Δ) →
    ∀ t, (Γ ⇒ Δ).refutedAt t = true → Ctx0 H t → (itpK p U k Γ Δ H).holds t = true := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; cases h
  | succ k ih =>
    intro Γ Δ H hH hk hC t hr hctx
    refine itpIn_a hH (fun H' hH' hlt u hg hc => ?_) _ Γ Δ hC (Nat.lt_succ_self _) t hr hctx
    exact ih _ _ H' hH' (by omega) (closed_xbox hH') u (good_iff.2 hg) hc

theorem itpK_b {p : Nat} {U : List Form} : ∀ (k : Nat) (Γ Δ H : List Form), HOK U H →
    ub U (H.map Form.box) < k → Closed U (Γ ⇒ Δ) →
    ∀ t, (itpK p U k Γ Δ H).holds t = true → Ctx p H t →
      ∃ t', Bisim p t t' ∧ (Γ ⇒ Δ).refutedAt t' = true := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; cases h
  | succ k ih =>
    intro Γ Δ H hH hk hC t he hctx
    refine itpIn_b hH (fun H' hH' hlt u hu hc => ?_) _ Γ Δ hC (Nat.lt_succ_self _) t he hctx
    obtain ⟨u', hb, hr⟩ := ih _ _ H' hH' (by omega) (closed_xbox hH') u hu hc
    exact ⟨u', hb, good_iff.1 hr⟩

theorem mem_nub {a : Form} : ∀ {l : List Form}, a ∈ nub l ↔ a ∈ l
  | [] => Iff.rfl
  | b :: l => by
    unfold nub
    split
    · next h =>
      rw [mem_nub, List.mem_cons]
      constructor
      · exact .inr
      · rintro (rfl | h')
        · exact mem_nub.1 h
        · exact h'
    · rw [List.mem_cons, List.mem_cons, mem_nub]

theorem closed_boxes (s : Seq) : Closed s.boxes s := fun A hA C hC =>
  mem_nub.2 (closed_self s A hA C hC)

theorem ub_nil_lt (U : List Form) : ub U ([] : List Form) < U.length + 1 :=
  Nat.lt_succ_of_le (List.countP_le_length)

/-- **(a)** A tree that refutes `Γ ⇒ Δ` satisfies its interpolant. -/
theorem uiSeq_of_refuted (p : Nat) {Γ Δ : List Form} {t : Tree}
    (h : (Γ ⇒ Δ).refutedAt t = true) : (uiSeq p Γ Δ).holds t = true :=
  itpK_a _ Γ Δ [] (fun _ h => nomatch h) (ub_nil_lt _) (closed_boxes _) t h (fun _ _ _ h => nomatch h)

/-- **(b)** A tree that satisfies the interpolant of `Γ ⇒ Δ` is bisimilar,
ignoring `p`, to a tree that refutes `Γ ⇒ Δ`. -/
theorem bisim_of_uiSeq (p : Nat) {Γ Δ : List Form} {t : Tree}
    (h : (uiSeq p Γ Δ).holds t = true) : ∃ t', Bisim p t t' ∧ (Γ ⇒ Δ).refutedAt t' = true :=
  itpK_b _ Γ Δ [] (fun _ h => nomatch h) (ub_nil_lt _) (closed_boxes _) t h
    (fun u _ => ⟨u, Bisim.refl p u, fun _ h => nomatch h⟩)

/-- **The interpolant is the bisimulation quantifier**: `∃p (⋀Γ ∧ ¬⋁Δ)` is
true at a finite tree iff some tree bisimilar to it, ignoring `p`,
refutes `Γ ⇒ Δ`. -/
theorem uiSeq_iff (p : Nat) (Γ Δ : List Form) (t : Tree) :
    (uiSeq p Γ Δ).holds t = true ↔ ∃ t', Bisim p t t' ∧ (Γ ⇒ Δ).refutedAt t' = true := by
  refine ⟨bisim_of_uiSeq p, fun ⟨t', hb, hr⟩ => ?_⟩
  rw [holds_bisim _ (uiSeq_free p Γ Δ) hb]
  exact uiSeq_of_refuted p hr

/-! ## The modal depth of the interpolant -/

/-- The modal depth of a formula: the greatest number of nested boxes. -/
def Form.mdepth : Form → Nat
  | .var _ => 0
  | ⊥ => 0
  | A ⟶ B => max A.mdepth B.mdepth
  | □A => A.mdepth + 1

theorem mdepth_and (A B : Form) : (A ⋏ B).mdepth = max A.mdepth B.mdepth := by
  simp only [Form.and, Form.mdepth, Nat.max_zero]

theorem mdepth_or (A B : Form) : (A ⋎ B).mdepth = max A.mdepth B.mdepth := by
  simp only [Form.or, Form.mdepth, Nat.max_zero]

theorem mdepth_dia (A : Form) : A.dia.mdepth = A.mdepth + 1 := by
  simp only [Form.dia, Form.mdepth, Nat.max_zero]

theorem mdepth_conjL_le {As : List Form} {m : Nat} (h : ∀ A ∈ As, A.mdepth ≤ m) :
    (conjL As).mdepth ≤ m := by
  induction As with
  | nil => exact Nat.zero_le _
  | cons A As ih =>
    rw [conjL, mdepth_and]
    exact Nat.max_le.2 ⟨h A (List.mem_cons_self ..), ih fun B hB => h B (List.mem_cons_of_mem _ hB)⟩

theorem mdepth_lits (p : Nat) (Γ Δ : List Form) : ∀ A ∈ lits p Γ Δ, A.mdepth ≤ 0 := by
  intro A hA
  unfold lits at hA
  rcases List.mem_append.1 hA with hA | hA
  · obtain ⟨q, _, rfl⟩ := List.mem_map.1 hA; exact Nat.le_refl _
  · obtain ⟨q, _, rfl⟩ := List.mem_map.1 hA; exact Nat.le_refl _

theorem itpIn_depth {p : Nat} {U : List Form} {bx : List Form → Form} {H : List Form}
    (hbx : ∀ H', HOK U H' → (bx H').mdepth ≤ ub U (xbox (H'.map Form.box)) + ub U (H'.map Form.box))
    (hH : HOK U H) :
    ∀ (n : Nat) (Γ Δ : List Form), Closed U (Γ ⇒ Δ) →
      (itpIn p bx n Γ Δ H).mdepth ≤ ub U Γ + ub U (H.map Form.box) := by
  intro n
  induction n with
  | zero => intro _ _ _; exact Nat.zero_le _
  | succ n ih =>
    intro Γ Δ hC
    simp only [itpIn]
    split
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · next A B h _ =>
      obtain ⟨hC', _⟩ := PSPrem.step (.impR A B h rfl) hC
      have := ih (A :: Γ) (B :: Δ.erase (A ⟶ B)) hC'
      have hle : ub U (A :: Γ) ≤ ub U Γ := ub_le (fun C _ hC => List.mem_cons_of_mem _ hC)
      omega
    · next A B h _ =>
      obtain ⟨hC1, _⟩ := PSPrem.step (.impL₁ A B h rfl) hC
      obtain ⟨hC2, _⟩ := PSPrem.step (.impL₂ A B h rfl) hC
      have h1 := ih (Γ.erase (A ⟶ B)) (A :: Δ) hC1
      have h2 := ih (B :: Γ.erase (A ⟶ B)) Δ hC2
      have hle1 : ub U (Γ.erase (A ⟶ B)) ≤ ub U Γ :=
        ub_le (fun C _ hC => mem_erase_of_ne (by intro h; cases h) hC)
      have hle2 : ub U (B :: Γ.erase (A ⟶ B)) ≤ ub U Γ :=
        ub_le (fun C _ hC => List.mem_cons_of_mem _ (mem_erase_of_ne (by intro h; cases h) hC))
      rw [mdepth_or]
      exact Nat.max_le.2 ⟨by omega, by omega⟩
    · next nP nBot nB nR nL _ =>
      rw [mdepth_and, mdepth_and]
      refine Nat.max_le.2 ⟨Nat.max_le.2 ⟨?_, ?_⟩, ?_⟩
      · exact Nat.le_trans (mdepth_conjL_le (mdepth_lits p Γ Δ)) (Nat.zero_le _)
      · split
        · exact Nat.zero_le _
        · next hn =>
          have hb := hbx _ (hok_append hH hC)
          have hlt := ub_append_lt hC hn
          have hle : ub U (xbox ((H ++ Γ.filterMap Form.unbox?).map Form.box)) ≤ ub U Γ := by
            refine ub_le (fun B _ hB => box_mem_xbox (mem_map_box.2 ?_))
            exact List.mem_append_right _ (mem_unboxes.2 hB)
          show (bx _).mdepth + 1 ≤ _
          omega
      · refine mdepth_conjL_le fun D hD => ?_
        obtain ⟨C, hCm, rfl⟩ := List.mem_map.1 hD
        have hCΔ := mem_unboxes.1 hCm
        obtain ⟨hC', _⟩ := PSPrem.step (.glr C nP nB nBot hCΔ rfl) hC
        have := ih (xbox Γ ++ [□C]) [C] hC'
        have hlt : ub U (xbox Γ ++ [□C]) < ub U Γ :=
          ub_lt (fun B _ hB => List.mem_append_left _ (box_mem_xbox hB))
            (hC _ (.inr hCΔ) _ (boxSubs_self C)) (fun hΓ => nB ⟨C, hΓ, hCΔ⟩)
            (List.mem_append_right _ (List.mem_singleton.2 rfl))
        rw [mdepth_dia]
        omega

theorem itpK_depth {p : Nat} {U : List Form} : ∀ (k : Nat) (Γ Δ H : List Form), HOK U H →
    Closed U (Γ ⇒ Δ) → (itpK p U k Γ Δ H).mdepth ≤ ub U Γ + ub U (H.map Form.box) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _; exact Nat.zero_le _
  | succ k ih =>
    intro Γ Δ H hH hC
    exact itpIn_depth (fun H' hH' => ih _ _ H' hH' (closed_xbox hH')) hH _ Γ Δ hC

/-- **The modal depth of the interpolant is at most twice the number of
distinct boxed subformulas of the sequent.** -/
theorem uiSeq_mdepth (p : Nat) (Γ Δ : List Form) :
    (uiSeq p Γ Δ).mdepth ≤ 2 * (Γ ⇒ Δ).boxes.length := by
  have h := itpK_depth (p := p) ((Γ ⇒ Δ).boxes.length + 1) Γ Δ [] (fun _ h => nomatch h)
    (closed_boxes _)
  have h1 : ub (Γ ⇒ Δ).boxes Γ ≤ (Γ ⇒ Δ).boxes.length := List.countP_le_length
  have h2 : ub (Γ ⇒ Δ).boxes ([] : List Form) ≤ (Γ ⇒ Δ).boxes.length := List.countP_le_length
  unfold uiSeq
  simp only [List.map_nil] at h
  omega

/-! ## Uniform interpolation, syntactically -/

/-- What GLS derives is refuted by no tree. -/
theorem not_refuted_of_fam {s : Seq} (d : Fam s) (t : Tree) : s.refutedAt t ≠ true :=
  fun h => not_satSeq_of_refutedAt h (soundness s d treeModel treeModel_GL treeModel_twoValued t)

/-- A sequent refuted by no tree has a derivation: the search's. -/
def famOfNoRefutation (s : Seq) (h : ∀ t, s.refutedAt t ≠ true) : Fam s :=
  match proofOrRef s with
  | .inl d => d
  | .inr r => absurd r.2 (h r.1)

theorem all_holds_of_bisim {p : Nat} {Υ : List Form} (hΥ : ∀ A ∈ Υ, A.occ p = false)
    {t t' : Tree} (hb : Bisim p t t') (b : Bool) (h : ∀ A ∈ Υ, A.holds t = b) :
    ∀ A ∈ Υ, A.holds t' = b :=
  fun A hA => (holds_bisim A (hΥ A hA) hb).symm.trans (h A hA)

/-- **Uniform interpolation for a sequent**, the statement: a formula `E`
without `p` such that `Γ ⇒ Δ, E` is derivable, and `E, Υ ⇒ Ξ` is
derivable whenever `Γ, Υ ⇒ Δ, Ξ` is and `Υ`, `Ξ` have no `p`. -/
structure UISeqFor (p : Nat) (Γ Δ : List Form) where
  /-- The interpolant. -/
  E : Form
  /-- It does not contain `p`. -/
  free : E.occ p = false
  /-- `Γ ⇒ Δ, E`. -/
  intro : Fam (Γ ⇒ Δ ++ [E])
  /-- From `Γ, Υ ⇒ Δ, Ξ` to `E, Υ ⇒ Ξ`, for `Υ`, `Ξ` without `p`. -/
  elim : (Υ Ξ : List Form) → (∀ A ∈ Υ, A.occ p = false) → (∀ A ∈ Ξ, A.occ p = false) →
    Fam (Γ ++ Υ ⇒ Δ ++ Ξ) → Fam (E :: Υ ⇒ Ξ)

/-- **Uniform interpolation for GLS** (sequent form): for every `p` and
every sequent, an interpolant that depends on `p` and the sequent alone. -/
abbrev UniformInterpolationSeq : Type := (p : Nat) → (Γ Δ : List Form) → UISeqFor p Γ Δ

/-- **Uniform interpolation for GLS, PROVED**: the interpolant is `uiSeq p Γ Δ`. -/
def uniformInterpolationSeq : UniformInterpolationSeq := fun p Γ Δ =>
  { E := uiSeq p Γ Δ
    free := uiSeq_free p Γ Δ
    intro := famOfNoRefutation _ fun t h => by
      rw [refutedAt_iff] at h
      have hr : (Γ ⇒ Δ).refutedAt t = true :=
        refutedAt_iff.2 ⟨h.1, fun B hB => h.2 B (List.mem_append_left _ hB)⟩
      have := h.2 _ (List.mem_append_right _ (List.mem_singleton.2 rfl))
      rw [uiSeq_of_refuted p hr] at this; cases this
    elim := fun Υ Ξ hΥ hΞ d => famOfNoRefutation _ fun t h => by
      rw [refutedAt_iff] at h
      obtain ⟨t', hb, hr⟩ := bisim_of_uiSeq p (h.1 _ (List.mem_cons_self ..))
      have hΥ' := all_holds_of_bisim hΥ hb true fun A hA => h.1 A (List.mem_cons_of_mem _ hA)
      have hΞ' := all_holds_of_bisim hΞ hb false h.2
      have hr' := refutedAt_iff.1 hr
      apply not_refuted_of_fam d t'
      rw [refutedAt_iff]
      refine ⟨fun A hA => ?_, fun A hA => ?_⟩
      · rcases List.mem_append.1 hA with hA | hA
        · exact hr'.1 A hA
        · exact hΥ' A hA
      · rcases List.mem_append.1 hA with hA | hA
        · exact hr'.2 A hA
        · exact hΞ' A hA }

/-- **Uniform interpolation for GL, the statement for formulas**: `∃p.A`
and `∀p.A`, formulas without `p`, with

    A → ∃p.A,       and   A → B  implies  ∃p.A → B,
    ∀p.A → A,       and   B → A  implies  B → ∀p.A,

for every `B` without `p` (each `→` a derivable sequent `X ⇒ Y`). -/
structure UIFor (p : Nat) (A : Form) where
  /-- `∃p.A`. -/
  ex : Form
  /-- `∀p.A`. -/
  all : Form
  ex_free : ex.occ p = false
  all_free : all.occ p = false
  ex_intro : Fam ([A] ⇒ [ex])
  ex_elim : (B : Form) → B.occ p = false → Fam ([A] ⇒ [B]) → Fam ([ex] ⇒ [B])
  all_elim : Fam ([all] ⇒ [A])
  all_intro : (B : Form) → B.occ p = false → Fam ([B] ⇒ [A]) → Fam ([B] ⇒ [all])

/-- **Uniform interpolation for GL.** -/
abbrev UniformInterpolation : Type := (p : Nat) → (A : Form) → UIFor p A

/-- The truth of a sequent `[X] ⇒ [Y]` refuted at a tree. -/
theorem refuted_one_one {X Y : Form} {t : Tree} :
    ([X] ⇒ [Y]).refutedAt t = true ↔ X.holds t = true ∧ Y.holds t = false := by
  rw [refutedAt_iff]; simp

/-- **Uniform interpolation for GL, PROVED**, with `∃p.A := uiExists p A`
and `∀p.A := uiForall p A`. -/
def uniformInterpolation : UniformInterpolation := fun p A =>
  { ex := uiExists p A
    all := uiForall p A
    ex_free := uiSeq_free p _ _
    all_free := occ_neg (uiSeq_free p _ _)
    ex_intro := famOfNoRefutation _ fun t h => by
      rw [refuted_one_one] at h
      have := uiSeq_of_refuted p (Γ := [A]) (Δ := []) (t := t)
        (refutedAt_iff.2 ⟨(fun B hB => by rw [List.mem_singleton.1 hB]; exact h.1), fun _ h => nomatch h⟩)
      unfold uiExists at h; rw [this] at h; cases h.2
    ex_elim := fun B hB d => famOfNoRefutation _ fun t h => by
      rw [refuted_one_one] at h
      obtain ⟨t', hb, hr⟩ := bisim_of_uiSeq p h.1
      have hA : A.holds t' = true := (refutedAt_iff.1 hr).1 A (List.mem_singleton.2 rfl)
      have hB' : B.holds t' = false := (holds_bisim B hB hb).symm.trans h.2
      exact not_refuted_of_fam d t' (refuted_one_one.2 ⟨hA, hB'⟩)
    all_elim := famOfNoRefutation _ fun t h => by
      rw [refuted_one_one] at h
      have hr : ([] ⇒ [A]).refutedAt t = true :=
        refutedAt_iff.2 ⟨(fun _ h => nomatch h), (fun B hB => by rw [List.mem_singleton.1 hB]; exact h.2)⟩
      have := h.1
      unfold uiForall at this
      rw [holds_neg, uiSeq_of_refuted p hr] at this; cases this
    all_intro := fun B hB d => famOfNoRefutation _ fun t h => by
      rw [refuted_one_one] at h
      have h2 := h.2
      unfold uiForall at h2
      rw [holds_neg, Bool.not_eq_false'] at h2
      obtain ⟨t', hb, hr⟩ := bisim_of_uiSeq p h2
      have hA : A.holds t' = false := (refutedAt_iff.1 hr).2 A (List.mem_singleton.2 rfl)
      have hB' : B.holds t' = true := (holds_bisim B hB hb).symm.trans h.1
      exact not_refuted_of_fam d t' (refuted_one_one.2 ⟨hB', hA⟩) }

end GLS

#axioms_within_file [propext, Quot.sound]
