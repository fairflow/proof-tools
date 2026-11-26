/-
A certificate against a derivation without cut, which the kernel checks:
a saturated set of sequents, the record of a failed search.

A finite set `D` of sequents is *saturated* when no member is the
conclusion of a rule with no premise (init, 1R, ⊤R, 0L), and every
instance of a rule of the calculus without cut (`CF`, CCP Figure 2) whose
conclusion is a member has a premise that is a member: for each formula
of the unrestricted zone the premise of copy; by the conclusion's
connective the premise of ⊸R, one of the two of &R, both that of ⊕R₁ and
that of ⊕R₂, the premise of !R where the linear zone is empty, and for
every division of the linear zone one of the two premises of ⊗R; and for
each formula of the linear zone, with the rest, the premise of ⊗L, of 1L
and of !L, one of the two of ⊕L, both that of &L₁ and that of &L₂, and
for every division of the rest one of the two premises of ⊸L.  A member
is counted up to a permutation of its linear zone and up to the members
of its unrestricted zone (`Sat.Equiv`).  All this is a Boolean function
of `D` (`Sat.saturated`).

`refutedBy D j` is: `j` is a member of `D`, and `D` is saturated.  Then
`j` has no derivation without cut (`not_cf_of_refutedBy`).  The proof
uses no semantics and no cut: by induction on a derivation without cut
of a sequent equivalent to a member, the last rule is an instance at the
member, one of its premises is equivalent to a member, and the induction
hypothesis is for that premise.

**What the certificate is for.**  A member with a formula `A` in its
unrestricted zone asks for the premise of copy, whose linear zone is
longer by `A`; that member asks for the next.  So a saturated set, being
finite, has no member with a non-empty unrestricted zone (`Sat.unr_nil`),
and none with `!A` in its linear zone (`Sat.no_bang`: the premise of !L
has `A` in the unrestricted zone).  The certifier is therefore for the
sequents with an empty unrestricted zone whose failed search needs no
sequent with `!` in a linear zone; `!` on the right is no obstacle, and
neither is a `!` on the left that the rules never bring into a linear
zone.  For the other sequents the producer (`DILL/Refute.lean`) answers
nothing.  That it finds a set wherever there is one is not proved.  With
`!` derivability is undecidable, and no certificate of this kind could
be complete.

Sources: none for the certificate.  It is the saturated set of
`calculi/MALL/MALL/Saturated.lean` of this repository, for a two-sided
calculus with two zones, with a syntactic proof in place of the phase
model.  The enumerations `Dec.picks` and `Dec.splits`, with their
lemmas, are those of `DILL/Decide.lean`.  Theory file: it ends with its
bound on axioms.
-/
import DILL.Decide

namespace DILL

open List

namespace Sat

/-! ## Membership up to the equivalence -/

/-- **Two sequents that the rules do not tell apart**: the same
conclusion, linear zones that are permutations of each other, and
unrestricted zones with the same members. -/
structure Equiv (k j : Seq) : Prop where
  goal : k.goal = j.goal
  lin : k.lin ~ j.lin
  sub : ∀ B, B ∈ k.unr → B ∈ j.unr
  sup : ∀ B, B ∈ j.unr → B ∈ k.unr

theorem Equiv.refl (j : Seq) : Equiv j j := ⟨rfl, .refl _, fun _ h => h, fun _ h => h⟩

theorem Equiv.trans {k j i : Seq} (h₁ : Equiv k j) (h₂ : Equiv j i) : Equiv k i :=
  ⟨h₁.goal.trans h₂.goal, h₁.lin.trans h₂.lin, fun B h => h₂.sub B (h₁.sub B h),
    fun B h => h₁.sup B (h₂.sup B h)⟩

/-- Every member of the first list is a member of the second. -/
def subB (l₁ l₂ : List Form) : Bool := l₁.all fun a => l₂.contains a

theorem subB_iff {l₁ l₂ : List Form} : subB l₁ l₂ = true ↔ ∀ B, B ∈ l₁ → B ∈ l₂ := by
  unfold subB
  rw [List.all_eq_true]
  exact ⟨fun h B hB => List.contains_iff_mem.1 (h B hB),
    fun h B hB => List.contains_iff_mem.2 (h B hB)⟩

/-- The equivalence, computed. -/
def equivB (k j : Seq) : Bool :=
  decide (k.goal = j.goal) && (permB k.lin j.lin && (subB k.unr j.unr && subB j.unr k.unr))

theorem equivB_iff {k j : Seq} : equivB k j = true ↔ Equiv k j := by
  unfold equivB
  constructor
  · intro h
    have h₁ := Bool.and_eq_true_iff.1 h
    have h₂ := Bool.and_eq_true_iff.1 h₁.2
    have h₃ := Bool.and_eq_true_iff.1 h₂.2
    exact ⟨of_decide_eq_true h₁.1, permB_iff.1 h₂.1, subB_iff.1 h₃.1, subB_iff.1 h₃.2⟩
  · intro h
    exact Bool.and_eq_true_iff.2 ⟨decide_eq_true h.goal,
      Bool.and_eq_true_iff.2 ⟨permB_iff.2 h.lin,
        Bool.and_eq_true_iff.2 ⟨subB_iff.2 h.sub, subB_iff.2 h.sup⟩⟩⟩

/-- **A sequent is a member of the set**, up to the equivalence. -/
def memS (D : List Seq) (j : Seq) : Bool := D.any fun k => equivB k j

theorem memS_iff {D : List Seq} {j : Seq} : memS D j = true ↔ ∃ k, k ∈ D ∧ Equiv k j := by
  unfold memS
  rw [List.any_eq_true]
  exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, equivB_iff.1 h⟩, fun ⟨k, hk, h⟩ => ⟨k, hk, equivB_iff.2 h⟩⟩

theorem memS_of_mem {D : List Seq} {j : Seq} (h : j ∈ D) : memS D j = true :=
  memS_iff.2 ⟨j, h, .refl j⟩

/-! ## Saturation -/

/-- **The conclusion of a rule with no premise**: init (the linear zone
is exactly the conclusion), 1R (the conclusion is `1` and the linear zone
is empty), ⊤R (the conclusion is `⊤`), 0L (`0` is in the linear zone). -/
def isAxiom (k : Seq) : Bool :=
  decide (k.lin = [k.goal]) || ((decide (k.goal = 𝟏) && decide (k.lin = [])) ||
    (decide (k.goal = ⊤) || k.lin.contains 𝟎))

/-- **What the right rules ask of the set** at a member `Γ ; Δ ⟹ C`, by
the connective of `C`: the premise of ⊸R; one of the two premises of &R;
the premise of ⊕R₁ and that of ⊕R₂; the premise of !R, where `Δ` is
empty; for every division of `Δ`, one of the two premises of ⊗R. -/
def satR (D : List Seq) (Γ Δ : List Form) : Form → Bool
  | .lolli A B => memS D (Γ ⨾ A :: Δ ⟹ B)
  | .wth A B => memS D (Γ ⨾ Δ ⟹ A) || memS D (Γ ⨾ Δ ⟹ B)
  | .plus A B => memS D (Γ ⨾ Δ ⟹ A) && memS D (Γ ⨾ Δ ⟹ B)
  | .bang A => !Δ.isEmpty || memS D (Γ ⨾ [] ⟹ A)
  | .tensor A B => (Dec.splits Δ).all fun p => memS D (Γ ⨾ p.1 ⟹ A) || memS D (Γ ⨾ p.2 ⟹ B)
  | .atom _ => true
  | .one => true
  | .top => true
  | .zero => true

/-- **What the left rules ask of the set** at one formula of the linear
zone of a member, with the rest `Δ` of that zone, the unrestricted zone
`Γ` and the conclusion `C`: the premise of ⊗L, of 1L, of !L; one of the
two premises of ⊕L; the premise of &L₁ and that of &L₂; for every
division of `Δ`, one of the two premises of ⊸L. -/
def satL (D : List Seq) (Γ : List Form) (C : Form) : Form → List Form → Bool
  | .tensor A B, Δ => memS D (Γ ⨾ A :: B :: Δ ⟹ C)
  | .one, Δ => memS D (Γ ⨾ Δ ⟹ C)
  | .bang A, Δ => memS D (A :: Γ ⨾ Δ ⟹ C)
  | .plus A B, Δ => memS D (Γ ⨾ A :: Δ ⟹ C) || memS D (Γ ⨾ B :: Δ ⟹ C)
  | .wth A B, Δ => memS D (Γ ⨾ A :: Δ ⟹ C) && memS D (Γ ⨾ B :: Δ ⟹ C)
  | .lolli A B, Δ =>
      (Dec.splits Δ).all fun p => memS D (Γ ⨾ p.1 ⟹ A) || memS D (Γ ⨾ B :: p.2 ⟹ C)
  | .atom _, _ => true
  | .top, _ => true
  | .zero, _ => true

/-- **The condition at one member**: it is the conclusion of no rule
without premises; the premise of each copy is a member; and the right
rule of its conclusion and the left rules of each formula of its linear
zone have the premises they ask for. -/
def satAt (D : List Seq) (k : Seq) : Bool :=
  !isAxiom k &&
    ((k.unr.all fun A => memS D (k.unr ⨾ A :: k.lin ⟹ k.goal)) &&
      (satR D k.unr k.lin k.goal &&
        (Dec.picks k.lin).all fun p => satL D k.unr k.goal p.1 p.2))

/-- **A saturated set of sequents**: the condition holds at every
member. -/
def saturated (D : List Seq) : Bool := D.all (satAt D)

end Sat

/-- **The check of the certificate**: the sequent is a member of the set,
and the set is saturated. -/
def refutedBy (D : List Seq) (j : Seq) : Bool := Sat.memS D j && Sat.saturated D

namespace Sat

/-! ## Soundness -/

/-- What saturation says at a member, in four parts. -/
theorem parts {D : List Seq} (hs : saturated D = true) {Γ Δ : List Form} {C : Form}
    (hk : (Γ ⨾ Δ ⟹ C) ∈ D) :
    isAxiom (Γ ⨾ Δ ⟹ C) = false ∧
    (∀ A, A ∈ Γ → memS D (Γ ⨾ A :: Δ ⟹ C) = true) ∧
    satR D Γ Δ C = true ∧
    (∀ p, p ∈ Dec.picks Δ → satL D Γ C p.1 p.2 = true) := by
  have h : satAt D (Γ ⨾ Δ ⟹ C) = true := List.all_eq_true.1 hs _ hk
  unfold satAt at h
  have h₁ := Bool.and_eq_true_iff.1 h
  have h₂ := Bool.and_eq_true_iff.1 h₁.2
  have h₃ := Bool.and_eq_true_iff.1 h₂.2
  refine ⟨?_, List.all_eq_true.1 h₂.1, h₃.1, List.all_eq_true.1 h₃.2⟩
  cases hax : isAxiom (Γ ⨾ Δ ⟹ C) with
  | false => rfl
  | true =>
    have h₀ := h₁.1
    rw [hax] at h₀
    cases h₀

/-- A formula of a list is picked with a permutation of the rest. -/
theorem picks_complete {d : List Form} {X : Form} {Δ : List Form} (h : d ~ X :: Δ) :
    ∃ r, (X, r) ∈ Dec.picks d ∧ r ~ Δ := by
  obtain ⟨r, hr⟩ := Dec.picks_mem (h.mem_iff.2 (mem_cons_self ..))
  have hp : d ~ X :: r := Dec.picks_perm hr
  exact ⟨r, hr, by perm_count [h, hp]⟩

/-- In a saturated set, what the left rules ask at a formula of the
linear zone of a member holds, with some order of the rest. -/
theorem satL_of {D : List Seq} (hs : saturated D = true) {Γ Δ Ξ Θ : List Form} {C X : Form}
    (hk : (Γ ⨾ Δ ⟹ C) ∈ D) (hl : Δ ~ Ξ) (h : Ξ ~ X :: Θ) :
    ∃ r, r ~ Θ ∧ satL D Γ C X r = true := by
  obtain ⟨r, hr, pr⟩ := picks_complete (hl.trans h)
  exact ⟨r, pr, (parts hs hk).2.2.2 (X, r) hr⟩

/-- The step of the induction: a premise equivalent to a member, with the
induction hypothesis for that premise. -/
theorem close {D : List Seq} {j' p : Seq} (m : memS D j' = true)
    (ih : ∀ k, k ∈ D → Equiv k p → False) (e : Equiv j' p) : False :=
  let ⟨k, hk, hkj⟩ := memS_iff.1 m
  ih k hk (hkj.trans e)

/-- One of two premises is a member. -/
theorem close₂ {D : List Seq} {j₁ j₂ p₁ p₂ : Seq} (m : (memS D j₁ || memS D j₂) = true)
    (ih₁ : ∀ k, k ∈ D → Equiv k p₁ → False) (ih₂ : ∀ k, k ∈ D → Equiv k p₂ → False)
    (e₁ : Equiv j₁ p₁) (e₂ : Equiv j₂ p₂) : False := by
  rcases Bool.or_eq_true_iff.1 m with m | m
  · exact close m ih₁ e₁
  · exact close m ih₂ e₂

theorem cons_sub' {A : Form} {Γ Γ' : List Form} (s : ∀ B, B ∈ Γ → B ∈ Γ') :
    ∀ B, B ∈ A :: Γ → B ∈ A :: Γ' := by
  intro B hB
  rcases List.mem_cons.1 hB with e | h
  · exact List.mem_cons.2 (.inl e)
  · exact List.mem_cons.2 (.inr (s B h))

/-- **No member of a saturated set, and no sequent equivalent to one, has
a derivation without cut.**  By induction on the derivation. -/
theorem no_cf {D : List Seq} (hs : saturated D = true) {j : Seq} (d : Fam false j) :
    ∀ k, k ∈ D → Equiv k j → False := by
  induction d with
  | init A h =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, -, -⟩
    simp only at hg hl
    subst hg
    have e : Δk = [Ck] := perm_singleton_eq (hl.trans h)
    have hax := (parts hs hk).1
    simp [isAxiom, e] at hax
  | copy A hΓ _ ih =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    exact close ((parts hs hk).2.1 A (h₂ A hΓ)) ih ⟨rfl, hl.cons A, h₁, h₂⟩
  | tensorL A B Δ h _ ih =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    obtain ⟨r, pr, hL⟩ := satL_of hs hk hl h
    exact close hL ih ⟨rfl, (pr.cons B).cons A, h₁, h₂⟩
  | tensorR Δ Δ' h _ _ ih₁ ih₂ =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    obtain ⟨p, hp, p₁, p₂⟩ := Dec.splits_complete (hl.trans h)
    have hR := List.all_eq_true.1 (parts hs hk).2.2.1 p hp
    exact close₂ hR ih₁ ih₂ ⟨rfl, p₁, h₁, h₂⟩ ⟨rfl, p₂, h₁, h₂⟩
  | oneL Δ h _ ih =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    obtain ⟨r, pr, hL⟩ := satL_of hs hk hl h
    exact close hL ih ⟨rfl, pr, h₁, h₂⟩
  | oneR h =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, -, -⟩
    simp only at hg hl
    subst hg
    have e : Δk = [] := perm_nil_eq (hl.trans h)
    have hax := (parts hs hk).1
    simp [isAxiom, e] at hax
  | lolliL A B Δ Δ' h _ _ ih₁ ih₂ =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    obtain ⟨r, pr, hL⟩ := satL_of hs hk hl h
    obtain ⟨p, hp, p₁, p₂⟩ := Dec.splits_complete pr
    have hL' := List.all_eq_true.1 hL p hp
    exact close₂ hL' ih₁ ih₂ ⟨rfl, p₁, h₁, h₂⟩ ⟨rfl, p₂.cons B, h₁, h₂⟩
  | lolliR _ ih =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    exact close (parts hs hk).2.2.1 ih ⟨rfl, hl.cons _, h₁, h₂⟩
  | withL₁ A B Δ h _ ih =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    obtain ⟨r, pr, hL⟩ := satL_of hs hk hl h
    exact close (Bool.and_eq_true_iff.1 hL).1 ih ⟨rfl, pr.cons A, h₁, h₂⟩
  | withL₂ A B Δ h _ ih =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    obtain ⟨r, pr, hL⟩ := satL_of hs hk hl h
    exact close (Bool.and_eq_true_iff.1 hL).2 ih ⟨rfl, pr.cons B, h₁, h₂⟩
  | withR _ _ ih₁ ih₂ =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    exact close₂ (parts hs hk).2.2.1 ih₁ ih₂ ⟨rfl, hl, h₁, h₂⟩ ⟨rfl, hl, h₁, h₂⟩
  | topR =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, -, -, -⟩
    simp only at hg
    subst hg
    have hax := (parts hs hk).1
    simp [isAxiom] at hax
  | zeroL Δ h =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, -, -⟩
    simp only at hg hl
    subst hg
    have hm : 𝟎 ∈ Δk := (hl.trans h).mem_iff.2 (mem_cons_self ..)
    have hax := (parts hs hk).1
    simp [isAxiom, hm] at hax
  | plusL A B Δ h _ _ ih₁ ih₂ =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    obtain ⟨r, pr, hL⟩ := satL_of hs hk hl h
    exact close₂ hL ih₁ ih₂ ⟨rfl, pr.cons A, h₁, h₂⟩ ⟨rfl, pr.cons B, h₁, h₂⟩
  | plusR₁ _ ih =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    exact close (Bool.and_eq_true_iff.1 (parts hs hk).2.2.1).1 ih ⟨rfl, hl, h₁, h₂⟩
  | plusR₂ _ ih =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    exact close (Bool.and_eq_true_iff.1 (parts hs hk).2.2.1).2 ih ⟨rfl, hl, h₁, h₂⟩
  | bangL A Δ h _ ih =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    obtain ⟨r, pr, hL⟩ := satL_of hs hk hl h
    exact close hL ih ⟨rfl, pr, cons_sub' h₁, cons_sub' h₂⟩
  | @bangR Γ Ξ A h _ ih =>
    rintro ⟨Γk, Δk, Ck⟩ hk ⟨hg, hl, h₁, h₂⟩
    simp only at hg hl h₁ h₂
    subst hg
    have e : Δk = [] := perm_nil_eq (hl.trans h)
    subst e
    have hR : memS D (Γk ⨾ [] ⟹ A) = true := by simpa [satR] using (parts hs hk).2.2.1
    exact close hR ih ⟨rfl, .refl _, h₁, h₂⟩
  | cut hc => cases hc
  | cutU hc => cases hc

/-! ## What a saturated set cannot have -/

/-- A bound on the lengths of the linear zones of the members. -/
def maxLin : List Seq → Nat
  | [] => 0
  | k :: D => max k.lin.length (maxLin D)

theorem le_maxLin {D : List Seq} {k : Seq} (h : k ∈ D) : k.lin.length ≤ maxLin D := by
  induction D with
  | nil => cases h
  | cons a D ih =>
    rcases List.mem_cons.1 h with e | h
    · subst e
      exact Nat.le_max_left ..
    · exact Nat.le_trans (ih h) (Nat.le_max_right ..)

/-- From a member with `A` in its unrestricted zone, the premises of copy
give members with linear zones as long as one likes. -/
theorem grow {D : List Seq} (hs : saturated D = true) {A : Form} (n : Nat) :
    ∀ k, k ∈ D → A ∈ k.unr → ∃ k', k' ∈ D ∧ A ∈ k'.unr ∧ k.lin.length + n ≤ k'.lin.length := by
  induction n with
  | zero => exact fun k hk hA => ⟨k, hk, hA, Nat.le_refl _⟩
  | succ n ih =>
    rintro ⟨Γ, Δ, C⟩ hk hA
    obtain ⟨k₁, hk₁, he⟩ := memS_iff.1 ((parts hs hk).2.1 A hA)
    obtain ⟨k', hk', hA', hle⟩ := ih k₁ hk₁ (he.sup A hA)
    refine ⟨k', hk', hA', ?_⟩
    have hlen : k₁.lin.length = Δ.length + 1 := he.lin.length_eq
    show Δ.length + (n + 1) ≤ k'.lin.length
    omega

/-- **The unrestricted zone of every member of a saturated set is
empty.** -/
theorem unr_nil {D : List Seq} (hs : saturated D = true) {k : Seq} (hk : k ∈ D) : k.unr = [] := by
  cases hu : k.unr with
  | nil => rfl
  | cons A Γ =>
    have hA : A ∈ k.unr := by
      rw [hu]
      exact List.mem_cons_self ..
    obtain ⟨k', hk', -, hle⟩ := grow hs (maxLin D + 1) k hk hA
    have := le_maxLin hk'
    omega

/-- **No member of a saturated set has `!A` in its linear zone.** -/
theorem no_bang {D : List Seq} (hs : saturated D = true) {k : Seq} (hk : k ∈ D) (A : Form) :
    (!A) ∉ k.lin := by
  obtain ⟨Γ, Δ, C⟩ := k
  intro hm
  obtain ⟨r, hr⟩ := Dec.picks_mem hm
  have hL : memS D (A :: Γ ⨾ r ⟹ C) = true := (parts hs hk).2.2.2 _ hr
  obtain ⟨k₁, hk₁, he⟩ := memS_iff.1 hL
  have hA : A ∈ k₁.unr := he.sup A (List.mem_cons_self ..)
  rw [unr_nil hs hk₁] at hA
  cases hA

end Sat

/-- **Soundness of the certificate**: a sequent that a set refutes has no
derivation without cut. -/
theorem not_cf_of_refutedBy : ∀ (D : List Seq) (j : Seq), refutedBy D j = true →
    ¬ Nonempty (CF j) := by
  intro D j h ⟨d⟩
  have h' := Bool.and_eq_true_iff.1 h
  obtain ⟨k, hk, he⟩ := Sat.memS_iff.1 h'.1
  exact Sat.no_cf h'.2 d k hk he

end DILL

#axioms_within_file [propext, Quot.sound]
