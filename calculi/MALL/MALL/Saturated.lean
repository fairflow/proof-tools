/-
A countermodel for every sequent with no derivation, as a certificate
that the kernel checks: a saturated set of sequents.

A finite set `D` of sequents is *saturated* when no member is the
conclusion of a rule without premises (the logical axiom at a letter, the
rule 1, the rule ⊤), and every rule instance whose conclusion is a member
has a premise that is a member: the premise of ⅋ and of ⊥; one of the two
premises of &; both the premise of 1⊕ and that of 2⊕; and, for every way
to divide the context of a ⊗, one of its two premises.  This is a Boolean
function of `D` (`saturated`).

A saturated set presents a finite phase structure (`satModel`): the
instance of `Syn` (`MALL/Completeness.lean`) whose congruence is
"permutations of each other, or neither is a part of a member of `D`" and
whose antiphases are the sequents that are not members of `D`.  Its phases
are the parts of the members of `D`, and one more for all other sequents.
By Okada's lemma a sequent that holds in it is an antiphase; so no member
of `D` holds in it (`satModel_refutes`).  The kernel checks the saturation
and never computes an interpretation.

The certificate is complete (`refutation_complete`): for a sequent `Γ`
with no derivation, the small sequents (those of `MALL/FiniteModel.lean`)
with no derivation without cut are a saturated set with `Γ` a member.

Sources: none for the certificate.  The structure is Lafont's finite
model (J. Symbolic Logic 62, 1997, the author's version, p. 3) with the
set `D` in place of "below `A` and not provable"; the lemma is his Lemma 1.
Theory file: it ends with its bound on axioms.
-/
import MALL.FiniteModel

namespace MALL

open List

/-! ## Membership up to permutation -/

/-- A sequent is a member of the set, up to the order of its formulas. -/
def memP (D : List (List Form)) (Γ : List Form) : Bool := D.any fun d => permB d Γ

theorem memP_iff {D : List (List Form)} {Γ : List Form} :
    memP D Γ = true ↔ ∃ d, d ∈ D ∧ d ~ Γ := by
  unfold memP
  rw [List.any_eq_true]
  exact ⟨fun ⟨d, hd, h⟩ => ⟨d, hd, permB_iff.1 h⟩, fun ⟨d, hd, h⟩ => ⟨d, hd, permB_iff.2 h⟩⟩

theorem memP_of_perm {D : List (List Form)} {Γ Δ : List Form} (h : Γ ~ Δ)
    (m : memP D Γ = true) : memP D Δ = true :=
  let ⟨d, hd, p⟩ := memP_iff.1 m
  memP_iff.2 ⟨d, hd, p.trans h⟩

theorem memP_of_mem {D : List (List Form)} {Γ : List Form} (h : Γ ∈ D) : memP D Γ = true :=
  memP_iff.2 ⟨Γ, h, .refl _⟩

/-! ## Saturation -/

/-- **The condition at one formula of a member**, with the rest `Γ` of the
member: what the rule that introduces the formula asks of the set. -/
def satAt (D : List (List Form)) : Form → List Form → Bool
  | .atom a, Γ => decide (Γ ≠ [.natom a])
  | .natom _, _ => true
  | .one, Γ => decide (Γ ≠ [])
  | .bot, Γ => memP D Γ
  | .top, _ => false
  | .zero, _ => true
  | .tensor A C, Γ => (splits Γ).all fun p => memP D (A :: p.1) || memP D (C :: p.2)
  | .par A C, Γ => memP D (A :: C :: Γ)
  | .wth A C, Γ => memP D (A :: Γ) || memP D (C :: Γ)
  | .plus A C, Γ => memP D (A :: Γ) && memP D (C :: Γ)

/-- **A saturated set of sequents**: the condition holds at every formula
of every member. -/
def saturated (D : List (List Form)) : Bool :=
  D.all fun d => (picks d).all fun p => satAt D p.1 p.2

/-- A formula of a list is picked with a permutation of the rest. -/
theorem picks_complete {d : List Form} {X : Form} {Γ : List Form} (h : d ~ X :: Γ) :
    ∃ Γ', (X, Γ') ∈ picks d ∧ Γ' ~ Γ := by
  obtain ⟨r, hr⟩ := picks_mem (h.mem_iff.2 (mem_cons_self ..))
  have hp := picks_perm hr
  refine ⟨r, hr, ?_⟩
  have hp' : d ~ X :: r := hp
  perm_count [h, hp']

/-- In a saturated set, the condition holds at a formula of a member, with
some order of the rest. -/
theorem satAt_of_memP {D : List (List Form)} (hs : saturated D = true) {X : Form}
    {Γ : List Form} (h : memP D (X :: Γ) = true) : ∃ Γ', Γ' ~ Γ ∧ satAt D X Γ' = true := by
  obtain ⟨d, hd, p⟩ := memP_iff.1 h
  obtain ⟨Γ', hΓ', pΓ⟩ := picks_complete p
  exact ⟨Γ', pΓ, List.all_eq_true.1 (List.all_eq_true.1 hs d hd) (X, Γ') hΓ'⟩

/-! ## The parts of the members -/

/-- **A part of a member** of the set: the sequents that are not parts of
members are an ideal. -/
def Part (D : List (List Form)) (Γ : List Form) : Prop := ∃ d, d ∈ D ∧ ∃ Θ, d ~ Γ ++ Θ

theorem Part.perm {D : List (List Form)} {Γ Δ : List Form} (h : Γ ~ Δ) :
    Part D Γ → Part D Δ
  | ⟨d, hd, Θ, p⟩ => ⟨d, hd, Θ, p.trans (h.append_right Θ)⟩

theorem Part.left {D : List (List Form)} {Γ Δ : List Form} : Part D (Γ ++ Δ) → Part D Γ
  | ⟨d, hd, Θ, p⟩ => ⟨d, hd, Δ ++ Θ, by rw [← List.append_assoc]; exact p⟩

theorem Part.right {D : List (List Form)} {Γ Δ : List Form} : Part D (Γ ++ Δ) → Part D Δ
  | ⟨d, hd, Θ, p⟩ => ⟨d, hd, Γ ++ Θ, by perm_count [p]⟩

theorem part_of_memP {D : List (List Form)} {Γ : List Form} (h : memP D Γ = true) : Part D Γ :=
  let ⟨d, hd, p⟩ := memP_iff.1 h
  ⟨d, hd, [], by rw [List.append_nil]; exact p⟩

/-! ## The phase structure of a saturated set -/

/-- **The syntactical data of a saturated set**: two sequents are congruent
when they are permutations of each other or neither is a part of a
member; a sequent is an antiphase when it is not a member. -/
def satSyn (D : List (List Form)) (hs : saturated D = true) : Syn where
  r := fun Γ Δ => Γ ~ Δ ∨ (¬ Part D Γ ∧ ¬ Part D Δ)
  equiv :=
    ⟨fun _ => .inl (.refl _),
     fun h => h.elim (fun p => .inl p.symm) (fun b => .inr ⟨b.2, b.1⟩),
     fun h₁ h₂ => match h₁, h₂ with
      | .inl p₁, .inl p₂ => .inl (p₁.trans p₂)
      | .inl p₁, .inr b₂ => .inr ⟨fun s => b₂.1 (s.perm p₁), b₂.2⟩
      | .inr b₁, .inl p₂ => .inr ⟨b₁.1, fun s => b₁.2 (s.perm p₂.symm)⟩
      | .inr b₁, .inr b₂ => .inr ⟨b₁.1, b₂.2⟩⟩
  perm := .inl
  app := fun h₁ h₂ => match h₁, h₂ with
    | .inl p₁, .inl p₂ => .inl (p₁.append p₂)
    | .inr b₁, _ => .inr ⟨fun s => b₁.1 s.left, fun s => b₁.2 s.left⟩
    | _, .inr b₂ => .inr ⟨fun s => b₂.1 s.right, fun s => b₂.2 s.right⟩
  B := fun Γ => memP D Γ = false
  B_r := fun {Γ Δ} h hB => by
    cases hΔ : memP D Δ with
    | false => rfl
    | true =>
      rcases h with p | b
      · rw [memP_of_perm p.symm hΔ] at hB
        cases hB
      · exact absurd (part_of_memP hΔ) b.2
  ax := fun a => by
    cases h : memP D [.atom a, .natom a] with
    | false => rfl
    | true =>
      obtain ⟨Γ', p, hc⟩ := satAt_of_memP hs h
      exact absurd (perm_singleton_eq p) (of_decide_eq_true hc)
  one := by
    cases h : memP D [𝟏] with
    | false => rfl
    | true =>
      obtain ⟨Γ', p, hc⟩ := satAt_of_memP hs h
      exact absurd (perm_nil_eq p) (of_decide_eq_true hc)
  bot := fun Γ hB => by
    cases h : memP D (⊥ :: Γ) with
    | false => rfl
    | true =>
      obtain ⟨Γ', p, hc⟩ := satAt_of_memP hs h
      have hc' : memP D Γ' = true := hc
      rw [memP_of_perm p hc'] at hB
      cases hB
  top := fun Γ => by
    cases h : memP D (⊤ :: Γ) with
    | false => rfl
    | true =>
      obtain ⟨Γ', _, hc⟩ := satAt_of_memP hs h
      cases hc
  par := fun A C Γ hB => by
    cases h : memP D (A ⅋ C :: Γ) with
    | false => rfl
    | true =>
      obtain ⟨Γ', p, hc⟩ := satAt_of_memP hs h
      have hc' : memP D (A :: C :: Γ') = true := hc
      rw [memP_of_perm ((p.cons C).cons A) hc'] at hB
      cases hB
  tensor := fun A C Γ Δ hB₁ hB₂ => by
    cases h : memP D (A ⊗ C :: (Γ ++ Δ)) with
    | false => rfl
    | true =>
      obtain ⟨Γ', p, hc⟩ := satAt_of_memP hs h
      obtain ⟨q, hq, p₁, p₂⟩ := splits_complete p
      have hc' : (memP D (A :: q.1) || memP D (C :: q.2)) = true :=
        List.all_eq_true.1 (show ((splits Γ').all fun p =>
          memP D (A :: p.1) || memP D (C :: p.2)) = true from hc) q hq
      rcases Bool.or_eq_true_iff.1 hc' with m | m
      · rw [memP_of_perm (p₁.cons A) m] at hB₁
        cases hB₁
      · rw [memP_of_perm (p₂.cons C) m] at hB₂
        cases hB₂
  wth := fun A C Γ hB₁ hB₂ => by
    cases h : memP D (A & C :: Γ) with
    | false => rfl
    | true =>
      obtain ⟨Γ', p, hc⟩ := satAt_of_memP hs h
      have hc' : (memP D (A :: Γ') || memP D (C :: Γ')) = true := hc
      rcases Bool.or_eq_true_iff.1 hc' with m | m
      · rw [memP_of_perm (p.cons A) m] at hB₁
        cases hB₁
      · rw [memP_of_perm (p.cons C) m] at hB₂
        cases hB₂
  plus₁ := fun A C Γ hB => by
    cases h : memP D ((A ⊕ C) :: Γ) with
    | false => rfl
    | true =>
      obtain ⟨Γ', p, hc⟩ := satAt_of_memP hs h
      have hc' : (memP D (A :: Γ') && memP D (C :: Γ')) = true := hc
      rw [memP_of_perm (p.cons A) (Bool.and_eq_true_iff.1 hc').1] at hB
      cases hB
  plus₂ := fun A C Γ hB => by
    cases h : memP D ((A ⊕ C) :: Γ) with
    | false => rfl
    | true =>
      obtain ⟨Γ', p, hc⟩ := satAt_of_memP hs h
      have hc' : (memP D (A :: Γ') && memP D (C :: Γ')) = true := hc
      rw [memP_of_perm (p.cons C) (Bool.and_eq_true_iff.1 hc').2] at hB
      cases hB

/-- **The phase structure of a saturated set.**  Its phases: the parts of
the members, up to the order of their formulas, and one more phase for
every other sequent.  Its antiphases: the phases that are not members.
The fact of a letter `a`: the phases `Γ` with `a, Γ` an antiphase. -/
def satModel (D : List (List Form)) (hs : saturated D = true) : PhaseStructure :=
  (satSyn D hs).str

theorem length_le_flatten {D : List (List Form)} {d : List Form} (h : d ∈ D) :
    d.length ≤ D.flatten.length := by
  induction D with
  | nil => cases h
  | cons e D ih =>
    rw [List.flatten_cons, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

/-- **The structure is finite.** -/
theorem satModel_finite (D : List (List Form)) (hs : saturated D = true) :
    (satModel D hs).Finite := by
  refine ⟨(satSyn D hs).cls (replicate (D.flatten.length + 1) 𝟏) ::
    (listsUpTo D.flatten D.flatten.length).map (satSyn D hs).cls, ?_⟩
  refine Quotient.ind fun Γ => ?_
  have key : ∀ Δ : List Form, Part D Δ →
      (∀ C ∈ Δ, C ∈ D.flatten) ∧ Δ.length ≤ D.flatten.length := by
    rintro Δ ⟨d, hd, Θ, p⟩
    refine ⟨fun C hC => List.mem_flatten.2 ⟨d, hd, p.mem_iff.2 (List.mem_append.2 (.inl hC))⟩, ?_⟩
    have h₁ := length_le_flatten hd
    have h₂ := p.length_eq
    rw [List.length_append] at h₂
    omega
  by_cases c : (∀ C ∈ Γ, C ∈ D.flatten) ∧ Γ.length ≤ D.flatten.length
  · exact mem_cons.2 (.inr (mem_map.2 ⟨Γ, mem_listsUpTo _ Γ c.1 c.2, rfl⟩))
  · refine mem_cons.2 (.inl ((satSyn D hs).sound (.inr ⟨fun s => c (key Γ s), fun s => ?_⟩)))
    have := (key _ s).2
    rw [List.length_replicate] at this
    omega

/-- **No member of a saturated set holds in its structure**: by Okada's
lemma a sequent that holds there is an antiphase. -/
theorem satModel_refutes {D : List (List Form)} (hs : saturated D = true) {Γ : List Form}
    (h : memP D Γ = true) : ¬ (satModel D hs).Sat Γ := fun hsat => by
  have hB : memP D Γ = false := (satSyn D hs).B_of_sat Γ hsat
  rw [h] at hB
  cases hB

/-! ## The check, and what it gives -/

/-- **The check of the certificate**: the sequent is a member of the set,
and the set is saturated. -/
def refutedBy (D : List (List Form)) (Γ : List Form) : Bool := memP D Γ && saturated D

/-- **A sequent with a saturated set has a finite countermodel.** -/
theorem countermodel_of_refutedBy {D : List (List Form)} {Γ : List Form}
    (h : refutedBy D Γ = true) : ∃ S : PhaseStructure, S.Finite ∧ ¬ S.Sat Γ :=
  have h' := Bool.and_eq_true_iff.1 h
  ⟨satModel D h'.2, satModel_finite D h'.2, satModel_refutes h'.2 h'.1⟩

theorem not_valid_of_refutedBy {D : List (List Form)} {Γ : List Form}
    (h : refutedBy D Γ = true) : ¬ Valid Γ := fun hv =>
  let ⟨S, _, hS⟩ := countermodel_of_refutedBy h
  hS (hv S)

theorem not_derivable_of_refutedBy {D : List (List Form)} {Γ : List Form}
    (h : refutedBy D Γ = true) : ¬ Derivable Γ := fun hd =>
  not_valid_of_refutedBy h (soundness Γ hd)

/-! ## Completeness of the certificate -/

/-- **The full refutation of a sequent**: the small sequents with no
derivation without cut.  (For the proof that a certificate exists: it is
far larger than the set a failed search visits.) -/
def fullRefutation (Γ₀ : List Form) : List (List Form) :=
  (listsUpTo (subsL Γ₀) (ssize Γ₀)).filter fun Δ =>
    decide (Small Γ₀ Δ) && !decide (Nonempty (CF Δ))

theorem mem_fullRefutation {Γ₀ Δ : List Form} :
    Δ ∈ fullRefutation Γ₀ ↔ Small Γ₀ Δ ∧ ¬ Nonempty (CF Δ) := by
  unfold fullRefutation
  rw [List.mem_filter, Bool.and_eq_true_iff, decide_eq_true_iff, Bool.not_eq_true',
    decide_eq_false_iff_not]
  exact ⟨fun h => h.2, fun h => ⟨mem_listsUpTo _ Δ h.1.1
    (Nat.le_trans (length_le_ssize Δ) h.1.2), h⟩⟩

theorem memP_fullRefutation {Γ₀ Δ : List Form} (s : Small Γ₀ Δ) (n : ¬ Nonempty (CF Δ)) :
    memP (fullRefutation Γ₀) Δ = true :=
  memP_of_mem (mem_fullRefutation.2 ⟨s, n⟩)

/-- The full refutation is saturated: a small sequent with no derivation
is the conclusion of no rule whose premises all have derivations, and the
premises of a rule with a small conclusion are small. -/
theorem saturated_fullRefutation (Γ₀ : List Form) : saturated (fullRefutation Γ₀) = true := by
  refine List.all_eq_true.2 fun d hd => List.all_eq_true.2 fun ⟨X, Γ⟩ hp => ?_
  obtain ⟨sd, nd⟩ := mem_fullRefutation.1 hd
  have p : d ~ X :: Γ := picks_perm hp
  have s : Small Γ₀ (X :: Γ) := sd.perm p
  have n : ¬ Nonempty (CF (X :: Γ)) := fun ⟨c⟩ => nd ⟨c.exch p.symm⟩
  show satAt (fullRefutation Γ₀) X Γ = true
  cases X with
  | atom a => exact decide_eq_true fun e => n ⟨.ax (.atom a) (e ▸ .refl _)⟩
  | natom a => rfl
  | one => exact decide_eq_true fun e => n ⟨.one (e ▸ .refl _)⟩
  | bot => exact memP_fullRefutation s.tail fun ⟨c⟩ => n ⟨.bot Γ (.refl _) c⟩
  | top => exact absurd ⟨.top Γ (.refl _)⟩ n
  | zero => rfl
  | par A C => exact memP_fullRefutation s.par fun ⟨c⟩ => n ⟨.par A C Γ (.refl _) c⟩
  | tensor A C =>
    refine List.all_eq_true.2 fun q hq => ?_
    have pq : Γ ~ q.1 ++ q.2 := splits_perm hq
    have s' : Small Γ₀ (A ⊗ C :: (q.1 ++ q.2)) := s.perm (pq.cons _)
    have s₁ : Small Γ₀ (A :: q.1) :=
      Small.left (Γ := A :: q.1) (Δ := q.2)
        (s'.sub₁ (mem_subs_left (.inl rfl)) (by simp only [Form.size]; omega))
    have s₂ : Small Γ₀ (C :: q.2) :=
      Small.right (Γ := q.1) (Δ := C :: q.2)
        ((s'.sub₁ (mem_subs_right (.inl rfl)) (by simp only [Form.size]; omega)).perm
          (by perm_count []))
    by_cases c₁ : Nonempty (CF (A :: q.1))
    · by_cases c₂ : Nonempty (CF (C :: q.2))
      · obtain ⟨d₁⟩ := c₁
        obtain ⟨d₂⟩ := c₂
        exact absurd ⟨.tensor A C q.1 q.2 (pq.cons _) d₁ d₂⟩ n
      · exact Bool.or_eq_true_iff.2 (.inr (memP_fullRefutation s₂ c₂))
    · exact Bool.or_eq_true_iff.2 (.inl (memP_fullRefutation s₁ c₁))
  | wth A C =>
    have s₁ : Small Γ₀ (A :: Γ) :=
      s.sub₁ (mem_subs_left (.inr (.inr (.inl rfl)))) (by simp only [Form.size]; omega)
    have s₂ : Small Γ₀ (C :: Γ) :=
      s.sub₁ (mem_subs_right (.inr (.inr (.inl rfl)))) (by simp only [Form.size]; omega)
    by_cases c₁ : Nonempty (CF (A :: Γ))
    · by_cases c₂ : Nonempty (CF (C :: Γ))
      · obtain ⟨d₁⟩ := c₁
        obtain ⟨d₂⟩ := c₂
        exact absurd ⟨.wth A C Γ (.refl _) d₁ d₂⟩ n
      · exact Bool.or_eq_true_iff.2 (.inr (memP_fullRefutation s₂ c₂))
    · exact Bool.or_eq_true_iff.2 (.inl (memP_fullRefutation s₁ c₁))
  | plus A C =>
    have s₁ : Small Γ₀ (A :: Γ) :=
      s.sub₁ (mem_subs_left (.inr (.inr (.inr rfl)))) (by simp only [Form.size]; omega)
    have s₂ : Small Γ₀ (C :: Γ) :=
      s.sub₁ (mem_subs_right (.inr (.inr (.inr rfl)))) (by simp only [Form.size]; omega)
    exact Bool.and_eq_true_iff.2
      ⟨memP_fullRefutation s₁ fun ⟨c⟩ => n ⟨.plus₁ A C Γ (.refl _) c⟩,
       memP_fullRefutation s₂ fun ⟨c⟩ => n ⟨.plus₂ A C Γ (.refl _) c⟩⟩

/-- **The certificate is complete**: a sequent with no derivation has a
saturated set of which it is a member. -/
theorem refutation_complete (Γ : List Form) (h : ¬ Derivable Γ) :
    refutedBy (fullRefutation Γ) Γ = true :=
  Bool.and_eq_true_iff.2
    ⟨memP_fullRefutation (small_self Γ) fun ⟨c⟩ => h ⟨c.toFam⟩, saturated_fullRefutation Γ⟩

/-- A sequent has no derivation exactly if some set of sequents refutes
it. -/
theorem not_derivable_iff_refuted (Γ : List Form) :
    ¬ Derivable Γ ↔ ∃ D, refutedBy D Γ = true :=
  ⟨fun h => ⟨_, refutation_complete Γ h⟩, fun ⟨_, h⟩ => not_derivable_of_refutedBy h⟩

end MALL

#axioms_within_file [propext, Quot.sound]
