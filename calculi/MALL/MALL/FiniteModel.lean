/-
The finite model property of MALL.

Source: Y. Lafont, *The finite model property for various fragments of
linear logic*, J. Symbolic Logic 62 (1997), in the author's version, p. 3,
Theorem 2 and the construction before it: the syntactical model of a
calculus `MALL⟨A⟩` in which every sequent that is not below `A` is an
axiom, and its quotient by the congruence that collapses those sequents,
which is finite.

Here "below" is a simpler relation than Lafont's `⊑`, with the same three
properties: a sequent is *small* (for a sequent `Γ₀`) when its formulas
are subformulas of formulas of `Γ₀` and its size is at most that of `Γ₀`.
Then (i) the premises of a rule with a small conclusion are small; (ii) a
part of a small sequent is small, so the sequents that are not small are
an ideal; (iii) there are finitely many small sequents.  The model is the
instance of `Syn` (`MALL/Completeness.lean`) whose congruence is
"permutations of each other, or neither is small" and whose antiphases are
"derivable without cut, or not small".  Theory file: it ends with its
bound on axioms.
-/
import MALL.Completeness
import MALL.Decide

namespace MALL

open List

/-! ## Subformulas and sizes -/

/-- The subformulas of a formula, itself first. -/
def Form.subs : Form → List Form
  | .atom n => [.atom n]
  | .natom n => [.natom n]
  | .one => [.one]
  | .bot => [.bot]
  | .top => [.top]
  | .zero => [.zero]
  | .tensor A B => .tensor A B :: (A.subs ++ B.subs)
  | .par A B => .par A B :: (A.subs ++ B.subs)
  | .wth A B => .wth A B :: (A.subs ++ B.subs)
  | .plus A B => .plus A B :: (A.subs ++ B.subs)

theorem Form.mem_subs_self (A : Form) : A ∈ A.subs := by
  cases A <;> exact mem_cons_self ..

theorem Form.subs_trans {X C D : Form} (hC : C ∈ D.subs) (hX : X ∈ C.subs) : X ∈ D.subs := by
  induction D with
  | atom n | natom n | one | bot | top | zero =>
    rcases mem_cons.1 hC with e | e
    · subst e; exact hX
    · cases e
  | tensor A B ihA ihB | par A B ihA ihB | wth A B ihA ihB | plus A B ihA ihB =>
    rcases mem_cons.1 hC with e | e
    · subst e; exact hX
    · rcases mem_append.1 e with e | e
      · exact mem_cons.2 (.inr (mem_append.2 (.inl (ihA e))))
      · exact mem_cons.2 (.inr (mem_append.2 (.inr (ihB e))))

/-- The subformulas of the formulas of a sequent. -/
def subsL (Γ₀ : List Form) : List Form := Γ₀.flatMap Form.subs

theorem mem_subsL_of_mem {Γ₀ : List Form} {C : Form} (h : C ∈ Γ₀) : C ∈ subsL Γ₀ :=
  mem_flatMap.2 ⟨C, h, C.mem_subs_self⟩

theorem subsL_trans {Γ₀ : List Form} {X C : Form} (hC : C ∈ subsL Γ₀) (hX : X ∈ C.subs) :
    X ∈ subsL Γ₀ := by
  obtain ⟨D, hD, hCD⟩ := mem_flatMap.1 hC
  exact mem_flatMap.2 ⟨D, hD, Form.subs_trans hCD hX⟩

theorem length_le_ssize (Γ : List Form) : Γ.length ≤ ssize Γ := by
  induction Γ with
  | nil => exact Nat.le_refl _
  | cons A Γ ih =>
    have := A.size_pos
    simp only [length_cons, ssize]; omega

/-! ## Small sequents -/

/-- **A small sequent**, for the sequent `Γ₀`: its formulas are subformulas
of formulas of `Γ₀`, and its size is at most that of `Γ₀`. -/
def Small (Γ₀ Γ : List Form) : Prop := (∀ C ∈ Γ, C ∈ subsL Γ₀) ∧ ssize Γ ≤ ssize Γ₀

instance (Γ₀ Γ : List Form) : Decidable (Small Γ₀ Γ) := by
  unfold Small; exact inferInstance

variable {Γ₀ : List Form}

theorem small_self (Γ₀ : List Form) : Small Γ₀ Γ₀ :=
  ⟨fun _ h => mem_subsL_of_mem h, Nat.le_refl _⟩

theorem Small.perm {Γ Δ : List Form} (h : Γ ~ Δ) (s : Small Γ₀ Γ) : Small Γ₀ Δ :=
  ⟨fun C hC => s.1 C (h.mem_iff.2 hC), by rw [← ssize_perm h]; exact s.2⟩

/-- A part of a small sequent is small: the sequents that are not small
are an ideal. -/
theorem Small.left {Γ Δ : List Form} (s : Small Γ₀ (Γ ++ Δ)) : Small Γ₀ Γ :=
  ⟨fun C hC => s.1 C (mem_append.2 (.inl hC)), by have := s.2; rw [ssize_append] at this; omega⟩

theorem Small.right {Γ Δ : List Form} (s : Small Γ₀ (Γ ++ Δ)) : Small Γ₀ Δ :=
  ⟨fun C hC => s.1 C (mem_append.2 (.inr hC)), by have := s.2; rw [ssize_append] at this; omega⟩

theorem Small.tail {A : Form} {Γ : List Form} (s : Small Γ₀ (A :: Γ)) : Small Γ₀ Γ :=
  Small.right (Γ := [A]) s

/-- The premise of a rule with a small conclusion is small: the formula
`X`, a subformula of the principal formula `C` and smaller than it, in
place of `C`. -/
theorem Small.sub₁ {C X : Form} {Γ : List Form} (s : Small Γ₀ (C :: Γ)) (hX : X ∈ C.subs)
    (hs : X.size ≤ C.size) : Small Γ₀ (X :: Γ) :=
  ⟨fun D hD => (mem_cons.1 hD).elim
      (fun e => e ▸ subsL_trans (s.1 C (mem_cons_self ..)) hX)
      (fun h => s.1 D (mem_cons.2 (.inr h))),
   by have := s.2; simp only [ssize] at this ⊢; omega⟩

theorem mem_subs_left {A B C : Form}
    (h : C = .tensor A B ∨ C = .par A B ∨ C = .wth A B ∨ C = .plus A B) : A ∈ C.subs := by
  rcases h with rfl | rfl | rfl | rfl <;>
    exact mem_cons.2 (.inr (mem_append.2 (.inl A.mem_subs_self)))

theorem mem_subs_right {A B C : Form}
    (h : C = .tensor A B ∨ C = .par A B ∨ C = .wth A B ∨ C = .plus A B) : B ∈ C.subs := by
  rcases h with rfl | rfl | rfl | rfl <;>
    exact mem_cons.2 (.inr (mem_append.2 (.inr B.mem_subs_self)))

theorem Small.par {A B : Form} {Γ : List Form} (s : Small Γ₀ (A ⅋ B :: Γ)) :
    Small Γ₀ (A :: B :: Γ) :=
  ⟨fun D hD => by
      have hC := s.1 (A ⅋ B) (mem_cons_self ..)
      rcases mem_cons.1 hD with e | hD
      · exact e ▸ subsL_trans hC (mem_subs_left (.inr (.inl rfl)))
      · rcases mem_cons.1 hD with e | hD
        · exact e ▸ subsL_trans hC (mem_subs_right (.inr (.inl rfl)))
        · exact s.1 D (mem_cons.2 (.inr hD)),
   by have := s.2; simp only [ssize, Form.size] at this ⊢; omega⟩

/-! ## The finite model -/

/-- **The syntactical data of the finite model** of a sequent `Γ₀`: two
sequents are congruent when they are permutations of each other or neither
is small; a sequent is an antiphase when it is derivable without cut or is
not small. -/
def fmSyn (Γ₀ : List Form) : Syn where
  r := fun Γ Δ => Γ ~ Δ ∨ (¬ Small Γ₀ Γ ∧ ¬ Small Γ₀ Δ)
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
  B := fun Γ => Nonempty (CF Γ) ∨ ¬ Small Γ₀ Γ
  B_r := fun h hB => match h, hB with
    | .inl p, .inl ⟨d⟩ => .inl ⟨d.exch p⟩
    | .inl p, .inr b => .inr fun s => b (s.perm p.symm)
    | .inr b, _ => .inr b.2
  ax := fun a => .inl ⟨.ax (.atom a) (.refl _)⟩
  one := .inl ⟨.one (.refl _)⟩
  bot := fun Γ h => h.elim (fun ⟨d⟩ => .inl ⟨.bot Γ (.refl _) d⟩) (fun b => .inr fun s => b s.tail)
  top := fun Γ => .inl ⟨.top Γ (.refl _)⟩
  par := fun A C Γ h =>
    h.elim (fun ⟨d⟩ => .inl ⟨.par A C Γ (.refl _) d⟩) (fun b => .inr fun s => b s.par)
  tensor := fun A C Γ Δ h₁ h₂ => match h₁, h₂ with
    | .inl ⟨d₁⟩, .inl ⟨d₂⟩ => .inl ⟨.tensor A C Γ Δ (.refl _) d₁ d₂⟩
    | .inr b, _ => .inr fun s => b
        ((Small.left (Γ := A :: Γ) (Δ := Δ)
          (s.sub₁ (mem_subs_left (.inl rfl)) (by simp only [Form.size]; omega))))
    | _, .inr b => .inr fun s => b
        ((Small.right (Γ := Γ) (Δ := C :: Δ)
          ((s.sub₁ (mem_subs_right (.inl rfl)) (by simp only [Form.size]; omega)).perm
            (by perm_count []))))
  wth := fun A C Γ h₁ h₂ => match h₁, h₂ with
    | .inl ⟨d₁⟩, .inl ⟨d₂⟩ => .inl ⟨.wth A C Γ (.refl _) d₁ d₂⟩
    | .inr b, _ => .inr fun s => b
        (s.sub₁ (mem_subs_left (.inr (.inr (.inl rfl)))) (by simp only [Form.size]; omega))
    | _, .inr b => .inr fun s => b
        (s.sub₁ (mem_subs_right (.inr (.inr (.inl rfl)))) (by simp only [Form.size]; omega))
  plus₁ := fun A C Γ h =>
    h.elim (fun ⟨d⟩ => .inl ⟨.plus₁ A C Γ (.refl _) d⟩) (fun b => .inr fun s => b
      (s.sub₁ (mem_subs_left (.inr (.inr (.inr rfl)))) (by simp only [Form.size]; omega)))
  plus₂ := fun A C Γ h =>
    h.elim (fun ⟨d⟩ => .inl ⟨.plus₂ A C Γ (.refl _) d⟩) (fun b => .inr fun s => b
      (s.sub₁ (mem_subs_right (.inr (.inr (.inr rfl)))) (by simp only [Form.size]; omega)))

/-- **The finite phase structure of a sequent** (Lafont's
`MALL•⟨A⟩/∼_A`). -/
def finiteModel (Γ₀ : List Form) : PhaseStructure := (fmSyn Γ₀).str

/-- The lists of length at most `n` over the alphabet `L`. -/
def listsUpTo (L : List Form) : Nat → List (List Form)
  | 0 => [[]]
  | n + 1 => [] :: L.flatMap fun a => (listsUpTo L n).map (a :: ·)

theorem mem_listsUpTo {L : List Form} : ∀ (n : Nat) (Γ : List Form),
    (∀ C ∈ Γ, C ∈ L) → Γ.length ≤ n → Γ ∈ listsUpTo L n
  | 0, [], _, _ => mem_cons_self ..
  | 0, _ :: _, _, h => absurd h (by simp)
  | _ + 1, [], _, _ => mem_cons_self ..
  | n + 1, A :: Γ, hm, h =>
    mem_cons.2 (.inr (mem_flatMap.2 ⟨A, hm A (mem_cons_self ..),
      mem_map.2 ⟨Γ, mem_listsUpTo n Γ (fun C hC => hm C (mem_cons.2 (.inr hC)))
        (Nat.le_of_succ_le_succ h), rfl⟩⟩))

theorem ssize_replicate_one (n : Nat) : ssize (replicate n 𝟏) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [replicate_succ, ssize, Form.size, ih]; omega

/-- **The model is finite**: its phases are the small sequents, of which
there are finitely many, and one more, the class of all the others. -/
theorem finiteModel_finite (Γ₀ : List Form) : (finiteModel Γ₀).Finite := by
  refine ⟨(fmSyn Γ₀).cls (replicate (ssize Γ₀ + 1) 𝟏) ::
    (listsUpTo (subsL Γ₀) (ssize Γ₀)).map (fmSyn Γ₀).cls, ?_⟩
  refine Quotient.ind fun Γ => ?_
  by_cases s : Small Γ₀ Γ
  · exact mem_cons.2 (.inr (mem_map.2 ⟨Γ, mem_listsUpTo _ Γ s.1
      (Nat.le_trans (length_le_ssize Γ) s.2), rfl⟩))
  · refine mem_cons.2 (.inl ((fmSyn Γ₀).sound (.inr ⟨s, fun s' => ?_⟩)))
    have := s'.2
    rw [ssize_replicate_one] at this
    omega

/-- A sequent that is valid in its finite model has a derivation without
cut (Lafont, Theorem 2, (3) ⟹ (1)). -/
theorem cf_of_sat_finiteModel (Γ₀ : List Form) (h : (finiteModel Γ₀).Sat Γ₀) :
    Nonempty (CF Γ₀) :=
  ((fmSyn Γ₀).B_of_sat Γ₀ h).elim id (fun b => absurd (small_self Γ₀) b)

/-- **The finite model property** (Lafont, Theorem 2, (2) ⟹ (1)). -/
theorem finiteModelProperty : FiniteModelProperty := fun Γ h =>
  let ⟨d⟩ := cf_of_sat_finiteModel Γ (h (finiteModel Γ) (finiteModel_finite Γ))
  ⟨d.toFam⟩

/-- The same, as a countermodel: a sequent that is not derivable is
refuted by a finite phase structure. -/
theorem finite_countermodel (Γ : List Form) (h : ¬ Derivable Γ) :
    ∃ S : PhaseStructure, S.Finite ∧ ¬ S.Sat Γ :=
  ⟨finiteModel Γ, finiteModel_finite Γ, fun hs =>
    let ⟨d⟩ := cf_of_sat_finiteModel Γ hs
    h ⟨d.toFam⟩⟩

end MALL

#axioms_within_file [propext, Quot.sound]
