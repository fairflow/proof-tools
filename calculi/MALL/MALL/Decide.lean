/-
A decision procedure for derivability without cut in MALL: a search for
a derivation, by structural recursion on a bound on the size of the
sequent, and its completeness.

Read upwards, every rule of `CF` removes a connective or a constant, so
the size of the sequent (`ssize`) bounds the height of a derivation
without cut and the depth of the search.  The search is sound by its
type: it returns a derivation.  It is complete (`search_complete`): where
there is a derivation, the search with a bound of at least the size finds
one.  So `Nonempty (CF Γ)` is decidable (`decCF`), and the kernel can
evaluate the decision (`decide +kernel`).

Theory file: it ends with its bound on axioms.
-/
import MALL.Perm
import MALL.System

namespace MALL

open List

/-! ## The size of a sequent -/

theorem ssize_append (l₁ l₂ : List Form) : ssize (l₁ ++ l₂) = ssize l₁ + ssize l₂ := by
  induction l₁ with
  | nil => simp [ssize]
  | cons a l ih => simp only [List.cons_append, ssize, ih]; omega

/-- Permutations of a sequent have its size. -/
theorem ssize_perm {l₁ l₂ : List Form} (h : l₁ ~ l₂) : ssize l₁ = ssize l₂ := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [ssize, ih]
  | swap a b l => simp only [ssize]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The first answer over a list -/

/-- The first answer of `f` over the members of `l`.  The function is
given, with each member, the proof that it is one. -/
def firstSome {α β : Type} : (l : List α) → ((a : α) → a ∈ l → Option β) → Option β
  | [], _ => none
  | a :: l, f =>
    match f a (List.mem_cons_self ..) with
    | some b => some b
    | none => firstSome l fun x h => f x (List.mem_cons_of_mem a h)

/-- Where `f` answers at some member, there is a first answer. -/
theorem firstSome_isSome {α β : Type} {l : List α} {f : (a : α) → a ∈ l → Option β}
    {a : α} (ha : a ∈ l) (h : (f a ha).isSome = true) : (firstSome l f).isSome = true := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    unfold firstSome
    cases hb : f b (List.mem_cons_self ..) with
    | some c => rfl
    | none =>
      rcases List.mem_cons.1 ha with e | e
      · subst e
        rw [hb] at h
        cases h
      · exact ih (f := fun x h => f x (List.mem_cons_of_mem b h)) e h

/-! ## The enumerations -/

/-- Every member of a list, each with the rest. -/
def picks : List Form → List (Form × List Form)
  | [] => []
  | a :: l => (a, l) :: (picks l).map fun p => (p.1, a :: p.2)

/-- A pick is a formula of the list and the rest of it. -/
theorem picks_perm {l : List Form} {p : Form × List Form} (h : p ∈ picks l) :
    l ~ p.1 :: p.2 := by
  induction l generalizing p with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with e | h
    · subst e
      exact .refl _
    · obtain ⟨p', hp', e⟩ := List.mem_map.1 h
      subst e
      exact ((ih hp').cons a).trans (.swap ..)

/-- Every formula of the list is picked. -/
theorem picks_mem {l : List Form} {x : Form} (h : x ∈ l) : ∃ r, (x, r) ∈ picks l := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with e | h
    · subst e
      exact ⟨l, List.mem_cons_self ..⟩
    · obtain ⟨r, hr⟩ := ih h
      exact ⟨a :: r, List.mem_cons_of_mem _ (List.mem_map.2 ⟨(x, r), hr, rfl⟩)⟩

/-- Every way to split a list into two sublists: each formula goes to the
left part or to the right one. -/
def splits : List Form → List (List Form × List Form)
  | [] => [([], [])]
  | a :: l =>
    (splits l).map (fun p => (a :: p.1, p.2)) ++ (splits l).map (fun p => (p.1, a :: p.2))

/-- The two parts of a split are, together, the list. -/
theorem splits_perm {l : List Form} {p : List Form × List Form} (h : p ∈ splits l) :
    l ~ p.1 ++ p.2 := by
  induction l generalizing p with
  | nil =>
    rcases List.mem_cons.1 h with e | h
    · subst e
      exact .refl _
    · cases h
  | cons a l ih =>
    rcases List.mem_append.1 h with h | h
    · obtain ⟨p', hp', e⟩ := List.mem_map.1 h
      subst e
      exact (ih hp').cons a
    · obtain ⟨p', hp', e⟩ := List.mem_map.1 h
      subst e
      have := ih hp'
      show a :: l ~ p'.1 ++ a :: p'.2
      perm_count [this]

/-- Every way to divide the list into two is, up to the order within each
part, a split. -/
theorem splits_complete {l Γ Δ : List Form} (h : l ~ Γ ++ Δ) :
    ∃ p, p ∈ splits l ∧ p.1 ~ Γ ∧ p.2 ~ Δ := by
  induction l generalizing Γ Δ with
  | nil =>
    have e := perm_nil_eq h.symm
    have e₁ : Γ = [] := by cases Γ with
      | nil => rfl
      | cons _ _ => cases e
    subst e₁
    have e₂ : Δ = [] := e
    subst e₂
    exact ⟨([], []), List.mem_cons_self .., .refl _, .refl _⟩
  | cons a l ih =>
    have ha : a ∈ Γ ++ Δ := h.mem_iff.1 (List.mem_cons_self ..)
    rcases List.mem_append.1 ha with ha | ha
    · have hp := perm_cons_erase ha
      have h' : l ~ Γ.erase a ++ Δ := by perm_count [h, hp]
      obtain ⟨p, hp', h₁, h₂⟩ := ih h'
      refine ⟨(a :: p.1, p.2), List.mem_append.2 (.inl (List.mem_map.2 ⟨p, hp', rfl⟩)), ?_, h₂⟩
      show a :: p.1 ~ Γ
      perm_count [h₁, hp]
    · have hp := perm_cons_erase ha
      have h' : l ~ Γ ++ Δ.erase a := by perm_count [h, hp]
      obtain ⟨p, hp', h₁, h₂⟩ := ih h'
      refine ⟨(p.1, a :: p.2), List.mem_append.2 (.inr (List.mem_map.2 ⟨p, hp', rfl⟩)), h₁, ?_⟩
      show a :: p.2 ~ Δ
      perm_count [h₂, hp]

/-! ## The two rules without a principal occurrence to choose -/

/-- The logical axiom: the sequent has exactly two formulas, the second
the negation of the first. -/
def axiomCase : (Γ : List Form) → Option (CF Γ)
  | [A, B] => if h : B = Aᗮ then some (.ax A (h ▸ .refl _)) else none
  | _ => none

/-- The axiom `⊢ 1`: the sequent is `[𝟏]`. -/
def oneCase : (Γ : List Form) → Option (CF Γ)
  | [.one] => some (.one (.refl _))
  | _ => none

/-- A permutation of a list of two is it or its reverse. -/
theorem perm_pair {l : List Form} {a b : Form} (h : l ~ [a, b]) : l = [a, b] ∨ l = [b, a] := by
  match l, h with
  | [], h => exact absurd h.length_eq (fun e => by cases e)
  | [_], h => exact absurd h.length_eq (fun e => by cases e)
  | [x, y], h =>
    have hx : x ∈ [a, b] := h.mem_iff.1 (List.mem_cons_self ..)
    rcases List.mem_cons.1 hx with e | hx
    · subst e
      have : [y] ~ [b] := by perm_count [h]
      cases perm_singleton_eq this
      exact .inl rfl
    · have e : x = b := by
        rcases List.mem_cons.1 hx with e | e
        · exact e
        · cases e
      subst e
      have : [y] ~ [a] := by perm_count [h]
      cases perm_singleton_eq this
      exact .inr rfl
  | _ :: _ :: _ :: l, h =>
    have e : l.length + 3 = 2 := h.length_eq
    omega

theorem axiomCase_complete {Γ : List Form} {A : Form} (h : Γ ~ [A, Aᗮ]) :
    (axiomCase Γ).isSome = true := by
  rcases perm_pair h with e | e
  · subst e
    simp [axiomCase]
  · subst e
    simp [axiomCase, Form.neg_neg]

theorem oneCase_complete {Γ : List Form} (h : Γ ~ [𝟏]) : (oneCase Γ).isSome = true := by
  cases perm_singleton_eq h
  rfl

/-! ## One rule, read upwards -/

/-- **The rule of a principal formula**: `Γ` is `C` and `Δ`; `C` is taken
as principal, and the premises are sought with `rec`.  ⊤ has no premise;
⊥ and ⅋ have one; & has two with the same context; ⊕ has either of two;
⊗ tries every split of `Δ`.  A letter, the dual of one, `𝟏` or `𝟎` is the
principal formula of no rule that has a context. -/
def searchStep (rec : (Γ : List Form) → Option (CF Γ)) (Γ : List Form) :
    (C : Form) → (Δ : List Form) → Γ ~ C :: Δ → Option (CF Γ)
  | .top, Δ, h => some (.top Δ h)
  | .bot, Δ, h =>
    match rec Δ with
    | some d => some (.bot Δ h d)
    | none => none
  | .par A B, Δ, h =>
    match rec (A :: B :: Δ) with
    | some d => some (.par A B Δ h d)
    | none => none
  | .wth A B, Δ, h =>
    match rec (A :: Δ) with
    | none => none
    | some d₁ =>
      match rec (B :: Δ) with
      | some d₂ => some (.wth A B Δ h d₁ d₂)
      | none => none
  | .plus A B, Δ, h =>
    match rec (A :: Δ) with
    | some d => some (.plus₁ A B Δ h d)
    | none =>
      match rec (B :: Δ) with
      | some d => some (.plus₂ A B Δ h d)
      | none => none
  | .tensor A B, Δ, h =>
    firstSome (splits Δ) fun s hs =>
      match rec (A :: s.1) with
      | none => none
      | some d₁ =>
        match rec (B :: s.2) with
        | some d₂ => some (.tensor A B s.1 s.2 (h.trans ((splits_perm hs).cons _)) d₁ d₂)
        | none => none
  | _, _, _ => none

/-- **The search for a derivation without cut**, with a bound on its
depth: the logical axiom, the axiom `⊢ 1`, and then, for each formula
occurrence of the sequent in turn, the rule of that occurrence. -/
def search : Nat → (Γ : List Form) → Option (CF Γ)
  | 0, _ => none
  | n + 1, Γ =>
    match axiomCase Γ with
    | some d => some d
    | none =>
      match oneCase Γ with
      | some d => some d
      | none => firstSome (picks Γ) fun p hp => searchStep (search n) Γ p.1 p.2 (picks_perm hp)

/-- The search, with the size of the sequent for its bound. -/
def searchCF (Γ : List Form) : Option (CF Γ) := search (ssize Γ) Γ

/-! ## Completeness -/

/-- A sequent with a derivation has a formula. -/
theorem CF.ssize_pos {Γ : List Form} (d : CF Γ) : 0 < ssize Γ := by
  have key : ∀ {C : Form} {Δ : List Form}, Γ ~ C :: Δ → 0 < ssize Γ := by
    intro C Δ h
    have := ssize_perm h
    have := C.size_pos
    simp only [ssize] at *
    omega
  cases d with
  | ax A h => exact key h
  | top Γ' h => exact key h
  | wth A B Γ' h _ _ => exact key h
  | plus₁ A B Γ' h _ => exact key h
  | plus₂ A B Γ' h _ => exact key h
  | one h => exact key h
  | bot Γ' h _ => exact key h
  | tensor A B Γ₁ Γ₂ h _ _ => exact key h
  | par A B Γ' h _ => exact key h

/-- **One rule, read upwards, is complete**: where `rec` finds a
derivation of every derivable sequent of size at most `n`, and `Γ` of
size at most `n + 1` has a derivation, either `Γ` is a logical axiom, or
it is `⊢ 1`, or the last rule of the derivation has a principal formula
`C`, and `searchStep` with `C` as principal, whatever list is given as the
rest, finds a derivation. -/
theorem searchStep_complete {rec : (Γ : List Form) → Option (CF Γ)} {n : Nat}
    (hrec : ∀ Γ, ssize Γ ≤ n → Nonempty (CF Γ) → (rec Γ).isSome = true)
    {Γ : List Form} (hΓ : ssize Γ ≤ n + 1) (d : CF Γ) :
    (∃ A, Γ ~ [A, Aᗮ]) ∨ Γ ~ [𝟏] ∨
      ∃ C, C ∈ Γ ∧ ∀ Δ (h : Γ ~ C :: Δ), (searchStep rec Γ C Δ h).isSome = true := by
  have mem : ∀ {C : Form} {Γ' : List Form}, Γ ~ C :: Γ' → C ∈ Γ :=
    fun h => h.mem_iff.2 (List.mem_cons_self ..)
  cases d with
  | ax A h => exact .inl ⟨A, h⟩
  | one h => exact .inr (.inl h)
  | top Γ' h =>
    refine .inr (.inr ⟨_, mem h, fun Δ h' => ?_⟩)
    rfl
  | bot Γ' h d =>
    refine .inr (.inr ⟨_, mem h, fun Δ h' => ?_⟩)
    have e : Γ' ~ Δ := by perm_count [h, h']
    have hs := ssize_perm h'
    simp only [ssize, Form.size] at hs
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1 (hrec Δ (by omega) ⟨d.exch e⟩)
    simp only [searchStep, hd']
    rfl
  | par A B Γ' h d =>
    refine .inr (.inr ⟨_, mem h, fun Δ h' => ?_⟩)
    have e : A :: B :: Γ' ~ A :: B :: Δ := by perm_count [h, h']
    have hs := ssize_perm h'
    simp only [ssize, Form.size] at hs
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1
      (hrec (A :: B :: Δ) (by simp only [ssize]; omega) ⟨d.exch e⟩)
    simp only [searchStep, hd']
    rfl
  | wth A B Γ' h d₁ d₂ =>
    refine .inr (.inr ⟨_, mem h, fun Δ h' => ?_⟩)
    have e₁ : A :: Γ' ~ A :: Δ := by perm_count [h, h']
    have e₂ : B :: Γ' ~ B :: Δ := by perm_count [h, h']
    have hs := ssize_perm h'
    simp only [ssize, Form.size] at hs
    obtain ⟨d₁', hd₁⟩ := Option.isSome_iff_exists.1
      (hrec (A :: Δ) (by simp only [ssize]; omega) ⟨d₁.exch e₁⟩)
    obtain ⟨d₂', hd₂⟩ := Option.isSome_iff_exists.1
      (hrec (B :: Δ) (by simp only [ssize]; omega) ⟨d₂.exch e₂⟩)
    simp only [searchStep, hd₁, hd₂]
    rfl
  | plus₁ A B Γ' h d =>
    refine .inr (.inr ⟨_, mem h, fun Δ h' => ?_⟩)
    have e : A :: Γ' ~ A :: Δ := by perm_count [h, h']
    have hs := ssize_perm h'
    simp only [ssize, Form.size] at hs
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1
      (hrec (A :: Δ) (by simp only [ssize]; omega) ⟨d.exch e⟩)
    simp only [searchStep, hd']
    rfl
  | plus₂ A B Γ' h d =>
    refine .inr (.inr ⟨_, mem h, fun Δ h' => ?_⟩)
    have e : B :: Γ' ~ B :: Δ := by perm_count [h, h']
    have hs := ssize_perm h'
    simp only [ssize, Form.size] at hs
    obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1
      (hrec (B :: Δ) (by simp only [ssize]; omega) ⟨d.exch e⟩)
    simp only [searchStep]
    cases rec (A :: Δ) with
    | some _ => rfl
    | none =>
      simp only [hd']
      rfl
  | tensor A B Γ₁ Γ₂ h d₁ d₂ =>
    refine .inr (.inr ⟨_, mem h, fun Δ h' => ?_⟩)
    have e : Δ ~ Γ₁ ++ Γ₂ := by perm_count [h, h']
    obtain ⟨s, hs, h₁, h₂⟩ := splits_complete e
    have e₁ : A :: Γ₁ ~ A :: s.1 := (h₁.cons A).symm
    have e₂ : B :: Γ₂ ~ B :: s.2 := (h₂.cons B).symm
    have hs₁ := ssize_perm h'
    have hs₂ := ssize_perm (splits_perm hs)
    rw [ssize_append] at hs₂
    simp only [ssize, Form.size] at hs₁
    obtain ⟨d₁', hd₁⟩ := Option.isSome_iff_exists.1
      (hrec (A :: s.1) (by simp only [ssize]; omega) ⟨d₁.exch e₁⟩)
    obtain ⟨d₂', hd₂⟩ := Option.isSome_iff_exists.1
      (hrec (B :: s.2) (by simp only [ssize]; omega) ⟨d₂.exch e₂⟩)
    simp only [searchStep]
    refine firstSome_isSome hs ?_
    simp only [hd₁, hd₂]
    rfl

/-- **The search is complete**: where a sequent of size at most `n` has a
derivation without cut, the search with the bound `n` finds one.
(Soundness is by the type of `search`: what it finds is a derivation.) -/
theorem search_complete : ∀ (n : Nat) (Γ : List Form), ssize Γ ≤ n → Nonempty (CF Γ) →
    (search n Γ).isSome = true
  | 0, _, hs, ⟨d⟩ => absurd d.ssize_pos (by omega)
  | n + 1, Γ, hs, ⟨d⟩ => by
    unfold search
    cases hax : axiomCase Γ with
    | some _ => rfl
    | none =>
      cases hone : oneCase Γ with
      | some _ => rfl
      | none =>
        rcases searchStep_complete (search_complete n) hs d with ⟨A, h⟩ | h | ⟨C, hC, hstep⟩
        · have := axiomCase_complete h
          rw [hax] at this
          cases this
        · have := oneCase_complete h
          rw [hone] at this
          cases this
        · obtain ⟨r, hr⟩ := picks_mem hC
          exact firstSome_isSome hr (hstep r (picks_perm hr))

/-- The search with the size of the sequent for its bound finds a
derivation exactly where there is one. -/
theorem searchCF_isSome_iff (Γ : List Form) : (searchCF Γ).isSome = true ↔ Nonempty (CF Γ) := by
  constructor
  · intro h
    obtain ⟨d, _⟩ := Option.isSome_iff_exists.1 h
    exact ⟨d⟩
  · exact search_complete (ssize Γ) Γ (Nat.le_refl _)

/-- **Derivability without cut is decidable**: by the search. -/
instance decCF (Γ : List Form) : Decidable (Nonempty (CF Γ)) :=
  decidable_of_iff _ (searchCF_isSome_iff Γ)

end MALL

#axioms_within_file [propext, Quot.sound]
