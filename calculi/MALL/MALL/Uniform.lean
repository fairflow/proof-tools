/-
Uniform interpolation for MALL: the interpolant, computed.

For a sequent `Γ` and a letter `p`, `ui p Γ` is a formula without `p`
that is the weakest such formula implying the par of `Γ`: `⊢ (ui p Γ)⊥, Γ`,
and `⊢ ui p Γ, Δ` for every `Δ` without `p` with `⊢ Γ, Δ`.

The definition follows the rules read upwards (Pitts's method, for a
calculus whose search ends by itself, since no rule contracts): the
interpolant of `Γ` is the ⊕ of one formula for each way a derivation of
`⊢ Γ, Δ` can end that concerns `Γ`:

* `Γ` is empty: `⊥`;
* `Γ` is one formula `A` without `p`, against `⊢ A, A⊥`: `A`;
* `Γ` is `A, A⊥`: `𝟏`;
* a rule at a formula of `Γ`: ⊤ gives `⊤`; ⊥ and ⅋ give the interpolant of
  the premise; ⊕ gives that of each premise; & gives the & of the two;
  ⊗ gives, for each division of the rest of `Γ`, the ⊗ of the two;
* a ⊗ of `Δ` whose premises divide `Γ` into two parts, neither empty:
  the ⅋ of the interpolants of the parts.

Every recursive call is at a sequent of smaller size; the recursion is
on a bound of the size.  The formula is simplified as it is built
(`sTensor`, `sPar`, `sWith`, `sBig`).

Theory file: it ends with its bound on axioms.
-/
import MALL.Cut
import MALL.Decide
import MALL.Split

namespace MALL

open List

/-! ## Connectives that simplify -/

/-- `A ⊗ B`, simplified: `𝟎` annihilates, `𝟏` is the unit, and `⊤ ⊗ ⊤` is
`⊤`. -/
def sTensor (A B : Form) : Form :=
  if A = 𝟎 ∨ B = 𝟎 then 𝟎 else if A = 𝟏 then B else if B = 𝟏 then A
  else if A = ⊤ ∧ B = ⊤ then ⊤ else A ⊗ B

/-- `A ⅋ B`, simplified: the dual. -/
def sPar (A B : Form) : Form := (sTensor Aᗮ Bᗮ)ᗮ

/-- A list without its repetitions. -/
def dedup : List Form → List Form
  | [] => []
  | a :: l => if a ∈ l then dedup l else a :: dedup l

/-- The ⊕ of a list of formulas; `𝟎` for none. -/
def plusList : List Form → Form
  | [] => 𝟎
  | [A] => A
  | A :: B :: l => A ⊕ plusList (B :: l)

/-- The ⊕ of a list, simplified: `𝟎` is left out, a formula is taken once,
and `⊤` absorbs. -/
def sBig (ds : List Form) : Form :=
  if ⊤ ∈ dedup (ds.filter fun D => decide (D ≠ 𝟎)) then ⊤
  else plusList (dedup (ds.filter fun D => decide (D ≠ 𝟎)))

/-- `A & B`, simplified: the dual. -/
def sWith (A B : Form) : Form := (sBig [Aᗮ, Bᗮ])ᗮ

/-! ## The interpolant -/

/-- The disjuncts for a sequent that is the conclusion of a rule without
premises, with the other side. -/
def uiBase (p : Nat) : List Form → List Form
  | [] => [⊥]
  | [A] => if p ∈ A.letters then [] else [A]
  | [A, B] => if B = Aᗮ then [𝟏] else []
  | _ => []

/-- The disjuncts for a rule at the formula `X` of the sequent, the rest
being `r`. -/
def uiPick (rec : List Form → Form) : Form → List Form → List Form
  | .top, _ => [⊤]
  | .bot, r => [rec r]
  | .par A B, r => [rec (A :: B :: r)]
  | .wth A B, r => [sWith (rec (A :: r)) (rec (B :: r))]
  | .plus A B, r => [rec (A :: r), rec (B :: r)]
  | .tensor A B, r => (splits r).map fun q => sTensor (rec (A :: q.1)) (rec (B :: q.2))
  | _, _ => []

/-- The divisions of a sequent into two parts, the first formula in the
first part and the second part not empty.  (The other divisions are these
with the parts exchanged.) -/
def properSplits : List Form → List (List Form × List Form)
  | [] => []
  | a :: l => ((splits l).filter fun q => !q.2.isEmpty).map fun q => (a :: q.1, q.2)

/-- The disjuncts of the interpolant of `Γ`, from the interpolants `rec`
of smaller sequents. -/
def uiStep (p : Nat) (rec : List Form → Form) (Γ : List Form) : List Form :=
  uiBase p Γ ++ ((picks Γ).flatMap fun X => uiPick rec X.1 X.2) ++
    (properSplits Γ).map fun q => sPar (rec q.1) (rec q.2)

/-- The interpolant, on a bound of the size of the sequent. -/
def uiN (p : Nat) : Nat → List Form → Form
  | 0, _ => 𝟎
  | n + 1, Γ => sBig (uiStep p (uiN p n) Γ)

/-- **The uniform interpolant** of the sequent `Γ` for the letter `p`. -/
def ui (p : Nat) (Γ : List Form) : Form := uiN p (ssize Γ + 1) Γ

/-- `∀p A`: the weakest formula without `p` that implies `A`. -/
def forallP (p : Nat) (A : Form) : Form := ui p [A]

/-- `∃p A`: the strongest formula without `p` that `A` implies. -/
def existsP (p : Nat) (A : Form) : Form := (ui p [Aᗮ])ᗮ

namespace UI

/-! ## Derivability, with cut -/

theorem exch {Γ Δ : List Form} (h : Γ ~ Δ) : Derivable Γ → Derivable Δ
  | ⟨d⟩ => ⟨d.exch h⟩

theorem cut {A : Form} {Γ Δ : List Form} :
    Derivable (A :: Γ) → Derivable (Aᗮ :: Δ) → Derivable (Γ ++ Δ)
  | ⟨d₁⟩, ⟨d₂⟩ => ⟨.cut A Γ Δ (.refl _) d₁ d₂⟩

theorem top (Γ : List Form) : Derivable (⊤ :: Γ) := ⟨.top Γ (.refl _)⟩

/-- From `⊢ 𝟎, Γ`, anything beside `Γ`. -/
theorem zero_any {Γ : List Form} (h : Derivable (𝟎 :: Γ)) (Θ : List Form) : Derivable (Γ ++ Θ) :=
  cut (A := 𝟎) h (top Θ)

/-- `𝟏` is the unit: from `⊢ 𝟏, Γ` and `⊢ Δ`. -/
theorem one_cut {Γ Δ : List Form} (h₁ : Derivable (𝟏 :: Γ)) (h₂ : Derivable Δ) :
    Derivable (Γ ++ Δ) :=
  cut (A := 𝟏) h₁ (let ⟨d⟩ := h₂; ⟨.bot Δ (.refl _) d⟩)

theorem bot_inv {Γ : List Form} (h : Derivable (⊥ :: Γ)) : Derivable Γ := by
  have := cut (A := ⊥) (Δ := []) h ⟨.one (.refl _)⟩
  rwa [List.append_nil] at this

/-! ## The simplifying connectives are the connectives -/

theorem sTensor_intro {A B : Form} {Γ Δ : List Form} (h₁ : Derivable (A :: Γ))
    (h₂ : Derivable (B :: Δ)) : Derivable (sTensor A B :: (Γ ++ Δ)) := by
  unfold sTensor
  split
  next h =>
    rcases h with rfl | rfl
    · exact exch (by perm_count []) (zero_any h₁ (𝟎 :: Δ))
    · exact exch (by perm_count []) (zero_any h₂ (𝟎 :: Γ))
  next _ =>
    split
    next h => subst h; exact exch (by perm_count []) (one_cut h₁ h₂)
    next _ =>
      split
      next h => subst h; exact exch (by perm_count []) (one_cut h₂ h₁)
      next _ =>
        split
        next _ => exact top _
        next _ =>
          obtain ⟨d₁⟩ := h₁
          obtain ⟨d₂⟩ := h₂
          exact ⟨.tensor A B Γ Δ (.refl _) d₁ d₂⟩

theorem sTensor_dual {A B : Form} {Γ : List Form} (h : Derivable (Aᗮ :: Bᗮ :: Γ)) :
    Derivable ((sTensor A B)ᗮ :: Γ) := by
  unfold sTensor
  split
  next _ => exact top Γ
  next _ =>
    split
    next h' => subst h'; exact bot_inv h
    next _ =>
      split
      next h' => subst h'; exact bot_inv (exch (.swap ..) h)
      next _ =>
        split
        next h' =>
          obtain ⟨rfl, rfl⟩ := h'
          have := zero_any h ([] : List Form)
          rwa [List.append_nil] at this
        next _ =>
          obtain ⟨d⟩ := h
          exact ⟨.par Aᗮ Bᗮ Γ (.refl _) d⟩

theorem sPar_intro {A B : Form} {Δ : List Form} (h : Derivable (A :: B :: Δ)) :
    Derivable (sPar A B :: Δ) :=
  sTensor_dual (A := Aᗮ) (B := Bᗮ) (by rw [Form.neg_neg, Form.neg_neg]; exact h)

theorem sPar_dual {A B : Form} {Γ Δ : List Form} (h₁ : Derivable (Aᗮ :: Γ))
    (h₂ : Derivable (Bᗮ :: Δ)) : Derivable ((sPar A B)ᗮ :: (Γ ++ Δ)) := by
  unfold sPar
  rw [Form.neg_neg]
  exact sTensor_intro h₁ h₂

theorem mem_dedup {a : Form} : ∀ {l : List Form}, a ∈ dedup l ↔ a ∈ l
  | [] => Iff.rfl
  | b :: l => by
    unfold dedup
    split
    next h =>
      rw [mem_dedup, mem_cons]
      exact ⟨.inr, fun h' => h'.elim (fun e => e ▸ h) id⟩
    next _ => rw [mem_cons, mem_cons, mem_dedup]

theorem plusList_inj {D : Form} {Δ : List Form} :
    ∀ l : List Form, D ∈ l → Derivable (D :: Δ) → Derivable (plusList l :: Δ)
  | [], h, _ => by cases h
  | [A], h, hd => by
    rcases mem_cons.1 h with rfl | h
    · exact hd
    · cases h
  | A :: B :: l, h, hd => by
    rcases mem_cons.1 h with rfl | h
    · obtain ⟨d⟩ := hd
      exact ⟨.plus₁ D (plusList (B :: l)) Δ (.refl _) d⟩
    · obtain ⟨d⟩ := plusList_inj (B :: l) h hd
      exact ⟨.plus₂ A (plusList (B :: l)) Δ (.refl _) d⟩

theorem plusList_dual {Γ : List Form} :
    ∀ l : List Form, (∀ D ∈ l, Derivable (Dᗮ :: Γ)) → Derivable ((plusList l)ᗮ :: Γ)
  | [], _ => top Γ
  | [A], h => h A (mem_cons_self ..)
  | A :: B :: l, h => by
    obtain ⟨d₁⟩ := h A (mem_cons_self ..)
    obtain ⟨d₂⟩ := plusList_dual (B :: l) fun D hD => h D (mem_cons_of_mem _ hD)
    exact ⟨.wth Aᗮ (plusList (B :: l))ᗮ Γ (.refl _) d₁ d₂⟩

theorem sBig_inj {D : Form} {ds Δ : List Form} (hD : D ∈ ds) (h : Derivable (D :: Δ)) :
    Derivable (sBig ds :: Δ) := by
  by_cases h0 : D = 𝟎
  · subst h0
    exact exch (by perm_count []) (zero_any h [sBig ds])
  · have hm : D ∈ dedup (ds.filter fun D => decide (D ≠ 𝟎)) :=
      mem_dedup.2 (mem_filter.2 ⟨hD, decide_eq_true h0⟩)
    unfold sBig
    split
    next _ => exact top Δ
    next _ => exact plusList_inj _ hm h

theorem sBig_dual {ds Γ : List Form} (h : ∀ D ∈ ds, Derivable (Dᗮ :: Γ)) :
    Derivable ((sBig ds)ᗮ :: Γ) := by
  unfold sBig
  split
  next ht => exact h ⊤ (mem_filter.1 (mem_dedup.1 ht)).1
  next _ => exact plusList_dual _ fun D hD => h D (mem_filter.1 (mem_dedup.1 hD)).1

theorem sWith_intro {A B : Form} {Δ : List Form} (h₁ : Derivable (A :: Δ))
    (h₂ : Derivable (B :: Δ)) : Derivable (sWith A B :: Δ) :=
  sBig_dual (ds := [Aᗮ, Bᗮ]) fun D hD => by
    rcases mem_cons.1 hD with rfl | hD
    · rw [Form.neg_neg]; exact h₁
    · rcases mem_cons.1 hD with rfl | hD
      · rw [Form.neg_neg]; exact h₂
      · cases hD

theorem sWith_dual₁ {A B : Form} {Γ : List Form} (h : Derivable (Aᗮ :: Γ)) :
    Derivable ((sWith A B)ᗮ :: Γ) := by
  unfold sWith
  rw [Form.neg_neg]
  exact sBig_inj (mem_cons_self ..) h

theorem sWith_dual₂ {A B : Form} {Γ : List Form} (h : Derivable (Bᗮ :: Γ)) :
    Derivable ((sWith A B)ᗮ :: Γ) := by
  unfold sWith
  rw [Form.neg_neg]
  exact sBig_inj (mem_cons_of_mem _ (mem_cons_self ..)) h

/-! ## Their letters -/

theorem letters_sTensor {A B : Form} {a : Nat} (h : a ∈ (sTensor A B).letters) :
    a ∈ A.letters ∨ a ∈ B.letters := by
  unfold sTensor at h
  split at h
  · cases h
  · split at h
    · exact .inr h
    · split at h
      · exact .inl h
      · split at h
        · cases h
        · exact mem_append.1 h

theorem letters_sPar {A B : Form} {a : Nat} (h : a ∈ (sPar A B).letters) :
    a ∈ A.letters ∨ a ∈ B.letters := by
  unfold sPar at h
  rw [Form.letters_neg] at h
  have := letters_sTensor h
  rwa [Form.letters_neg, Form.letters_neg] at this

theorem letters_plusList {a : Nat} :
    ∀ l : List Form, a ∈ (plusList l).letters → ∃ D, D ∈ l ∧ a ∈ D.letters
  | [], h => by cases h
  | [A], h => ⟨A, mem_cons_self .., h⟩
  | A :: B :: l, h => by
    rcases mem_append.1 (show a ∈ A.letters ++ (plusList (B :: l)).letters from h) with h | h
    · exact ⟨A, mem_cons_self .., h⟩
    · obtain ⟨D, hD, hDa⟩ := letters_plusList (B :: l) h
      exact ⟨D, mem_cons_of_mem _ hD, hDa⟩

theorem letters_sBig {ds : List Form} {a : Nat} (h : a ∈ (sBig ds).letters) :
    ∃ D, D ∈ ds ∧ a ∈ D.letters := by
  unfold sBig at h
  split at h
  · cases h
  · obtain ⟨D, hD, hDa⟩ := letters_plusList _ h
    exact ⟨D, (mem_filter.1 (mem_dedup.1 hD)).1, hDa⟩

theorem letters_sWith {A B : Form} {a : Nat} (h : a ∈ (sWith A B).letters) :
    a ∈ A.letters ∨ a ∈ B.letters := by
  unfold sWith at h
  rw [Form.letters_neg] at h
  obtain ⟨D, hD, hDa⟩ := letters_sBig h
  rcases mem_cons.1 hD with rfl | hD
  · rw [Form.letters_neg] at hDa; exact .inl hDa
  · rcases mem_cons.1 hD with rfl | hD
    · rw [Form.letters_neg] at hDa; exact .inr hDa
    · cases hD

theorem mem_lettersL {a : Nat} {Γ : List Form} : a ∈ lettersL Γ ↔ ∃ A, A ∈ Γ ∧ a ∈ A.letters := by
  unfold lettersL
  exact mem_flatMap

/-! ## The divisions -/

theorem properSplits_spec {Γ : List Form} {q : List Form × List Form}
    (h : q ∈ properSplits Γ) : Γ ~ q.1 ++ q.2 ∧ q.1 ≠ [] ∧ q.2 ≠ [] := by
  cases Γ with
  | nil => cases h
  | cons a l =>
    obtain ⟨q', hq', rfl⟩ := mem_map.1 h
    obtain ⟨hs, hne⟩ := mem_filter.1 hq'
    refine ⟨(splits_perm hs).cons a, List.cons_ne_nil _ _, fun e => ?_⟩
    have e' : q'.2 = [] := e
    rw [e'] at hne
    cases hne

theorem properSplits_complete {Γ G₁ G₂ : List Form} (h : Γ ~ G₁ ++ G₂) (h₁ : G₁ ≠ [])
    (h₂ : G₂ ≠ []) :
    ∃ q, q ∈ properSplits Γ ∧ ((q.1 ~ G₁ ∧ q.2 ~ G₂) ∨ (q.1 ~ G₂ ∧ q.2 ~ G₁)) := by
  have ne : ∀ {l G : List Form}, l ~ G → G ≠ [] → (!l.isEmpty) = true := by
    intro l G hp hG
    cases l with
    | nil => exact absurd (perm_nil_eq hp.symm) hG
    | cons _ _ => rfl
  cases Γ with
  | nil =>
    have := perm_nil_eq h.symm
    cases G₁ with
    | nil => exact absurd rfl h₁
    | cons _ _ => cases this
  | cons a l =>
    have ha : a ∈ G₁ ++ G₂ := h.mem_iff.1 (mem_cons_self ..)
    by_cases ha₁ : a ∈ G₁
    · have hp := perm_cons_erase ha₁
      have h' : l ~ G₁.erase a ++ G₂ := by perm_count [h, hp]
      obtain ⟨q, hq, p₁, p₂⟩ := splits_complete h'
      refine ⟨(a :: q.1, q.2), mem_map.2 ⟨q, mem_filter.2 ⟨hq, ne p₂ h₂⟩, rfl⟩, .inl ⟨?_, p₂⟩⟩
      show a :: q.1 ~ G₁
      perm_count [p₁, hp]
    · have ha₂ : a ∈ G₂ := (mem_append.1 ha).resolve_left ha₁
      have hp := perm_cons_erase ha₂
      have h' : l ~ G₂.erase a ++ G₁ := by perm_count [h, hp]
      obtain ⟨q, hq, p₁, p₂⟩ := splits_complete h'
      refine ⟨(a :: q.1, q.2), mem_map.2 ⟨q, mem_filter.2 ⟨hq, ne p₂ h₁⟩, rfl⟩, .inr ⟨?_, p₂⟩⟩
      show a :: q.1 ~ G₂
      perm_count [p₁, hp]

/-- Where the principal formula of a rule is, in a sequent divided in two:
in the first part, picked with the rest; or in the second. -/
theorem locate {X : Form} {Θ Γ Δ : List Form} (e : X :: Θ ~ Γ ++ Δ) :
    (∃ r, (X, r) ∈ picks Γ ∧ Θ ~ r ++ Δ) ∨ (∃ Δ', Δ ~ X :: Δ' ∧ Θ ~ Γ ++ Δ') := by
  by_cases hX : X ∈ Γ
  · obtain ⟨r, hr⟩ := picks_mem hX
    have hp : Γ ~ X :: r := picks_perm hr
    exact .inl ⟨r, hr, by perm_count [e, hp]⟩
  · have : X ∈ Γ ++ Δ := e.mem_iff.1 (mem_cons_self ..)
    have hX' : X ∈ Δ := (mem_append.1 this).resolve_left hX
    have hp := perm_cons_erase hX'
    exact .inr ⟨Δ.erase X, hp, by perm_count [e, hp]⟩

theorem ssize_pick {Γ : List Form} {X : Form} {r : List Form} (h : Γ ~ X :: r) :
    ssize Γ = X.size + ssize r := by
  rw [ssize_perm h]; rfl

theorem mem_step_base {p : Nat} {rec : List Form → Form} {Γ : List Form} {D : Form}
    (h : D ∈ uiBase p Γ) : D ∈ uiStep p rec Γ :=
  mem_append.2 (.inl (mem_append.2 (.inl h)))

theorem mem_step_pick {p : Nat} {rec : List Form → Form} {Γ : List Form} {X : Form}
    {r : List Form} {D : Form} (hp : (X, r) ∈ picks Γ) (h : D ∈ uiPick rec X r) :
    D ∈ uiStep p rec Γ :=
  mem_append.2 (.inl (mem_append.2 (.inr (mem_flatMap.2 ⟨(X, r), hp, h⟩))))

theorem mem_step_split {p : Nat} {rec : List Form → Form} {Γ : List Form}
    {q : List Form × List Form} (h : q ∈ properSplits Γ) :
    sPar (rec q.1) (rec q.2) ∈ uiStep p rec Γ :=
  mem_append.2 (.inr (mem_map.2 ⟨q, h, rfl⟩))

theorem mem_uiBase {p : Nat} {Γ : List Form} {D : Form} (h : D ∈ uiBase p Γ) :
    (Γ = [] ∧ D = ⊥) ∨ (Γ = [D] ∧ p ∉ D.letters) ∨ ∃ A, Γ = [A, Aᗮ] ∧ D = 𝟏 := by
  cases Γ with
  | nil =>
    rcases mem_cons.1 (show D ∈ [⊥] from h) with rfl | h
    · exact .inl ⟨rfl, rfl⟩
    · cases h
  | cons A l =>
    cases l with
    | nil =>
      have h' : D ∈ (if p ∈ A.letters then [] else [A]) := h
      by_cases hp : p ∈ A.letters
      · rw [if_pos hp] at h'; cases h'
      · rw [if_neg hp] at h'
        rcases mem_cons.1 h' with rfl | h'
        · exact .inr (.inl ⟨rfl, hp⟩)
        · cases h'
    | cons B l =>
      cases l with
      | nil =>
        have h' : D ∈ (if B = Aᗮ then [𝟏] else []) := h
        by_cases hB : B = Aᗮ
        · rw [if_pos hB] at h'
          subst hB
          rcases mem_cons.1 h' with rfl | h'
          · exact .inr (.inr ⟨A, rfl, rfl⟩)
          · cases h'
        · rw [if_neg hB] at h'; cases h'
      | cons _ _ => cases h

theorem uiBase_single {p : Nat} {X : Form} (hp : p ∉ X.letters) : X ∈ uiBase p [X] := by
  show X ∈ (if p ∈ X.letters then [] else [X])
  rw [if_neg hp]; exact mem_cons_self ..

theorem uiBase_axiom (p : Nat) (A : Form) : 𝟏 ∈ uiBase p [A, Aᗮ] := by
  show 𝟏 ∈ (if Aᗮ = Aᗮ then [𝟏] else [])
  rw [if_pos rfl]; exact mem_cons_self ..

/-- The cases of a disjunct of the interpolant. -/
theorem mem_step {p : Nat} {rec : List Form → Form} {Γ : List Form} {D : Form}
    (h : D ∈ uiStep p rec Γ) :
    D ∈ uiBase p Γ ∨ (∃ X r, (X, r) ∈ picks Γ ∧ D ∈ uiPick rec X r) ∨
      ∃ q, q ∈ properSplits Γ ∧ D = sPar (rec q.1) (rec q.2) := by
  rcases mem_append.1 h with h | h
  · rcases mem_append.1 h with h | h
    · exact .inl h
    · obtain ⟨X, hX, hD⟩ := mem_flatMap.1 h
      exact .inr (.inl ⟨X.1, X.2, hX, hD⟩)
  · obtain ⟨q, hq, e⟩ := mem_map.1 h
    exact .inr (.inr ⟨q, hq, e.symm⟩)

end UI

open UI

/-! ## The interpolant implies the sequent -/

/-- **`⊢ (ui p Γ)⊥, Γ`**, at every bound. -/
theorem uiN_below (p : Nat) : ∀ (n : Nat) (Γ : List Form), Derivable ((uiN p n Γ)ᗮ :: Γ)
  | 0, Γ => UI.top Γ
  | n + 1, Γ => by
    refine sBig_dual fun D hD => ?_
    rcases mem_step hD with hD | ⟨X, r, hr, hD⟩ | ⟨q, hq, rfl⟩
    · -- a rule without premises
      rcases mem_uiBase hD with ⟨rfl, rfl⟩ | ⟨rfl, _⟩ | ⟨A, rfl, rfl⟩
      · exact ⟨.one (.refl _)⟩
      · exact ⟨.ax D (.swap ..)⟩
      · exact ⟨.bot [A, Aᗮ] (.refl _) (.ax A (.refl _))⟩
    · -- a rule at a formula of Γ
      have hp : Γ ~ X :: r := picks_perm hr
      cases X with
      | atom _ | natom _ | one | zero => cases hD
      | top =>
        rcases mem_cons.1 hD with rfl | hD
        · exact ⟨.top (𝟎 :: r) (by show 𝟎 :: Γ ~ _; perm_count [hp])⟩
        · cases hD
      | bot =>
        rcases mem_cons.1 hD with rfl | hD
        · obtain ⟨d⟩ := uiN_below p n r
          exact ⟨.bot ((uiN p n r)ᗮ :: r) (by perm_count [hp]) d⟩
        · cases hD
      | par A B =>
        rcases mem_cons.1 hD with rfl | hD
        · obtain ⟨d⟩ := uiN_below p n (A :: B :: r)
          exact ⟨.par A B ((uiN p n (A :: B :: r))ᗮ :: r) (by perm_count [hp])
            (d.exch (by perm_count []))⟩
        · cases hD
      | wth A B =>
        rcases mem_cons.1 hD with rfl | hD
        · obtain ⟨d₁⟩ := sWith_dual₁ (B := uiN p n (B :: r)) (uiN_below p n (A :: r))
          obtain ⟨d₂⟩ := sWith_dual₂ (A := uiN p n (A :: r)) (uiN_below p n (B :: r))
          exact ⟨.wth A B (_ :: r) (by perm_count [hp]) (d₁.exch (.swap ..)) (d₂.exch (.swap ..))⟩
        · cases hD
      | plus A B =>
        rcases mem_cons.1 hD with rfl | hD
        · obtain ⟨d⟩ := uiN_below p n (A :: r)
          exact ⟨.plus₁ A B (_ :: r) (by perm_count [hp]) (d.exch (.swap ..))⟩
        · rcases mem_cons.1 hD with rfl | hD
          · obtain ⟨d⟩ := uiN_below p n (B :: r)
            exact ⟨.plus₂ A B (_ :: r) (by perm_count [hp]) (d.exch (.swap ..))⟩
          · cases hD
      | tensor A B =>
        obtain ⟨q, hq, rfl⟩ := mem_map.1 hD
        have pq : r ~ q.1 ++ q.2 := splits_perm hq
        obtain ⟨d₁⟩ := uiN_below p n (A :: q.1)
        obtain ⟨d₂⟩ := uiN_below p n (B :: q.2)
        refine sTensor_dual ⟨.tensor A B (_ :: q.1) (_ :: q.2) ?_ (d₁.exch (.swap ..))
          (d₂.exch (.swap ..))⟩
        perm_count [hp, pq]
    · -- a division of Γ
      obtain ⟨pq, _, _⟩ := properSplits_spec hq
      exact exch (by perm_count [pq]) (sPar_dual (uiN_below p n q.1) (uiN_below p n q.2))

/-! ## Its letters -/

/-- The letters of the interpolant are letters of the sequent other than
`p`. -/
theorem uiN_letters (p : Nat) : ∀ (n : Nat) (Γ : List Form) (a : Nat),
    a ∈ (uiN p n Γ).letters → a ≠ p ∧ ∃ C, C ∈ Γ ∧ a ∈ C.letters
  | 0, _, _, h => by cases h
  | n + 1, Γ, a, h => by
    obtain ⟨D, hD, ha⟩ := letters_sBig h
    rcases mem_step hD with hD | ⟨X, r, hr, hD⟩ | ⟨q, hq, rfl⟩
    · rcases mem_uiBase hD with ⟨rfl, rfl⟩ | ⟨rfl, hp⟩ | ⟨A, rfl, rfl⟩
      · cases ha
      · exact ⟨fun e => hp (e ▸ ha), D, mem_cons_self .., ha⟩
      · cases ha
    · have hp : Γ ~ X :: r := picks_perm hr
      have hX : X ∈ Γ := hp.mem_iff.2 (mem_cons_self ..)
      have hr' : ∀ C, C ∈ r → C ∈ Γ := fun C hC => hp.mem_iff.2 (mem_cons_of_mem _ hC)
      -- from a premise's interpolant to the conclusion
      have lift : ∀ (Γ' : List Form), (∀ C, C ∈ Γ' → C ∈ Γ ∨ ∀ b, b ∈ C.letters → b ∈ X.letters) →
          a ∈ (uiN p n Γ').letters → a ≠ p ∧ ∃ C, C ∈ Γ ∧ a ∈ C.letters := by
        intro Γ' hsub h'
        obtain ⟨hne, C, hC, haC⟩ := uiN_letters p n Γ' a h'
        rcases hsub C hC with hC | hC
        · exact ⟨hne, C, hC, haC⟩
        · exact ⟨hne, X, hX, hC a haC⟩
      cases X with
      | atom _ | natom _ | one | zero => cases hD
      | top =>
        rcases mem_cons.1 hD with rfl | hD
        · cases ha
        · cases hD
      | bot =>
        rcases mem_cons.1 hD with rfl | hD
        · exact lift r (fun C hC => .inl (hr' C hC)) ha
        · cases hD
      | par A B =>
        rcases mem_cons.1 hD with rfl | hD
        · refine lift (A :: B :: r) (fun C hC => ?_) ha
          rcases mem_cons.1 hC with rfl | hC
          · exact .inr fun b hb => mem_append.2 (.inl hb)
          · rcases mem_cons.1 hC with rfl | hC
            · exact .inr fun b hb => mem_append.2 (.inr hb)
            · exact .inl (hr' C hC)
        · cases hD
      | wth A B =>
        rcases mem_cons.1 hD with rfl | hD
        · rcases letters_sWith ha with ha | ha
          · refine lift (A :: r) (fun C hC => ?_) ha
            rcases mem_cons.1 hC with rfl | hC
            · exact .inr fun b hb => mem_append.2 (.inl hb)
            · exact .inl (hr' C hC)
          · refine lift (B :: r) (fun C hC => ?_) ha
            rcases mem_cons.1 hC with rfl | hC
            · exact .inr fun b hb => mem_append.2 (.inr hb)
            · exact .inl (hr' C hC)
        · cases hD
      | plus A B =>
        rcases mem_cons.1 hD with rfl | hD
        · refine lift (A :: r) (fun C hC => ?_) ha
          rcases mem_cons.1 hC with rfl | hC
          · exact .inr fun b hb => mem_append.2 (.inl hb)
          · exact .inl (hr' C hC)
        · rcases mem_cons.1 hD with rfl | hD
          · refine lift (B :: r) (fun C hC => ?_) ha
            rcases mem_cons.1 hC with rfl | hC
            · exact .inr fun b hb => mem_append.2 (.inr hb)
            · exact .inl (hr' C hC)
          · cases hD
      | tensor A B =>
        obtain ⟨q, hq, rfl⟩ := mem_map.1 hD
        have pq : r ~ q.1 ++ q.2 := splits_perm hq
        rcases letters_sTensor ha with ha | ha
        · refine lift (A :: q.1) (fun C hC => ?_) ha
          rcases mem_cons.1 hC with rfl | hC
          · exact .inr fun b hb => mem_append.2 (.inl hb)
          · exact .inl (hr' C (pq.mem_iff.2 (mem_append.2 (.inl hC))))
        · refine lift (B :: q.2) (fun C hC => ?_) ha
          rcases mem_cons.1 hC with rfl | hC
          · exact .inr fun b hb => mem_append.2 (.inr hb)
          · exact .inl (hr' C (pq.mem_iff.2 (mem_append.2 (.inr hC))))
    · obtain ⟨pq, _, _⟩ := properSplits_spec hq
      rcases letters_sPar ha with ha | ha
      · obtain ⟨hne, C, hC, haC⟩ := uiN_letters p n q.1 a ha
        exact ⟨hne, C, pq.mem_iff.2 (mem_append.2 (.inl hC)), haC⟩
      · obtain ⟨hne, C, hC, haC⟩ := uiN_letters p n q.2 a ha
        exact ⟨hne, C, pq.mem_iff.2 (mem_append.2 (.inr hC)), haC⟩

/-! ## The interpolant is the weakest -/

/-- No formula of the sequent has the letter. -/
def FreeL (p : Nat) (Δ : List Form) : Prop := ∀ C, C ∈ Δ → p ∉ C.letters

theorem FreeL.sub {p : Nat} {Δ Δ' : List Form} (h : FreeL p Δ) (hs : ∀ C, C ∈ Δ' → C ∈ Δ) :
    FreeL p Δ' := fun C hC => h C (hs C hC)

/-- **`⊢ ui p Γ, Δ` for every `Δ` without `p` with `⊢ Γ, Δ`**: by induction
on a derivation without cut, for every division of its sequent and every
bound above the size of the first part. -/
theorem uiN_greatest (p : Nat) : ∀ {Ξ : List Form}, CF Ξ → ∀ (n : Nat) (Γ Δ : List Form),
    Ξ ~ Γ ++ Δ → FreeL p Δ → ssize Γ < n → Derivable (uiN p n Γ :: Δ) := by
  intro Ξ d
  induction d with
  | ax A h =>
    intro n Γ Δ e hΔ hn
    obtain _ | n := n
    · exact absurd hn (Nat.not_lt_zero _)
    have e' : [A, Aᗮ] ~ Γ ++ Δ := h.symm.trans e
    have hl := e'.length_eq
    match Γ, Δ, e', hl, hΔ with
    | [], Δ, e', _, _ =>
      exact sBig_inj (mem_step_base (mem_cons_self ..)) ⟨.bot Δ (.refl _) (.ax A e'.symm)⟩
    | [X], [Y], e', _, hΔ =>
      have hXY : Y = Xᗮ := by
        rcases perm_pair (show [A, Aᗮ] ~ [X, Y] from e') with e₁ | e₁
        · cases e₁; rfl
        · cases e₁; exact (Form.neg_neg _).symm
      subst hXY
      have hp : p ∉ X.letters := fun hp =>
        hΔ Xᗮ (mem_cons_self ..) (by rw [Form.letters_neg]; exact hp)
      exact sBig_inj (mem_step_base (uiBase_single hp)) ⟨.ax X (.refl _)⟩
    | [X, Y], [], e', _, _ =>
      have hXY : Y = Xᗮ := by
        rcases perm_pair (show [A, Aᗮ] ~ [X, Y] from e') with e₁ | e₁
        · cases e₁; rfl
        · cases e₁; exact (Form.neg_neg _).symm
      subst hXY
      exact sBig_inj (mem_step_base (uiBase_axiom p X)) ⟨.one (.refl _)⟩
    | [_], [], _, hl, _ => cases hl
    | [_], _ :: _ :: _, _, hl, _ =>
      exfalso; simp only [List.length_cons, List.length_append, List.length_nil] at hl; omega
    | [_, _], _ :: _, _, hl, _ =>
      exfalso; simp only [List.length_cons, List.length_append, List.length_nil] at hl; omega
    | _ :: _ :: _ :: _, _, _, hl, _ =>
      exfalso; simp only [List.length_cons, List.length_append, List.length_nil] at hl; omega
  | one h =>
    intro n Γ Δ e hΔ hn
    obtain _ | n := n
    · exact absurd hn (Nat.not_lt_zero _)
    have e' : [𝟏] ~ Γ ++ Δ := h.symm.trans e
    have hl := e'.length_eq
    match Γ, Δ, e', hl with
    | [], Δ, e', _ =>
      exact sBig_inj (mem_step_base (mem_cons_self ..)) ⟨.bot Δ (.refl _) (.one e'.symm)⟩
    | [X], [], e', _ =>
      have hX : [𝟏] = [X] := perm_singleton_eq e'
      cases hX
      exact sBig_inj (mem_step_base (uiBase_single (p := p) (X := 𝟏) (fun h => by cases h)))
        ⟨.one (.refl _)⟩
    | [_], _ :: _, _, hl =>
      exfalso; simp only [List.length_cons, List.length_append, List.length_nil] at hl; omega
    | _ :: _ :: _, _, _, hl =>
      exfalso; simp only [List.length_cons, List.length_append, List.length_nil] at hl; omega
  | top Θ h =>
    intro n Γ Δ e hΔ hn
    rcases locate (h.symm.trans e) with ⟨r, hr, _⟩ | ⟨Δ', hΔ', _⟩
    · obtain _ | n := n
      · exact absurd hn (Nat.not_lt_zero _)
      exact sBig_inj (mem_step_pick hr (show ⊤ ∈ uiPick _ ⊤ r from mem_cons_self ..)) (UI.top Δ)
    · exact ⟨.top (uiN p n Γ :: Δ') (by perm_count [hΔ'])⟩
  | bot Θ h d ih =>
    intro n Γ Δ e hΔ hn
    rcases locate (h.symm.trans e) with ⟨r, hr, hΘ⟩ | ⟨Δ', hΔ', hΘ⟩
    · obtain _ | n := n
      · exact absurd hn (Nat.not_lt_zero _)
      have hsz := ssize_pick (picks_perm hr)
      have i := ih n r Δ hΘ hΔ (by simp only [Form.size] at hsz; omega)
      exact sBig_inj (mem_step_pick hr (show uiN p n r ∈ uiPick _ ⊥ r from mem_cons_self ..)) i
    · obtain ⟨c⟩ := ih n Γ Δ' hΘ
        (hΔ.sub fun C hC => hΔ'.mem_iff.2 (mem_cons_of_mem _ hC)) hn
      exact ⟨.bot (uiN p n Γ :: Δ') (by perm_count [hΔ']) c⟩
  | par A B Θ h d ih =>
    intro n Γ Δ e hΔ hn
    rcases locate (h.symm.trans e) with ⟨r, hr, hΘ⟩ | ⟨Δ', hΔ', hΘ⟩
    · obtain _ | n := n
      · exact absurd hn (Nat.not_lt_zero _)
      have hsz := ssize_pick (picks_perm hr)
      have i := ih n (A :: B :: r) Δ (by perm_count [hΘ]) hΔ
        (by simp only [Form.size] at hsz; simp only [ssize]; omega)
      exact sBig_inj (mem_step_pick hr
        (show uiN p n (A :: B :: r) ∈ uiPick _ (A ⅋ B) r from mem_cons_self ..)) i
    · have hX : A ⅋ B ∈ Δ := hΔ'.mem_iff.2 (mem_cons_self ..)
      have hfree : FreeL p (A :: B :: Δ') := fun C hC => by
        rcases mem_cons.1 hC with rfl | hC
        · exact fun hp => hΔ _ hX (mem_append.2 (.inl hp))
        · rcases mem_cons.1 hC with rfl | hC
          · exact fun hp => hΔ _ hX (mem_append.2 (.inr hp))
          · exact hΔ C (hΔ'.mem_iff.2 (mem_cons_of_mem _ hC))
      obtain ⟨c⟩ := ih n Γ (A :: B :: Δ') (by perm_count [hΘ]) hfree hn
      exact ⟨.par A B (uiN p n Γ :: Δ') (by perm_count [hΔ']) (c.exch (by perm_count []))⟩
  | plus₁ A B Θ h d ih =>
    intro n Γ Δ e hΔ hn
    rcases locate (h.symm.trans e) with ⟨r, hr, hΘ⟩ | ⟨Δ', hΔ', hΘ⟩
    · obtain _ | n := n
      · exact absurd hn (Nat.not_lt_zero _)
      have hsz := ssize_pick (picks_perm hr)
      have i := ih n (A :: r) Δ (by perm_count [hΘ]) hΔ
        (by simp only [Form.size] at hsz; simp only [ssize]; omega)
      exact sBig_inj (mem_step_pick hr
        (show uiN p n (A :: r) ∈ uiPick _ (.plus A B) r from mem_cons_self ..)) i
    · have hX : (A ⊕ B) ∈ Δ := hΔ'.mem_iff.2 (mem_cons_self ..)
      have hfree : FreeL p (A :: Δ') := fun C hC => by
        rcases mem_cons.1 hC with rfl | hC
        · exact fun hp => hΔ _ hX (mem_append.2 (.inl hp))
        · exact hΔ C (hΔ'.mem_iff.2 (mem_cons_of_mem _ hC))
      obtain ⟨c⟩ := ih n Γ (A :: Δ') (by perm_count [hΘ]) hfree hn
      exact ⟨.plus₁ A B (uiN p n Γ :: Δ') (by perm_count [hΔ']) (c.exch (.swap ..))⟩
  | plus₂ A B Θ h d ih =>
    intro n Γ Δ e hΔ hn
    rcases locate (h.symm.trans e) with ⟨r, hr, hΘ⟩ | ⟨Δ', hΔ', hΘ⟩
    · obtain _ | n := n
      · exact absurd hn (Nat.not_lt_zero _)
      have hsz := ssize_pick (picks_perm hr)
      have i := ih n (B :: r) Δ (by perm_count [hΘ]) hΔ
        (by simp only [Form.size] at hsz; simp only [ssize]; omega)
      exact sBig_inj (mem_step_pick hr
        (show uiN p n (B :: r) ∈ uiPick _ (.plus A B) r from
          mem_cons_of_mem _ (mem_cons_self ..))) i
    · have hX : (A ⊕ B) ∈ Δ := hΔ'.mem_iff.2 (mem_cons_self ..)
      have hfree : FreeL p (B :: Δ') := fun C hC => by
        rcases mem_cons.1 hC with rfl | hC
        · exact fun hp => hΔ _ hX (mem_append.2 (.inr hp))
        · exact hΔ C (hΔ'.mem_iff.2 (mem_cons_of_mem _ hC))
      obtain ⟨c⟩ := ih n Γ (B :: Δ') (by perm_count [hΘ]) hfree hn
      exact ⟨.plus₂ A B (uiN p n Γ :: Δ') (by perm_count [hΔ']) (c.exch (.swap ..))⟩
  | wth A B Θ h d₁ d₂ ih₁ ih₂ =>
    intro n Γ Δ e hΔ hn
    rcases locate (h.symm.trans e) with ⟨r, hr, hΘ⟩ | ⟨Δ', hΔ', hΘ⟩
    · obtain _ | n := n
      · exact absurd hn (Nat.not_lt_zero _)
      have hsz := ssize_pick (picks_perm hr)
      have i₁ := ih₁ n (A :: r) Δ (by perm_count [hΘ]) hΔ
        (by simp only [Form.size] at hsz; simp only [ssize]; omega)
      have i₂ := ih₂ n (B :: r) Δ (by perm_count [hΘ]) hΔ
        (by simp only [Form.size] at hsz; simp only [ssize]; omega)
      exact sBig_inj (mem_step_pick hr
        (show sWith (uiN p n (A :: r)) (uiN p n (B :: r)) ∈ uiPick _ (A & B) r from
          mem_cons_self ..)) (sWith_intro i₁ i₂)
    · have hX : A & B ∈ Δ := hΔ'.mem_iff.2 (mem_cons_self ..)
      have hfree₁ : FreeL p (A :: Δ') := fun C hC => by
        rcases mem_cons.1 hC with rfl | hC
        · exact fun hp => hΔ _ hX (mem_append.2 (.inl hp))
        · exact hΔ C (hΔ'.mem_iff.2 (mem_cons_of_mem _ hC))
      have hfree₂ : FreeL p (B :: Δ') := fun C hC => by
        rcases mem_cons.1 hC with rfl | hC
        · exact fun hp => hΔ _ hX (mem_append.2 (.inr hp))
        · exact hΔ C (hΔ'.mem_iff.2 (mem_cons_of_mem _ hC))
      obtain ⟨c₁⟩ := ih₁ n Γ (A :: Δ') (by perm_count [hΘ]) hfree₁ hn
      obtain ⟨c₂⟩ := ih₂ n Γ (B :: Δ') (by perm_count [hΘ]) hfree₂ hn
      exact ⟨.wth A B (uiN p n Γ :: Δ') (by perm_count [hΔ']) (c₁.exch (.swap ..))
        (c₂.exch (.swap ..))⟩
  | tensor A B Θ₁ Θ₂ h d₁ d₂ ih₁ ih₂ =>
    intro n Γ Δ e hΔ hn
    rcases locate (h.symm.trans e) with ⟨r, hr, hΘ⟩ | ⟨Δ', hΔ', hΘ⟩
    · -- the ⊗ is in Γ: its premises divide the rest of Γ, and Δ
      obtain _ | n := n
      · exact absurd hn (Nat.not_lt_zero _)
      have hsz := ssize_pick (picks_perm hr)
      have s := split4 r Δ Θ₁ Θ₂ hΘ.symm
      obtain ⟨q, hq, hq₁, hq₂⟩ := splits_complete s.hΓ
      have hr' := ssize_perm (splits_perm hq)
      rw [ssize_append] at hr'
      have hΔ₁ : FreeL p s.Δ₁ := hΔ.sub fun C hC => s.hΔ.mem_iff.2 (mem_append.2 (.inl hC))
      have hΔ₂ : FreeL p s.Δ₂ := hΔ.sub fun C hC => s.hΔ.mem_iff.2 (mem_append.2 (.inr hC))
      have i₁ := ih₁ n (A :: q.1) s.Δ₁ (by have := s.h₁; perm_count [this, hq₁]) hΔ₁
        (by simp only [Form.size] at hsz; simp only [ssize]; omega)
      have i₂ := ih₂ n (B :: q.2) s.Δ₂ (by have := s.h₂; perm_count [this, hq₂]) hΔ₂
        (by simp only [Form.size] at hsz; simp only [ssize]; omega)
      refine sBig_inj (mem_step_pick hr
        (show sTensor (uiN p n (A :: q.1)) (uiN p n (B :: q.2)) ∈ uiPick _ (A ⊗ B) r from
          mem_map.2 ⟨q, hq, rfl⟩)) (exch ?_ (sTensor_intro i₁ i₂))
      have := s.hΔ
      perm_count [this]
    · -- the ⊗ is in Δ: its premises divide Γ, and the rest of Δ
      have hX : A ⊗ B ∈ Δ := hΔ'.mem_iff.2 (mem_cons_self ..)
      have hsub : ∀ C, C ∈ Δ' → C ∈ Δ := fun C hC => hΔ'.mem_iff.2 (mem_cons_of_mem _ hC)
      have s := split4 Γ Δ' Θ₁ Θ₂ hΘ.symm
      have hfree₁ : FreeL p (A :: s.Δ₁) := fun C hC => by
        rcases mem_cons.1 hC with rfl | hC
        · exact fun hp => hΔ _ hX (mem_append.2 (.inl hp))
        · exact hΔ C (hsub C (s.hΔ.mem_iff.2 (mem_append.2 (.inl hC))))
      have hfree₂ : FreeL p (B :: s.Δ₂) := fun C hC => by
        rcases mem_cons.1 hC with rfl | hC
        · exact fun hp => hΔ _ hX (mem_append.2 (.inr hp))
        · exact hΔ C (hsub C (s.hΔ.mem_iff.2 (mem_append.2 (.inr hC))))
      have sΓ := s.hΓ
      have sΔ := s.hΔ
      have s₁ := s.h₁
      have s₂ := s.h₂
      by_cases e₂ : s.Γ₂ = []
      · -- all of Γ goes to the first premise
        rw [e₂] at sΓ s₂
        obtain ⟨c₁⟩ := ih₁ n Γ (A :: s.Δ₁) (by perm_count [s₁, sΓ]) hfree₁ hn
        exact ⟨.tensor A B (uiN p n Γ :: s.Δ₁) s.Δ₂ (by perm_count [hΔ', sΔ])
          (c₁.exch (.swap ..)) (d₂.exch (by perm_count [s₂])).toFam⟩
      · by_cases e₁ : s.Γ₁ = []
        · -- all of Γ goes to the second premise
          rw [e₁] at sΓ s₁
          obtain ⟨c₂⟩ := ih₂ n Γ (B :: s.Δ₂) (by perm_count [s₂, sΓ]) hfree₂ hn
          exact ⟨.tensor A B s.Δ₁ (uiN p n Γ :: s.Δ₂) (by perm_count [hΔ', sΔ])
            (d₁.exch (by perm_count [s₁])).toFam (c₂.exch (.swap ..))⟩
        · -- Γ is divided: the ⅋ of the interpolants of its parts
          obtain _ | n := n
          · exact absurd hn (Nat.not_lt_zero _)
          obtain ⟨q, hq, hq'⟩ := properSplits_complete sΓ e₁ e₂
          obtain ⟨pq, ne₁, ne₂⟩ := properSplits_spec hq
          have hsz := ssize_perm pq
          rw [ssize_append] at hsz
          have pos : ∀ l : List Form, l ≠ [] → 0 < ssize l := by
            intro l hl
            cases l with
            | nil => exact absurd rfl hl
            | cons C _ => have := C.size_pos; simp only [ssize]; omega
          have pos₁ := pos q.1 ne₁
          have pos₂ := pos q.2 ne₂
          refine sBig_inj (mem_step_split hq) (sPar_intro ?_)
          rcases hq' with ⟨p₁, p₂⟩ | ⟨p₁, p₂⟩
          · obtain ⟨c₁⟩ := ih₁ n q.1 (A :: s.Δ₁) (by perm_count [s₁, p₁]) hfree₁ (by omega)
            obtain ⟨c₂⟩ := ih₂ n q.2 (B :: s.Δ₂) (by perm_count [s₂, p₂]) hfree₂ (by omega)
            exact ⟨.tensor A B (uiN p n q.1 :: s.Δ₁) (uiN p n q.2 :: s.Δ₂)
              (by perm_count [hΔ', sΔ]) (c₁.exch (.swap ..)) (c₂.exch (.swap ..))⟩
          · obtain ⟨c₁⟩ := ih₁ n q.2 (A :: s.Δ₁) (by perm_count [s₁, p₂]) hfree₁ (by omega)
            obtain ⟨c₂⟩ := ih₂ n q.1 (B :: s.Δ₂) (by perm_count [s₂, p₁]) hfree₂ (by omega)
            exact ⟨.tensor A B (uiN p n q.2 :: s.Δ₁) (uiN p n q.1 :: s.Δ₂)
              (by perm_count [hΔ', sΔ]) (c₁.exch (.swap ..)) (c₂.exch (.swap ..))⟩

/-! ## The theorems -/

/-- **Uniform interpolation**, with the interpolant `ui p Γ`. -/
theorem ui_spec (p : Nat) (Γ : List Form) :
    (∀ a ∈ (ui p Γ).letters, a ≠ p ∧ a ∈ lettersL Γ) ∧
    Derivable ((ui p Γ)ᗮ :: Γ) ∧
    ∀ Δ : List Form, (∀ a ∈ lettersL Δ, a ≠ p) → Derivable (Γ ++ Δ) → Derivable (ui p Γ :: Δ) :=
  ⟨fun a ha =>
      let ⟨hne, C, hC, haC⟩ := uiN_letters p _ Γ a ha
      ⟨hne, mem_lettersL.2 ⟨C, hC, haC⟩⟩,
   uiN_below p _ Γ,
   fun Δ hΔ ⟨d⟩ =>
     uiN_greatest p (cutElimination _ d) _ Γ Δ (.refl _)
       (fun C hC hp => hΔ p (mem_lettersL.2 ⟨C, hC, hp⟩) rfl) (Nat.lt_succ_self _)⟩

theorem uniformInterpolation : UniformInterpolation := fun p Γ => ⟨ui p Γ, ui_spec p Γ⟩

theorem UI.lettersL_single {X : Form} {a : Nat} (ha : a ∈ lettersL [X]) : a ∈ X.letters := by
  obtain ⟨C, hC, haC⟩ := mem_lettersL.1 ha
  rcases mem_cons.1 hC with rfl | hC
  · exact haC
  · cases hC

/-- **`∀p A`**: without `p`, implies `A`, and is implied by every formula
without `p` that implies `A`. -/
theorem forallP_spec (p : Nat) (A : Form) :
    (∀ a ∈ (forallP p A).letters, a ≠ p ∧ a ∈ A.letters) ∧ Derivable [(forallP p A)ᗮ, A] ∧
    ∀ B : Form, p ∉ B.letters → Derivable [Bᗮ, A] → Derivable [Bᗮ, forallP p A] := by
  obtain ⟨l, b, g⟩ := ui_spec p [A]
  refine ⟨fun a ha => ⟨(l a ha).1, lettersL_single (l a ha).2⟩, b, fun B hB h => ?_⟩
  have := g [Bᗮ] (fun a ha e => hB (by
    have := lettersL_single ha
    rw [Form.letters_neg] at this
    exact e ▸ this)) (exch (.swap ..) h)
  exact exch (.swap ..) this

/-- **`∃p A`**: without `p`, implied by `A`, and implies every formula
without `p` that `A` implies. -/
theorem existsP_spec (p : Nat) (A : Form) :
    (∀ a ∈ (existsP p A).letters, a ≠ p ∧ a ∈ A.letters) ∧ Derivable [Aᗮ, existsP p A] ∧
    ∀ B : Form, p ∉ B.letters → Derivable [Aᗮ, B] → Derivable [(existsP p A)ᗮ, B] := by
  obtain ⟨l, b, g⟩ := ui_spec p [Aᗮ]
  refine ⟨fun a ha => ?_, exch (.swap ..) b, fun B hB h => ?_⟩
  · have ha' : a ∈ (ui p [Aᗮ]).letters := by
      have : a ∈ ((ui p [Aᗮ])ᗮ).letters := ha
      rwa [Form.letters_neg] at this
    have := lettersL_single (l a ha').2
    rw [Form.letters_neg] at this
    exact ⟨(l a ha').1, this⟩
  · have := g [B] (fun a ha e => hB (e ▸ lettersL_single ha)) h
    show Derivable [(existsP p A)ᗮ, B]
    unfold existsP
    rw [Form.neg_neg]
    exact this

/-- **The uniform interpolants of a formula**: `forallP p A` and
`existsP p A`. -/
theorem uniformInterpolationForFormulas : UniformInterpolationForFormulas := fun p A =>
  ⟨⟨forallP p A, forallP_spec p A⟩, ⟨existsP p A, existsP_spec p A⟩⟩

end MALL

#axioms_within_file [propext, Quot.sound]
