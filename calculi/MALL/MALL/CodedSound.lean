/-
The check of a saturated set in numbers is sound (S27): a certificate that
`codeRefutes` accepts stands for a set of sequents that `refutedBy`
accepts.  So the theorems of `MALL/Saturated.lean` hold of what the
numbers stand for.

The proof has four parts: the arithmetic of digits (a unit added, a unit
taken away, a number divided in two with no carry); the search tree; the
table of formulas; and the walk of one member along the table.

Theory file: it ends with its bound on axioms.
-/
import MALL.Coded

namespace MALL

open List

/-! ## The arithmetic of digits -/

/-- Quotient and remainder of `B * q + c`, for `c < B`. -/
theorem div_mod_of_lt {B c : Nat} (q : Nat) (h : c < B) :
    (B * q + c) % B = c ∧ (B * q + c) / B = q := by
  have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h]
  · rw [Nat.mul_add_div hB, Nat.div_eq_of_lt h, Nat.add_zero]

/-- A number, by its quotient and remainder. -/
theorem eq_div_mod (B d : Nat) : d = B * (d / B) + d % B := (Nat.div_add_mod d B).symm

/-- **Every digit of `d`, with `s` added, is below the base**, at `n`
places, and `d` has no digit beyond them. -/
def Fit (B s : Nat) : Nat → Nat → Prop
  | 0, d => d = 0
  | n + 1, d => d % B + s < B ∧ Fit B s n (d / B)

theorem Fit.mono {B s : Nat} : ∀ {n d : Nat}, Fit B (s + 1) n d → Fit B s n d
  | 0, _, h => h
  | _ + 1, _, ⟨h₁, h₂⟩ => ⟨by omega, Fit.mono h₂⟩

theorem Fit.pos {B s n d : Nat} (h : Fit B s (n + 1) d) : s < B := by
  have := h.1; omega

/-- The sum of the digits. -/
def dsum (B : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, q => q % B + dsum B n (q / B)

theorem dec_zero (B : Nat) : ∀ fs : List Form, dec B fs 0 = []
  | [] => rfl
  | X :: fs => by simp [dec, dec_zero B fs]

theorem length_dec (B : Nat) : ∀ (fs : List Form) (d : Nat), (dec B fs d).length = dsum B fs.length d
  | [], _ => rfl
  | X :: fs, d => by simp [dec, dsum, length_dec B fs]

/-- A formula of the sequent of a number stands at a place whose digit is
not 0. -/
theorem mem_dec {B : Nat} {X : Form} :
    ∀ {fs : List Form} {d : Nat}, X ∈ dec B fs d → ∃ i, fs[i]? = some X ∧ 1 ≤ d / B ^ i % B
  | [], _, h => by cases h
  | Y :: fs, d, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨hn, rfl⟩ := List.mem_replicate.1 h
      exact ⟨0, rfl, by simp only [Nat.pow_zero, Nat.div_one]; omega⟩
    · obtain ⟨i, hi, hd⟩ := mem_dec h
      refine ⟨i + 1, hi, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      exact hd

/-- **A unit added**: where the digit has room, the formula at the place is
put in the sequent. -/
theorem dec_add_unit {B s : Nat} {X : Form} :
    ∀ {fs : List Form} {a r : Nat}, fs[a]? = some X → Fit B (s + 1) fs.length r →
      Fit B s fs.length (r + B ^ a) ∧ dec B fs (r + B ^ a) ~ X :: dec B fs r
  | [], _, _, h, _ => by cases h
  | Y :: fs, 0, r, h, hf => by
    obtain rfl : Y = X := by simpa using h
    obtain ⟨h₁, h₂⟩ := hf
    have hc : r % B + 1 < B := by omega
    have e : r + B ^ 0 = B * (r / B) + (r % B + 1) := by
      have := eq_div_mod B r; rw [Nat.pow_zero]; omega
    obtain ⟨em, ed⟩ := div_mod_of_lt (r / B) hc
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [e, em]; omega
    · rw [e, ed]; exact Fit.mono h₂
    · rw [e]; simp only [dec, em, ed, List.replicate_succ, List.cons_append]; exact .refl _
  | Y :: fs, a + 1, r, h, hf => by
    obtain ⟨h₁, h₂⟩ := hf
    have hB : 0 < B := by omega
    have e : r + B ^ (a + 1) = r + B * B ^ a := by rw [Nat.pow_succ, Nat.mul_comm]
    have em : (r + B * B ^ a) % B = r % B := Nat.add_mul_mod_self_left ..
    have ed : (r + B * B ^ a) / B = r / B + B ^ a := Nat.add_mul_div_left _ _ hB
    obtain ⟨f, p⟩ := dec_add_unit (fs := fs) (a := a) (r := r / B) h h₂
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [e, em]; omega
    · rw [e, ed]; exact f
    · rw [e]; simp only [dec, em, ed]
      exact (List.Perm.append_left _ p).trans List.perm_middle

/-- **A unit taken away**: where the digit is not 0, the formula at the
place is taken out of the sequent. -/
theorem dec_sub_unit {B : Nat} (hB : 0 < B) {X : Form} :
    ∀ {fs : List Form} {i d : Nat}, fs[i]? = some X → 1 ≤ d / B ^ i % B →
      B ^ i ≤ d ∧ X :: dec B fs (d - B ^ i) ~ dec B fs d ∧
        ∀ s, Fit B s fs.length d → Fit B s fs.length (d - B ^ i)
  | [], _, _, h, _ => by cases h
  | Y :: fs, 0, d, h, hd => by
    obtain rfl : Y = X := by simpa using h
    simp only [Nat.pow_zero, Nat.div_one] at hd ⊢
    have hlt : d % B < B := Nat.mod_lt _ hB
    have hc : d % B - 1 < B := by omega
    have e : d - 1 = B * (d / B) + (d % B - 1) := by have := eq_div_mod B d; omega
    obtain ⟨em, ed⟩ := div_mod_of_lt (d / B) hc
    refine ⟨by have := Nat.mod_le d B; omega, ?_, ?_⟩
    · rw [e]; simp only [dec, em, ed]
      have : d % B = (d % B - 1) + 1 := by omega
      conv => rhs; rw [this, List.replicate_succ]
      exact .refl _
    · intro s ⟨h₁, h₂⟩
      exact ⟨by rw [e, em]; omega, by rw [e, ed]; exact h₂⟩
  | Y :: fs, i + 1, d, h, hd => by
    have hd' : 1 ≤ d / B / B ^ i % B := by
      rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul] at hd; exact hd
    obtain ⟨hle, p, f⟩ := dec_sub_unit hB (fs := fs) (i := i) (d := d / B) h hd'
    have e : B ^ (i + 1) = B * B ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
    have hle' : B * B ^ i ≤ d := by
      have := (Nat.le_div_iff_mul_le hB).1 hle; rw [Nat.mul_comm] at this; exact this
    have em : (d - B * B ^ i) % B = d % B := Nat.sub_mul_mod hle'
    have ed : (d - B * B ^ i) / B = d / B - B ^ i := Nat.sub_mul_div _ _ _
    refine ⟨by rw [e]; exact hle', ?_, ?_⟩
    · rw [e]; simp only [dec, em, ed]
      exact List.perm_middle.symm.trans (List.Perm.append_left _ p)
    · intro s ⟨h₁, h₂⟩
      exact ⟨by rw [e, em]; exact h₁, by rw [e, ed]; exact f s h₂⟩

/-! ## A number divided in two -/

/-- A list of copies of one formula, divided in two. -/
theorem replicate_split {c : Nat} {Y : Form} {a₁ a₂ : List Form}
    (h : List.replicate c Y ~ a₁ ++ a₂) :
    a₁ = List.replicate a₁.length Y ∧ a₂ = List.replicate a₂.length Y ∧ a₁.length + a₂.length = c := by
  have hm : ∀ b ∈ a₁ ++ a₂, b = Y := fun b hb => (List.mem_replicate.1 (h.mem_iff.2 hb)).2
  refine ⟨List.eq_replicate_iff.2 ⟨rfl, fun b hb => hm b (List.mem_append.2 (.inl hb))⟩,
    List.eq_replicate_iff.2 ⟨rfl, fun b hb => hm b (List.mem_append.2 (.inr hb))⟩, ?_⟩
  have := h.length_eq
  simp only [List.length_replicate, List.length_append] at this
  exact this.symm

/-- The numbers that `allParts` runs through, for a support: at each
formula present, at most its digit of its unit. -/
def InParts : List (Nat × Nat) → Nat → Prop
  | [], x => x = 0
  | (u, c) :: s, x => ∃ k x', k ≤ c ∧ InParts s x' ∧ x = k * u + x'

theorem upTo_spec {f : Nat → Bool} {u : Nat} :
    ∀ {c x : Nat}, upTo f u c x = true → ∀ k, k ≤ c → f (x + k * u) = true
  | 0, x, h, k, hk => by
    obtain rfl : k = 0 := by omega
    simpa [upTo] using h
  | c + 1, x, h, k, hk => by
    simp only [upTo, Bool.and_eq_true] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := upTo_spec h.2 k (by omega)
      rw [show x + (k + 1) * u = x + u + k * u by rw [Nat.succ_mul]; omega]
      exact this

/-- `allParts` reaches every number of `InParts`. -/
theorem allParts_spec {P : Nat → Bool} :
    ∀ {s : List (Nat × Nat)} {x₀ x : Nat}, allParts P s x₀ = true → InParts s x → P (x₀ + x) = true
  | [], x₀, x, h, hx => by
    obtain rfl : x = 0 := hx
    simpa [allParts] using h
  | (u, c) :: s, x₀, x, h, ⟨k, x', hk, hx', e⟩ => by
    have := allParts_spec (upTo_spec (f := allParts P s) h k hk) hx'
    rw [e, ← Nat.add_assoc]; exact this

/-- **A number divided in two with no carry**: every way to divide the
sequent of `r` in two is the sequents of two numbers whose sum is `r`, and
`allParts` reaches the first. -/
theorem dec_split {B s : Nat} :
    ∀ {fs : List Form} {r : Nat} (u : Nat) {Γ₁ Γ₂ : List Form},
      Fit B s fs.length r → dec B fs r ~ Γ₁ ++ Γ₂ →
      ∃ x y, x + y = r ∧ InParts (support B fs.length r u) (u * x) ∧
        Fit B s fs.length x ∧ Fit B s fs.length y ∧ dec B fs x ~ Γ₁ ∧ dec B fs y ~ Γ₂
  | [], r, u, Γ₁, Γ₂, hf, h => by
    obtain rfl : r = 0 := hf
    have e := perm_nil_eq h.symm
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 e
    exact ⟨0, 0, rfl, by simp [support, InParts], rfl, rfl, .refl _, .refl _⟩
  | Y :: fs, r, u, Γ₁, Γ₂, ⟨hc, hf⟩, h => by
    obtain ⟨a₁, a₂, b₁, b₂, ha, hb, h₁, h₂⟩ := split4 _ _ _ _ h
    obtain ⟨e₁, e₂, el⟩ := replicate_split ha
    obtain ⟨x', y', exy, hp, fx, fy, px, py⟩ := dec_split (u * B) hf hb
    have hk : a₁.length < B := by omega
    have hk' : a₂.length < B := by omega
    obtain ⟨xm, xd⟩ := div_mod_of_lt x' hk
    obtain ⟨ym, yd⟩ := div_mod_of_lt y' hk'
    refine ⟨B * x' + a₁.length, B * y' + a₂.length, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · have := eq_div_mod B r
      rw [← exy, Nat.mul_add] at this; omega
    · have hu : u * (B * x' + a₁.length) = a₁.length * u + u * B * x' := by
        rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm u a₁.length]; omega
      simp only [List.length_cons, support]
      cases hz : Nat.beq (r % B) 0 with
      | true =>
        have : r % B = 0 := Nat.eq_of_beq_eq_true hz
        have : a₁.length = 0 := by omega
        simp only [cond_true]
        rw [hu, this, Nat.zero_mul, Nat.zero_add]; exact hp
      | false =>
        simp only [cond_false]
        exact ⟨a₁.length, u * B * x', by omega, hp, hu⟩
    · rw [xm]; omega
    · rw [xd]; exact fx
    · rw [ym]; omega
    · rw [yd]; exact fy
    · simp only [dec, xm, xd]
      rw [← e₁]
      exact (List.Perm.append_left _ px).trans h₁.symm
    · simp only [dec, ym, yd]
      rw [← e₂]
      exact (List.Perm.append_left _ py).trans h₂.symm

/-! ## The search tree -/

theorem Tree.mem_of_has : ∀ {t : Tree} {c : Nat}, t.has c = true → c ∈ t.keys
  | .leaf, _, h => by simp [Tree.has] at h
  | .node l k r, c, h => by
    simp only [Tree.has] at h
    simp only [Tree.keys, List.mem_append, List.mem_cons]
    cases h₁ : Nat.ble k c with
    | false => rw [h₁] at h; exact .inl (Tree.mem_of_has h)
    | true =>
      rw [h₁] at h
      cases h₂ : Nat.ble c k with
      | false => rw [h₂] at h; exact .inr (.inr (Tree.mem_of_has h))
      | true => exact .inr (.inl (Nat.le_antisymm (Nat.le_of_ble_eq_true h₂) (Nat.le_of_ble_eq_true h₁)))

theorem Tree.all_spec {P : Nat → Bool} : ∀ {t : Tree}, Tree.all P t = true → ∀ k ∈ t.keys, P k = true
  | .leaf, _, _, hk => by cases hk
  | .node l k r, h, k', hk => by
    simp only [Tree.all, Bool.and_eq_true] at h
    simp only [Tree.keys, List.mem_append, List.mem_cons] at hk
    rcases hk with hk | rfl | hk
    · exact Tree.all_spec h.1.1 _ hk
    · exact h.1.2
    · exact Tree.all_spec h.2 _ hk

/-! ## The table of formulas -/

theorem forms_length : ∀ T : List Node, (forms T).length = T.length
  | [] => rfl
  | _ :: T => by simp [forms, forms_length T]

theorem forms_drop : ∀ (T : List Node) (k : Nat), forms (T.drop k) = (forms T).drop k
  | _, 0 => rfl
  | [], _ + 1 => rfl
  | _ :: T, k + 1 => by simp [forms, forms_drop T k]

/-- The formula at a place is the formula of the entry there, over the
formulas of the entries after it. -/
theorem forms_getElem? : ∀ (T : List Node) (i : Nat),
    (forms T)[i]? = T[i]?.map fun N => N.form (forms (T.drop (i + 1)))
  | [], _ => rfl
  | _ :: T, 0 => rfl
  | _ :: T, i + 1 => by simpa [forms] using forms_getElem? T i

/-- The part of a formula that its entry places `a` entries later stands
at that place. -/
theorem forms_child {T : List Node} {i a : Nat} (h : i + 1 + a < T.length) :
    (forms T)[i + 1 + a]? = some ((forms (T.drop (i + 1))).getD a .one) := by
  rw [forms_drop, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have : i + 1 + a < (forms T).length := by rw [forms_length]; exact h
  rw [List.getElem?_eq_getElem this]; rfl

/-! ## The walk of one member -/

/-- What the walk has checked, from a place on: the digits fit; the
condition holds at each place with a digit that is not 0; and the member
has more than two formulas or is not an axiom. -/
theorem walk_spec {B n : Nat} {t : Tree} {fs : List Form} {d : Nat} :
    ∀ {Ts : List Node} {i q s : Nat}, walk B n t fs d Ts i q s = true →
      Fit B 2 Ts.length q ∧
      (∀ j N, Ts[j]? = some N → 1 ≤ q / B ^ j % B →
        nodeOK B n t (d - B ^ (i + j)) (i + j) N = true) ∧
      (2 < s + dsum B Ts.length q ∨ axFree (dec B fs d) = true)
  | [], i, q, s, h => by
    simp only [walk, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at h
    refine ⟨Nat.eq_of_beq_eq_true h.1, fun j N hj _ => by simp at hj, ?_⟩
    rcases h.2 with h | h
    · exact .inl (by simp only [List.length_nil, dsum]; omega)
    · exact .inr h
  | N :: Ts, i, q, s, h => by
    simp only [walk, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
    obtain ⟨f, nd, ax⟩ := walk_spec h₃
    refine ⟨⟨h₁, f⟩, ?_, ?_⟩
    · intro j N' hj hd
      cases j with
      | zero =>
        obtain rfl : N = N' := by simpa using hj
        simp only [Nat.pow_zero, Nat.div_one] at hd
        cases hz : Nat.beq (q % B) 0 with
        | true => have := Nat.eq_of_beq_eq_true hz; omega
        | false => rw [hz] at h₂; simpa using h₂
      | succ j =>
        have hd' : 1 ≤ q / B / B ^ j % B := by
          rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul] at hd; exact hd
        have := nd j N' (by simpa using hj) hd'
        rw [show i + (j + 1) = i + 1 + j by omega]; exact this
    · rcases ax with ax | ax
      · exact .inl (by simp only [List.length_cons, dsum]; omega)
      · exact .inr ax

/-- A number of the tree stands for a member of the set. -/
theorem CodeCert.memP_of_has (C : CodeCert) {e : Nat} {Δ : List Form} (h : C.tree.has e = true)
    (p : dec C.B (forms C.table) e ~ Δ) : memP C.sequents Δ = true :=
  memP_of_perm p (memP_of_mem (List.mem_map.2 ⟨e, Tree.mem_of_has h, rfl⟩))

/-- **One member**: where the walk passes, the condition of saturation
holds at every formula of the sequent of the number. -/
theorem CodeCert.member_sat (C : CodeCert) {d : Nat} (h : C.memberOK d = true)
    {p : Form × List Form} (hp : p ∈ picks (dec C.B (forms C.table) d)) :
    satAt C.sequents p.1 p.2 = true := by
  obtain ⟨X, Γ'⟩ := p
  have h' : walk C.B C.table.length C.tree (forms C.table) d C.table 0 d 0 = true := h
  obtain ⟨fit, nd, ax⟩ := walk_spec h'
  have pδ : dec C.B (forms C.table) d ~ X :: Γ' := picks_perm hp
  obtain ⟨i, hi, hd⟩ := mem_dec (pδ.mem_iff.2 (mem_cons_self ..))
  have hi' := hi
  rw [forms_getElem?] at hi'
  obtain ⟨N, hN, eX⟩ := Option.map_eq_some_iff.1 hi'
  have hlt : i < C.table.length := (List.getElem?_eq_some_iff.1 hN).1
  have hB : 2 < C.B := by
    obtain ⟨k, hk⟩ : ∃ k, C.table.length = k + 1 := ⟨C.table.length - 1, by omega⟩
    rw [hk] at fit; exact fit.pos
  have fit' : Fit C.B 2 (forms C.table).length d := by rw [forms_length]; exact fit
  obtain ⟨_, pr, fr⟩ := dec_sub_unit (by omega : 0 < C.B) hi hd
  have hr : dec C.B (forms C.table) (d - C.B ^ i) ~ Γ' := (pr.trans pδ).cons_inv
  have fitr := fr 2 fit'
  have ok := nd i N hN hd
  simp only [Nat.zero_add] at ok
  have axδ : 2 < (dec C.B (forms C.table) d).length ∨ axFree (dec C.B (forms C.table) d) = true := by
    rw [length_dec, forms_length]; simpa using ax
  subst eX
  cases N with
  | atom a =>
    simp only [Node.form, satAt, decide_eq_true_eq]
    rintro rfl
    rcases perm_pair pδ with e | e <;> rw [e] at axδ <;> simp [axFree, Node.form] at axδ
  | natom a => rfl
  | one =>
    simp only [Node.form, satAt, decide_eq_true_eq]
    rintro rfl
    rw [perm_singleton_eq pδ] at axδ
    simp [axFree, Node.form] at axδ
  | zero => rfl
  | top => simp [nodeOK] at ok
  | bot => exact C.memP_of_has (by simpa [nodeOK] using ok) hr
  | par a c =>
    simp only [nodeOK, Bool.and_eq_true, Nat.blt_eq] at ok
    obtain ⟨⟨ha, hc⟩, hh⟩ := ok
    obtain ⟨f₁, p₁⟩ := dec_add_unit (s := 1) (forms_child ha) fitr
    obtain ⟨_, p₂⟩ := dec_add_unit (s := 0) (forms_child hc) f₁
    exact C.memP_of_has hh
      (p₂.trans (((p₁.cons _).trans (List.Perm.swap ..)).trans ((hr.cons _).cons _)))
  | wth a c =>
    simp only [nodeOK, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at ok
    obtain ⟨⟨ha, hc⟩, hh⟩ := ok
    simp only [Node.form, satAt, Bool.or_eq_true]
    rcases hh with hh | hh
    · exact .inl (C.memP_of_has hh
        ((dec_add_unit (s := 1) (forms_child ha) fitr).2.trans (hr.cons _)))
    · exact .inr (C.memP_of_has hh
        ((dec_add_unit (s := 1) (forms_child hc) fitr).2.trans (hr.cons _)))
  | plus a c =>
    simp only [nodeOK, Bool.and_eq_true, Nat.blt_eq] at ok
    obtain ⟨⟨ha, hc⟩, hh₁, hh₂⟩ := ok
    simp only [Node.form, satAt, Bool.and_eq_true]
    exact ⟨C.memP_of_has hh₁ ((dec_add_unit (s := 1) (forms_child ha) fitr).2.trans (hr.cons _)),
      C.memP_of_has hh₂ ((dec_add_unit (s := 1) (forms_child hc) fitr).2.trans (hr.cons _))⟩
  | tensor a c =>
    simp only [nodeOK, Bool.and_eq_true, Nat.blt_eq] at ok
    obtain ⟨⟨ha, hc⟩, hall⟩ := ok
    simp only [Node.form, satAt, List.all_eq_true, Bool.or_eq_true]
    intro sp hsp
    obtain ⟨x, y, exy, hin, fx, fy, px, py⟩ := dec_split 1 fitr (hr.trans (splits_perm hsp))
    rw [forms_length] at hin
    have := allParts_spec hall hin
    simp only [Nat.zero_add, Nat.one_mul, Bool.or_eq_true] at this
    rcases this with hh | hh
    · exact .inl (C.memP_of_has hh
        ((dec_add_unit (s := 1) (forms_child ha) fx).2.trans (px.cons _)))
    · rw [show d - C.B ^ i - x = y by omega] at hh
      exact .inr (C.memP_of_has hh
        ((dec_add_unit (s := 1) (forms_child hc) fy).2.trans (py.cons _)))

/-! ## The sequent refuted -/

/-- The formulas at the places, taken out of a number one by one with
nothing left, are its sequent. -/
theorem drain_spec {B : Nat} {fs : List Form} (hB : 0 < fs.length → 0 < B) :
    ∀ {l : List Nat} {g : Nat}, CodeCert.drain B fs.length g l = true →
      dec B fs g ~ l.map fun i => fs.getD i .one
  | [], g, h => by
    obtain rfl : g = 0 := Nat.eq_of_beq_eq_true h
    rw [dec_zero]; exact .refl _
  | i :: l, g, h => by
    simp only [CodeCert.drain, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨⟨hi, hd⟩, h⟩ := h
    have e : fs[i]? = some (fs.getD i .one) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    obtain ⟨_, p, _⟩ := dec_sub_unit (hB (by omega)) e hd
    exact p.symm.trans ((drain_spec hB h).cons _)

/-- **S27.**  A certificate in numbers that passes stands for a set of
sequents that passes the check of `MALL/Saturated.lean`. -/
theorem refutedBy_of_code : CodeSoundness := by
  intro C Γ h
  simp only [codeRefutes, CodeCert.goalOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨eΓ, hg⟩, hdr⟩, hall⟩ := h
  have hmem := Tree.all_spec hall
  simp only [refutedBy, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · have hB : 0 < (forms C.table).length → 0 < C.B := by
      rw [forms_length]
      intro hpos
      have h' : walk C.B C.table.length C.tree (forms C.table) _ C.table 0 _ 0 = true :=
        hmem _ (Tree.mem_of_has hg)
      obtain ⟨fit, _, _⟩ := walk_spec h'
      obtain ⟨k, hk⟩ : ∃ k, C.table.length = k + 1 := ⟨C.table.length - 1, by omega⟩
      rw [hk] at fit
      have := fit.pos; omega
    rw [← forms_length] at hdr
    rw [eΓ]
    exact C.memP_of_has hg (drain_spec hB hdr)
  · simp only [saturated, List.all_eq_true]
    intro δ hδ pk hpk
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hδ
    exact C.member_sat (hmem k hk) hpk

/-- A certificate in numbers that passes: the sequent has no derivation. -/
theorem not_derivable_of_code {C : CodeCert} {Γ : List Form} (h : codeRefutes C Γ = true) :
    ¬ Derivable Γ :=
  not_derivable_of_refutedBy (refutedBy_of_code C Γ h)

/-- And is not valid. -/
theorem not_valid_of_code {C : CodeCert} {Γ : List Form} (h : codeRefutes C Γ = true) :
    ¬ Valid Γ :=
  not_valid_of_refutedBy (refutedBy_of_code C Γ h)

/-- The set that the numbers stand for presents a finite phase structure
in which the sequent does not hold. -/
theorem countermodel_of_code {C : CodeCert} {Γ : List Form} (h : codeRefutes C Γ = true) :
    ∃ S : PhaseStructure, S.Finite ∧ ¬ S.Sat Γ :=
  countermodel_of_refutedBy (refutedBy_of_code C Γ h)

end MALL

#axioms_within_file [propext, Quot.sound]
