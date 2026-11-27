/-
The replay of a tree of moves with each side of a sequent kept as a list
of formulas with the number of occurrences of each: the check of the
certifier `treeCert` (`GLS/Run.lean`).

`Cert.check` (`ProofTools.Explore.Cert`) is the definition: `step` at the
root, then each child at its premise.  The premise of GLR is
`xbox Γ ++ [□A] ⇒ [A]`, and `xbox Γ` has `B, □B` for each `□B` of `Γ`: a
formula with `n` nested boxes in the antecedent gives `2ⁿ` formulas after
`n` steps of GLR, so the sequents of GLS, written out, grow like `2ⁿ`
along a tree of `n` moves.  A replay that writes each sequent out as a
list is that large (compiled: 1.3 s and 2.2 GB at `n = 24`).

No rule of GLS looks at the order of a side, only at how often a formula
occurs in it: whether a move applies depends on whether a count is
positive, and the counts of a premise are computed from the counts of the
conclusion.  Here a side is a list of formulas, each with its count, as a
number; the formulas of all the sequents of a derivation are subformulas
of its end sequent, so the list stays short while the counts grow.

The entries of a side are kept in order of the size of the formula, so
that the premise of GLR is made in one pass: the boxed entries, and the
same entries each less its box, are two lists in order, and are merged.
The formula that ImpR or ImpL adds is put at the head of the entries of
its size, with no search (`put`): a formula can then be listed twice, at
most once more for each such move.  (With a search among the entries of
its size, the kernel took 4.2 s on `kChain 128`, where a side has 128
variables, against 1.4 s; with no search for the `□A` of GLR either, a
formula was listed again at each GLR of `lastChain`, and the kernel took
3.8 s at 128 against 2.5 s.)
(A first form looked each formula up in the whole side: at each GLR the
square of the number of entries in comparisons of formulas, and in the
kernel 3.7 s at 64 nested boxes and over 8 GB at 128.)  The order is not
part of what is proved: a count is a sum over the entries of a formula
wherever they are.

    countCheck (CSeq.of s) c = Cert.check s c           (countCheck_eq)

Theory file: it ends with its bound on axioms.
-/
import GLS.Proof

namespace GLS

open ProofTools ProofTools.Explore

/-- **A side of a sequent by counts**: formulas, each with a tag and a
number of occurrences.  The tag is a number by which the entries are kept
in order, the size of the formula; nothing that is proved rests on the
tags or on the order, which only keep the work down.  A formula may be
listed more than once: its count is the sum. -/
abbrev Counts : Type := List (Form × Nat × Nat)

namespace Counts

/-- How often a formula occurs. -/
def cnt (A : Form) : Counts → Nat
  | [] => 0
  | (B, _, c) :: m => if B = A then c + cnt A m else cnt A m

/-- The formula occurs. -/
def has (A : Form) : Counts → Bool
  | [] => false
  | (B, _, c) :: m => if B = A then (if c = 0 then has A m else true) else has A m

/-- `c` more occurrences of a formula with tag `t`: added to an entry of
that tag and formula, or as a new entry after the entries of smaller or
equal tag. -/
def ins (A : Form) (t c : Nat) : Counts → Counts
  | [] => [(A, t, c)]
  | (B, u, d) :: m =>
    if t < u then (A, t, c) :: (B, u, d) :: m
    else if u < t then (B, u, d) :: ins A t c m
    else if B = A then (B, u, d + c) :: m
    else (B, u, d) :: ins A t c m

/-- `c` more occurrences of a formula with tag `t`, with no search: added
to the first entry of that tag if it is the formula's, or as a new entry
before it.  For the one formula a move adds; an entry of the formula
further on is left as it is, and the formula is then listed twice. -/
def put (A : Form) (t c : Nat) : Counts → Counts
  | [] => [(A, t, c)]
  | (B, u, d) :: m =>
    if u < t then (B, u, d) :: put A t c m
    else if t < u then (A, t, c) :: (B, u, d) :: m
    else if B = A then (B, u, d + c) :: m
    else (A, t, c) :: (B, u, d) :: m

/-- One occurrence fewer of a formula, if it occurs. -/
def dec (A : Form) : Counts → Counts
  | [] => []
  | (B, u, d) :: m =>
    if B = A then (if d = 0 then (B, u, d) :: dec A m else (B, u, d - 1) :: m)
    else (B, u, d) :: dec A m

/-- The counts of a list. -/
def of : List Form → Counts
  | [] => []
  | A :: l => put A A.size 1 (of l)

/-- One entry put into a list of entries in order of tag, where `k` goes
on with what is left of the list. -/
def mergeInto (A : Form) (t c : Nat) (k : Counts → Counts) : Counts → Counts
  | [] => (A, t, c) :: k []
  | (B, u, d) :: m =>
    if u < t then (B, u, d) :: mergeInto A t c k m
    else if t < u then (A, t, c) :: k ((B, u, d) :: m)
    else ins A t c (k ((B, u, d) :: m))

/-- Two lists of entries as one: in order of tag where both are, in one
pass; entries of one tag are put together by `ins`. -/
def merge : Counts → Counts → Counts
  | [], m₂ => m₂
  | (A, t, c) :: m₁, m₂ => mergeInto A t c (merge m₁) m₂

/-- The boxed entries. -/
def boxes : Counts → Counts
  | [] => []
  | (□D, t, c) :: m => (□D, t, c) :: boxes m
  | _ :: m => boxes m

/-- The boxed entries, each less its box: the tag is one less. -/
def unboxes : Counts → Counts
  | [] => []
  | (□D, t, c) :: m => (D, t - 1, c) :: unboxes m
  | _ :: m => unboxes m

/-- The counts of `xbox Γ` from those of `Γ`: each `□D` gives as many `D`
and as many `□D` as it has occurrences. -/
def xbox (m : Counts) : Counts := merge (unboxes m) (boxes m)

end Counts

/-- **A sequent by counts.** -/
structure CSeq where
  /-- The antecedent. -/
  ant : Counts
  /-- The succedent. -/
  suc : Counts
  deriving Repr

/-- The counts of a sequent. -/
def CSeq.of (s : Seq) : CSeq := ⟨.of s.ant, .of s.suc⟩

open Counts in
/-- **One step, by counts**: the premises of the move, or nothing where
it does not apply.  The side conditions and the premises are those of
`Move.rule`, read on the counts. -/
def countStep (m : Move) (j : CSeq) : Option (List CSeq) :=
  match m with
  | .idP p =>
    if has (.var p) j.ant && has (.var p) j.suc then some [] else none
  | .botL => if has ⊥ j.ant then some [] else none
  | .impR A B =>
    if has (A ⟶ B) j.suc then
      some [⟨put A A.size 1 j.ant, put B B.size 1 (dec (A ⟶ B) j.suc)⟩]
    else none
  | .impL A B =>
    if has (A ⟶ B) j.ant then
      some [⟨dec (A ⟶ B) j.ant, put A A.size 1 j.suc⟩,
        ⟨put B B.size 1 (dec (A ⟶ B) j.ant), j.suc⟩]
    else none
  | .glr A =>
    if has (□A) j.suc then
      some [⟨ins (□A) (A.size + 1) 1 (Counts.xbox j.ant), [(A, A.size, 1)]⟩]
    else none

mutual
  /-- **The replay by counts**: `countStep` at the root, then each child
  at its premise, as many children as premises. -/
  def countCheck : CSeq → Cert S → Bool
    | j, .node m cs =>
      match countStep m j with
      | some ps => countCheckL ps cs
      | none => false
  /-- `countCheck` on a list. -/
  def countCheckL : List CSeq → List (Unit × Cert S) → Bool
    | [], [] => true
    | p :: ps, (_, c) :: cs => countCheck p c && countCheckL ps cs
    | _, _ => false
end

/-- **The check of a tree of moves at a sequent, by counts.** -/
def Seq.countCheck (s : Seq) (c : Cert S) : Bool := GLS.countCheck (.of s) c

/-! ## The counts are right -/

/-- A boxed formula. -/
def Form.boxed : Form → Bool
  | □_ => true
  | _ => false

namespace Counts

theorem cnt_cons (X B : Form) (u d : Nat) (m : Counts) :
    cnt X ((B, u, d) :: m) = (if B = X then d else 0) + cnt X m := by
  by_cases h : B = X <;> simp [cnt, h]

theorem cnt_ins (A X : Form) (t c : Nat) (m : Counts) :
    cnt X (ins A t c m) = cnt X m + if A = X then c else 0 := by
  induction m with
  | nil => simp [ins, cnt_cons, cnt]
  | cons e m ih =>
    obtain ⟨B, u, d⟩ := e
    unfold ins
    split
    · rw [cnt_cons, Nat.add_comm]
    · split
      · rw [cnt_cons, ih, cnt_cons, Nat.add_assoc]
      · split
        · next hBA =>
          subst hBA
          rw [cnt_cons, cnt_cons]
          split <;> omega
        · rw [cnt_cons, ih, cnt_cons, Nat.add_assoc]

theorem cnt_put (A X : Form) (t c : Nat) (m : Counts) :
    cnt X (put A t c m) = cnt X m + if A = X then c else 0 := by
  induction m with
  | nil => simp [put, cnt_cons, cnt]
  | cons e m ih =>
    obtain ⟨B, u, d⟩ := e
    unfold put
    split
    · rw [cnt_cons, ih, cnt_cons, Nat.add_assoc]
    · split
      · rw [cnt_cons, Nat.add_comm]
      · split
        · next hBA =>
          subst hBA
          rw [cnt_cons, cnt_cons]
          split <;> omega
        · rw [cnt_cons, Nat.add_comm]

theorem cnt_dec (A X : Form) (m : Counts) :
    cnt X (dec A m) = cnt X m - if A = X then 1 else 0 := by
  induction m with
  | nil => simp [dec, cnt]
  | cons e m ih =>
    obtain ⟨B, u, d⟩ := e
    unfold dec
    split
    · next hBA =>
      subst hBA
      split
      · next hd =>
        subst hd
        rw [cnt_cons, ih, cnt_cons]
        split <;> omega
      · rw [cnt_cons, cnt_cons]
        split <;> omega
    · next hBA =>
      rw [cnt_cons, ih, cnt_cons]
      by_cases hAX : A = X
      · subst hAX
        simp [hBA]
      · simp [hAX]

theorem has_eq (A : Form) (m : Counts) : has A m = decide (0 < cnt A m) := by
  induction m with
  | nil => simp [has, cnt]
  | cons e m ih =>
    obtain ⟨B, u, d⟩ := e
    unfold has
    rw [cnt_cons]
    split
    · split
      · next hd => simp [ih, hd]
      · next hd => exact (decide_eq_true (by omega)).symm
    · simp [ih]

theorem cnt_mergeInto (A X : Form) (t c : Nat) (k : Counts → Counts) (K : Nat)
    (hk : ∀ m, cnt X (k m) = K + cnt X m) (m : Counts) :
    cnt X (mergeInto A t c k m) = (if A = X then c else 0) + K + cnt X m := by
  induction m with
  | nil => rw [mergeInto, cnt_cons, hk]
           simp [cnt]
  | cons e m ih =>
    obtain ⟨B, u, d⟩ := e
    unfold mergeInto
    split
    · rw [cnt_cons, ih, cnt_cons]
      omega
    · split
      · rw [cnt_cons, hk]
        omega
      · rw [cnt_ins, hk]
        omega

theorem cnt_merge (X : Form) (m₁ m₂ : Counts) :
    cnt X (merge m₁ m₂) = cnt X m₁ + cnt X m₂ := by
  induction m₁ generalizing m₂ with
  | nil => simp [merge, cnt]
  | cons e m₁ ih =>
    obtain ⟨A, t, c⟩ := e
    rw [merge, cnt_mergeInto A X t c (merge m₁) (cnt X m₁) (fun m => ih m), cnt_cons]

theorem cnt_boxes (X : Form) (m : Counts) :
    cnt X (boxes m) = if X.boxed then cnt X m else 0 := by
  induction m with
  | nil => simp [boxes, cnt]
  | cons e m ih =>
    obtain ⟨C, u, d⟩ := e
    cases C with
    | var n => cases X <;> simp [boxes, cnt, Form.boxed, ih]
    | bot => cases X <;> simp [boxes, cnt, Form.boxed, ih]
    | imp C₁ C₂ => cases X <;> simp [boxes, cnt, Form.boxed, ih]
    | box D =>
      rw [show boxes ((□D, u, d) :: m) = (□D, u, d) :: boxes m from rfl, cnt_cons, ih, cnt_cons]
      by_cases h : □D = X
      · subst h
        simp [Form.boxed]
      · simp [h]

theorem cnt_unboxes (X : Form) (m : Counts) : cnt X (unboxes m) = cnt (□X) m := by
  induction m with
  | nil => simp [unboxes, cnt]
  | cons e m ih =>
    obtain ⟨C, u, d⟩ := e
    cases C with
    | var n => simp [unboxes, cnt, ih]
    | bot => simp [unboxes, cnt, ih]
    | imp C₁ C₂ => simp [unboxes, cnt, ih]
    | box D =>
      rw [show unboxes ((□D, u, d) :: m) = (D, u - 1, d) :: unboxes m from rfl, cnt_cons, ih,
        cnt_cons]
      by_cases h : D = X <;> simp [h]

theorem cnt_xbox (B : Form) (m : Counts) :
    cnt B (Counts.xbox m) = cnt (□B) m + if B.boxed then cnt B m else 0 := by
  rw [Counts.xbox, cnt_merge, cnt_unboxes, cnt_boxes]

/-- **The counts of a list of formulas**: each formula as often as it
occurs. -/
def Rep (m : Counts) (l : List Form) : Prop := ∀ A, cnt A m = l.count A

theorem Rep.cons {m : Counts} {l : List Form} (h : Rep m l) (A : Form) (t : Nat) :
    Rep (put A t 1 m) (A :: l) := by
  intro B
  by_cases hAB : A = B <;> simp [cnt_put, h B, hAB]

theorem Rep.of (l : List Form) : Rep (of l) l := by
  induction l with
  | nil => intro A; rfl
  | cons C l ih => exact ih.cons C _

theorem Rep.snoc {m : Counts} {l : List Form} (h : Rep m l) (A : Form) (t : Nat) :
    Rep (ins A t 1 m) (l ++ [A]) := by
  intro B
  by_cases hAB : A = B <;> simp [cnt_ins, h B, List.count_append, hAB]

/-- How often a formula occurs in a list less one occurrence of a
formula. -/
theorem count_erase (A B : Form) (l : List Form) :
    (l.erase A).count B = l.count B - if A = B then 1 else 0 := by
  induction l with
  | nil => simp
  | cons C l ih =>
    by_cases hCA : C = A
    · subst hCA
      rw [List.erase_cons_head, List.count_cons]
      by_cases hCB : C = B <;> simp [hCB]
    · rw [List.erase_cons_tail (by simpa using hCA), List.count_cons, List.count_cons, ih]
      by_cases hAB : A = B
      · subst hAB
        simp [hCA]
      · simp [hAB]

theorem Rep.erase {m : Counts} {l : List Form} (h : Rep m l) (A : Form) :
    Rep (dec A m) (l.erase A) := by
  intro B
  rw [cnt_dec, h B, count_erase]

theorem Rep.single (A : Form) (t : Nat) : Rep [(A, t, 1)] [A] := by
  intro B
  by_cases hAB : A = B <;> simp [cnt, hAB]

theorem Rep.has {m : Counts} {l : List Form} (h : Rep m l) (A : Form) :
    has A m = decide (A ∈ l) := by
  rw [has_eq, h A]
  exact decide_eq_decide.2 List.count_pos_iff

end Counts

/-- How often a formula occurs in `xbox Γ`: once for each `□B` of `Γ`,
and, if it is boxed, once for each occurrence of it in `Γ`. -/
theorem count_xbox (B : Form) (Γ : List Form) :
    (xbox Γ).count B = Γ.count (□B) + if B.boxed then Γ.count B else 0 := by
  induction Γ with
  | nil => simp [xbox]
  | cons C Γ ih =>
    have e : xbox (C :: Γ) = C.xb ++ xbox Γ := by simp [xbox]
    rw [e, List.count_append, ih]
    cases C with
    | var n => cases B <;> simp [Form.xb, Form.boxed]
    | bot => cases B <;> simp [Form.xb, Form.boxed]
    | imp C₁ C₂ => cases B <;> simp [Form.xb, Form.boxed]
    | box D =>
      by_cases h₁ : D = B <;> by_cases h₂ : □D = B <;>
        cases B <;> simp_all [Form.xb, Form.boxed, List.count_cons] <;> omega

namespace Counts

theorem Rep.xbox {m : Counts} {l : List Form} (h : Rep m l) : Rep (Counts.xbox m) (GLS.xbox l) := by
  intro B
  rw [cnt_xbox, count_xbox, h, h]

end Counts

/-- **The counts of a sequent.** -/
def CSeq.Rep (j : CSeq) (s : Seq) : Prop := Counts.Rep j.ant s.ant ∧ Counts.Rep j.suc s.suc

theorem CSeq.Rep.of (s : Seq) : (CSeq.of s).Rep s := ⟨.of _, .of _⟩

/-- The counts of the sequents of a list, one for one. -/
inductive CSeq.RepL : List CSeq → List Seq → Prop where
  | nil : CSeq.RepL [] []
  | cons {j : CSeq} {s : Seq} {js : List CSeq} {ss : List Seq} (h : j.Rep s)
      (hs : CSeq.RepL js ss) : CSeq.RepL (j :: js) (s :: ss)

/-- **One step by counts is one step**: at the counts of a sequent,
`countStep` applies where the move does, and its premises are the counts
of the move's premises. -/
theorem countStep_rep {j : CSeq} {s : Seq} (h : j.Rep s) (m : Move) :
    if (m.rule s).ok then
      ∃ qs, countStep m j = some qs ∧ CSeq.RepL qs (m.rule s).prems
    else countStep m j = none := by
  obtain ⟨ha, hs⟩ := h
  cases m with
  | idP p =>
    simp only [Move.rule, countStep, ha.has, hs.has]
    split
    · exact ⟨_, rfl, .nil⟩
    · rfl
  | botL =>
    simp only [Move.rule, countStep, ha.has]
    split
    · exact ⟨_, rfl, .nil⟩
    · rfl
  | impR A B =>
    simp only [Move.rule, countStep, hs.has]
    split
    · exact ⟨_, rfl, .cons ⟨ha.cons A _, (hs.erase _).cons B _⟩ .nil⟩
    · rfl
  | impL A B =>
    simp only [Move.rule, countStep, ha.has]
    split
    · exact ⟨_, rfl, .cons ⟨ha.erase _, hs.cons A _⟩ (.cons ⟨(ha.erase _).cons B _, hs⟩ .nil)⟩
    · rfl
  | glr A =>
    simp only [Move.rule, countStep, hs.has]
    split
    · exact ⟨_, rfl, .cons ⟨ha.xbox.snoc _ _, .single A _⟩ .nil⟩
    · rfl

mutual
  /-- The replay by counts, at the counts of a sequent, is the replay. -/
  theorem countCheck_rep : (c : Cert S) → (j : CSeq) → (s : Seq) → j.Rep s →
      countCheck j c = Cert.check s c
    | .node m cs, j, s, h => by
      have hs := countStep_rep h m
      by_cases hok : (m.rule s).ok = true
      · rw [if_pos hok] at hs
        obtain ⟨qs, hq, hrel⟩ := hs
        rw [countCheck, hq, Cert.check_node (step_of hok)]
        exact countCheckL_rep cs qs _ hrel
      · rw [if_neg hok] at hs
        have he : S.step m s = .error (m.rule s).why := by
          show step m s = _
          simp [step, hok]
        rw [countCheck, hs]
        exact (Bool.eq_false_iff.2 (Cert.not_check_of_error he)).symm
  /-- `countCheck_rep` on a list. -/
  theorem countCheckL_rep : (cs : List (Unit × Cert S)) → (qs : List CSeq) → (ps : List Seq) →
      CSeq.RepL qs ps → countCheckL qs cs = Cert.checkL ps cs
    | [], [], [], _ => by simp [countCheckL, Cert.checkL]
    | [], _ :: _, _ :: _, _ => by simp [countCheckL, Cert.checkL]
    | _ :: _, [], [], _ => by simp [countCheckL, Cert.checkL]
    | (_, c) :: cs, q :: qs, p :: ps, h => by
      cases h with
      | cons h₁ h₂ =>
        rw [countCheckL, Cert.checkL, countCheck_rep c q p h₁, countCheckL_rep cs qs ps h₂]
    | _, [], _ :: _, h => nomatch h
    | _, _ :: _, [], h => nomatch h
end

/-- **S27.  The replay by counts is the replay**: the two checks of a tree
of moves are one function. -/
theorem countCheck_eq (s : Seq) (c : Cert S) : s.countCheck c = Cert.check s c :=
  countCheck_rep c _ s (.of s)

end GLS

#axioms_within_file [propext, Quot.sound]
