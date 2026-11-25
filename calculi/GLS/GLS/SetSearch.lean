/-
A certifier and a search over sets.

The premise of GLR holds `B, □B` for every boxed formula of the
antecedent, with repetitions, so the sequents of a derivation in GLS can
double from one GLR to the next (`campaign/measurements.md`).  For the
proposition "there is a derivation in GLS" that size is not needed: a
sequent less its repeated formulas is derivable only if the sequent is
(weakening).  Here: the proof system `SS`, whose `step` is that of GLS
with the repeated formulas of each premise removed; that its moves are
sound for derivability in GLS; a search over it, which is not proved; and
a decision of derivability that runs that search and checks its answer.

Theory file: it ends with its bound on axioms.
-/
import GLS.Run
import GLS.Structural

namespace GLS

open ProofTools ProofTools.Explore

/-! ## Removing repeated formulas -/

/-- `A` put before a list, unless it is there already. -/
def insertNew (A : Form) (Γ : List Form) : List Form := if A ∈ Γ then Γ else A :: Γ

/-- A list less its repeated formulas: of several occurrences the last is
kept.  (Written through `insertNew` so that the recursive call is made
once: with the `if` written out in place, the compiled function made it
twice, and its time doubled with each formula of the list.  Found by the
measurements, `campaign/measurements.md`.) -/
def dedup : List Form → List Form
  | [] => []
  | A :: Γ => insertNew A (dedup Γ)

/-- The occurrences that `dedup` removes. -/
def dropped : List Form → List Form
  | [] => []
  | A :: Γ => if A ∈ dedup Γ then A :: dropped Γ else dropped Γ

theorem mem_dedup {A : Form} {Γ : List Form} : A ∈ dedup Γ ↔ A ∈ Γ := by
  induction Γ with
  | nil => simp [dedup]
  | cons C Γ ih =>
    by_cases hC : C ∈ dedup Γ
    · simp only [dedup, insertNew, hC, if_true, List.mem_cons, ih]
      constructor
      · exact .inr
      · rintro (rfl | h)
        · exact ih.1 hC
        · exact h
    · simp only [dedup, insertNew, hC, if_false, List.mem_cons, ih]

theorem dedup_perm (Γ : List Form) : Γ.Perm (dedup Γ ++ dropped Γ) := by
  induction Γ with
  | nil => exact List.Perm.refl _
  | cons C Γ ih =>
    by_cases hC : C ∈ dedup Γ
    · simp only [dedup, insertNew, dropped, hC, if_true]
      exact (ih.cons C).trans List.perm_middle.symm
    · simp only [dedup, insertNew, dropped, hC, if_false, List.cons_append]
      exact ih.cons C

/-- A sequent less its repeated formulas, on each side. -/
def Seq.dedup (s : Seq) : Seq := GLS.dedup s.ant ⇒ GLS.dedup s.suc

/-- **A sequent is derivable if it is so less its repeated formulas**:
weakening. -/
theorem derivable_of_dedup {s : Seq} (h : Derivable s.dedup) : Derivable s :=
  let ⟨d⟩ := h
  ⟨(d.wk (dropped s.ant) (dropped s.suc) s.ant s.suc (dedup_perm _) (dedup_perm _)).1⟩

/-! ## The proof system over sets, and its certifier -/

/-- One step over sets: the step of GLS, with the repeated formulas of
each premise removed. -/
def stepSet (m : Move) (j : Seq) : Except String (List Seq) :=
  if (m.rule j).ok then .ok ((m.rule j).prems.map Seq.dedup) else .error (m.rule j).why

/-- **GLS over sets, as a proof system**: the moves of GLS, the step
`stepSet`. -/
abbrev SS : ProofSystem where
  Judg := Seq
  Move := Move
  step := stepSet

/-- **The moves over sets are sound for derivability in GLS.** -/
theorem stepSet_sound : SS.Sound Derivable := by
  intro m j ps h hps
  have h' : stepSet m j = .ok ps := h
  unfold stepSet at h'
  split at h'
  · next hok =>
    have e : ps = (m.rule j).prems.map Seq.dedup := (Except.ok.inj h').symm
    apply step_sound_derivable m j (m.rule j).prems (step_of hok)
    intro q hq
    exact derivable_of_dedup (hps _ (e ▸ List.mem_map_of_mem hq))
  · cases h'

/-- **Trees of moves over sets, checked**: a tree that `Cert.check`
accepts for `s` in `SS` shows that `s` is derivable in GLS. -/
def setCert : Certify.Certifier Seq (Cert SS) Derivable := Cert.certifier stepSet_sound.soundT

#certify_structural GLS.setCert
#certify_statement GLS.setCert

/-! ## A search over sets (not proved: its answers are checked) -/

/-- The tree of moves of the identity on a formula. -/
def idCert : Form → Cert SS
  | .var p => .mk (.idP p) []
  | ⊥ => .mk .botL []
  | A ⟶ B => .mk (.impR A B) [.mk (.impL A B) [idCert A, idCert B]]
  | □A => .mk (.glr A) [idCert A]

/-- GLR on each boxed formula of a list, over sets: a tree of moves as
soon as one premise has one; the refuting trees, if every premise is
refuted. -/
def tryBoxesSet (rec : Seq → Option (Cert SS ⊕ Tree)) (Γ : List Form) :
    List Form → Option (Cert SS ⊕ List Tree)
  | [] => some (.inr [])
  | A :: bs =>
    match rec (xbox Γ ++ [□A] ⇒ [A]).dedup with
    | none => none
    | some (.inl c) => some (.inl (.mk (.glr A) [c]))
    | some (.inr t) =>
      match tryBoxesSet rec Γ bs with
      | none => none
      | some (.inl c) => some (.inl c)
      | some (.inr ts) => some (.inr (t :: ts))

/-- **The search over sets**, with a number of steps allowed: the search
of `GLS/Search.lean`, each premise less its repeated formulas.  A tree of
moves for `setCert`, or a tree for `noDerivable`, or nothing. -/
def searchSet : Nat → Seq → Option (Cert SS ⊕ Tree)
  | 0, _ => none
  | n + 1, s =>
    match classify s with
    | .idP p _ _ => some (.inl (.mk (.idP p) []))
    | .botL _ => some (.inl (.mk .botL []))
    | .idB A _ _ => some (.inl (idCert (□A)))
    | .impR A B _ =>
      match searchSet n (A :: s.ant ⇒ B :: s.suc.erase (A ⟶ B)).dedup with
      | none => none
      | some (.inl c) => some (.inl (.mk (.impR A B) [c]))
      | some (.inr t) => some (.inr t)
    | .impL A B _ =>
      match searchSet n (s.ant.erase (A ⟶ B) ⇒ A :: s.suc).dedup with
      | none => none
      | some (.inr t) => some (.inr t)
      | some (.inl c₁) =>
        match searchSet n (B :: s.ant.erase (A ⟶ B) ⇒ s.suc).dedup with
        | none => none
        | some (.inr t) => some (.inr t)
        | some (.inl c₂) => some (.inl (.mk (.impL A B) [c₁, c₂]))
    | .prime _ _ _ _ _ =>
      match tryBoxesSet (searchSet n) s.ant (s.suc.filterMap Form.unbox?) with
      | none => none
      | some (.inl c) => some (.inl c)
      | some (.inr ts) => some (.inr (.node (s.ant.filterMap Form.var?) ts))

/-- The producer over sets: the search, at the steps of `fuel`. -/
def produceSet (s : Seq) : Option (Cert SS ⊕ Tree) := searchSet (fuel s) s

/-! ## A decision that runs the search over sets, and checks -/

/-- **Derivability in GLS is decidable, by the search over sets**: its
answer is checked, a tree of moves by `setCert` and a tree by
`noDerivable`; where a check fails or the search gives nothing, the
decision is that of `derivableDecidable`. -/
@[reducible] def derivableDecidableFast : DerivableDecidable := fun s =>
  match produceSet s with
  | some (.inl c) =>
    if h : setCert.check s c = true then isTrue (setCert.sound s c h) else derivableDecidable s
  | some (.inr t) =>
    if h : noDerivable.check s t = true then isFalse (noDerivable.sound s t h)
    else derivableDecidable s
  | none => derivableDecidable s

/-- **Validity is decidable, by the search over sets**, in the same way. -/
@[reducible] def validDecidableFast : ValidDecidable := fun s =>
  match produceSet s with
  | some (.inl c) =>
    if h : setCert.check s c = true then
      isTrue (let ⟨d⟩ := setCert.sound s c h; soundness s d)
    else validDecidable s
  | some (.inr t) =>
    if h : noValid.check s t = true then isFalse (noValid.sound s t h) else validDecidable s
  | none => validDecidable s

end GLS

#axioms_within_file [propext, Quot.sound]
