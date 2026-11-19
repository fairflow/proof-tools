/-
The example calculus of the tests of `ProofTools.Explore`: a sequent
calculus for intuitionistic propositional logic, in the style of G3ip
(Troelstra and Schwichtenberg, *Basic Proof Theory*, 2nd ed., §3.5), small
enough to read in one screen.

    Γ ⊢ C         a list of hypotheses, read as a set, and a conclusion

| move | applies when | premises |
|---|---|---|
| `ax` | `C ∈ Γ` | none |
| `botL` | `⊥ ∈ Γ` | none |
| `impR` | `C = A ⟶ B` | `A, Γ ⊢ B` |
| `impL A B` | `A ⟶ B ∈ Γ` | `Γ ⊢ A` and `B, Γ ⊢ C` |
| `andR` | `C = A ⋏ B` | `Γ ⊢ A` and `Γ ⊢ B` |
| `andL A B` | `A ⋏ B ∈ Γ` | `A, B, Γ ⊢ C` |
| `orR1`, `orR2` | `C = A ⋎ B` | `Γ ⊢ A`, or `Γ ⊢ B` |
| `orL A B` | `A ⋎ B ∈ Γ` | `A, Γ ⊢ C` and `B, Γ ⊢ C` |

Differences from the book's G3ip, on purpose: `ax` is for any formula, not
atoms only, and a rule adds hypotheses and removes none.

What holds (`Valid`) is taken to be truth under every classical valuation.
The moves are sound for it (`sound`, PROVED), and a valuation that makes the
hypotheses true and the conclusion false refutes a sequent (`evaluator`).
The calculus is intuitionistic, so it is not complete for `Valid`: Peirce's
law holds and has no derivation.  That makes it an instance at level 2 of
`ProofTools.Explore.Certify`: both checkers, and a producer that may answer
`flag`.
-/
import ProofTools.Explore

namespace ProofToolsTest.Explore

open ProofTools.Explore

/-- Formulas. -/
inductive Form where
  | atom (n : Nat)
  | bot
  | imp (a b : Form)
  | and (a b : Form)
  | or (a b : Form)
  deriving DecidableEq, Repr, Lean.ToExpr

scoped infixr:60 " ⟶ " => Form.imp
scoped infixr:70 " ⋏ " => Form.and
scoped infixr:65 " ⋎ " => Form.or
scoped notation "⊥'" => Form.bot

/-- Sequents: hypotheses and a conclusion. -/
structure Seq where
  hyps : List Form
  concl : Form
  deriving DecidableEq, Repr, Lean.ToExpr

scoped infix:50 " ⊢ " => Seq.mk

/-- The moves. -/
inductive Move where
  | ax
  | botL
  | impR
  | impL (a b : Form)
  | andR
  | andL (a b : Form)
  | orR1
  | orR2
  | orL (a b : Form)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- The premises of a move at a sequent, or why it does not apply. -/
def step : Move → Seq → Except String (List Seq)
  | .ax, ⟨Γ, C⟩ =>
    if C ∈ Γ then .ok [] else .error "the conclusion is not among the hypotheses"
  | .botL, ⟨Γ, _⟩ => if Form.bot ∈ Γ then .ok [] else .error "⊥ is not among the hypotheses"
  | .impR, ⟨Γ, .imp a b⟩ => .ok [⟨a :: Γ, b⟩]
  | .impR, _ => .error "the conclusion is not an implication"
  | .impL a b, ⟨Γ, C⟩ =>
    if Form.imp a b ∈ Γ then .ok [⟨Γ, a⟩, ⟨b :: Γ, C⟩]
    else .error "the implication is not among the hypotheses"
  | .andR, ⟨Γ, .and a b⟩ => .ok [⟨Γ, a⟩, ⟨Γ, b⟩]
  | .andR, _ => .error "the conclusion is not a conjunction"
  | .andL a b, ⟨Γ, C⟩ =>
    if Form.and a b ∈ Γ then .ok [⟨a :: b :: Γ, C⟩]
    else .error "the conjunction is not among the hypotheses"
  | .orR1, ⟨Γ, .or a _⟩ => .ok [⟨Γ, a⟩]
  | .orR1, _ => .error "the conclusion is not a disjunction"
  | .orR2, ⟨Γ, .or _ b⟩ => .ok [⟨Γ, b⟩]
  | .orR2, _ => .error "the conclusion is not a disjunction"
  | .orL a b, ⟨Γ, C⟩ =>
    if Form.or a b ∈ Γ then .ok [⟨a :: Γ, C⟩, ⟨b :: Γ, C⟩]
    else .error "the disjunction is not among the hypotheses"

/-- **The example calculus**, as a proof system.  An `abbrev`, so that
`IPC.Judg` unfolds to `Seq` where Lean looks for instances. -/
abbrev IPC : ProofSystem where
  Judg := Seq
  Move := Move
  step := step

/-! ## What holds, and the two checkers -/

/-- Truth under a valuation of the atoms. -/
def Form.eval (v : Nat → Bool) : Form → Bool
  | .atom n => v n
  | .bot => false
  | .imp a b => !a.eval v || b.eval v
  | .and a b => a.eval v && b.eval v
  | .or a b => a.eval v || b.eval v

/-- **A sequent holds** if every valuation that makes its hypotheses true
makes its conclusion true. -/
def Valid (s : Seq) : Prop :=
  ∀ v : Nat → Bool, (∀ a ∈ s.hyps, a.eval v = true) → s.concl.eval v = true

/-- **The moves are sound.** -/
theorem sound : IPC.Sound Valid := by
  intro m ⟨Γ, C⟩ ps hstep hps v hv
  have prem : ∀ p ∈ ps, (∀ a ∈ p.hyps, a.eval v = true) → p.concl.eval v = true :=
    fun p hp => hps p hp v
  cases m with
  | ax =>
    simp only [step] at hstep
    split at hstep
    · next hmem => exact hv C hmem
    · cases hstep
  | botL =>
    simp only [step] at hstep
    split at hstep
    · next hmem => exact absurd (hv _ hmem) (by simp [Form.eval])
    · cases hstep
  | impR =>
    cases C with
    | imp a b =>
      simp only [step, Except.ok.injEq] at hstep
      subst hstep
      have h := prem ⟨a :: Γ, b⟩ (by simp)
      simp only [Form.eval, Bool.or_eq_true, Bool.not_eq_true']
      cases ha : a.eval v with
      | false => exact Or.inl rfl
      | true =>
        refine Or.inr (h ?_)
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hv x hx
    | atom _ | bot | and _ _ | or _ _ => simp [step] at hstep
  | impL a b =>
    simp only [step] at hstep
    split at hstep
    · next hmem =>
      simp only [Except.ok.injEq] at hstep
      subst hstep
      have h₁ := prem ⟨Γ, a⟩ (by simp) hv
      have hab := hv _ hmem
      simp only [Form.eval, Bool.or_eq_true, Bool.not_eq_true'] at hab h₁
      have hb : b.eval v = true := by
        rcases hab with hab | hab
        · rw [h₁] at hab
          cases hab
        · exact hab
      refine prem ⟨b :: Γ, C⟩ (by simp) ?_
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb
      · exact hv x hx
    · cases hstep
  | andR =>
    cases C with
    | and a b =>
      simp only [step, Except.ok.injEq] at hstep
      subst hstep
      have h₁ := prem ⟨Γ, a⟩ (by simp) hv
      have h₂ := prem ⟨Γ, b⟩ (by simp) hv
      simp only [Form.eval, Bool.and_eq_true]
      exact ⟨h₁, h₂⟩
    | atom _ | bot | imp _ _ | or _ _ => simp [step] at hstep
  | andL a b =>
    simp only [step] at hstep
    split at hstep
    · next hmem =>
      simp only [Except.ok.injEq] at hstep
      subst hstep
      have hab := hv _ hmem
      simp only [Form.eval, Bool.and_eq_true] at hab
      refine prem ⟨a :: b :: Γ, C⟩ (by simp) ?_
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab.1
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hab.2
        · exact hv x hx
    · cases hstep
  | orR1 =>
    cases C with
    | or a b =>
      simp only [step, Except.ok.injEq] at hstep
      subst hstep
      have h₁ := prem ⟨Γ, a⟩ (by simp) hv
      simp only [Form.eval, Bool.or_eq_true]
      exact Or.inl h₁
    | atom _ | bot | imp _ _ | and _ _ => simp [step] at hstep
  | orR2 =>
    cases C with
    | or a b =>
      simp only [step, Except.ok.injEq] at hstep
      subst hstep
      have h₁ := prem ⟨Γ, b⟩ (by simp) hv
      simp only [Form.eval, Bool.or_eq_true]
      exact Or.inr h₁
    | atom _ | bot | imp _ _ | and _ _ => simp [step] at hstep
  | orL a b =>
    simp only [step] at hstep
    split at hstep
    · next hmem =>
      simp only [Except.ok.injEq] at hstep
      subst hstep
      have hab := hv _ hmem
      simp only [Form.eval, Bool.or_eq_true] at hab
      rcases hab with ha | hb
      · refine prem ⟨a :: Γ, C⟩ (by simp) ?_
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hv x hx
      · refine prem ⟨b :: Γ, C⟩ (by simp) ?_
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hb
        · exact hv x hx
    · cases hstep

/-- A valuation, as the list of the atoms it makes true. -/
def valOf (M : List Nat) : Nat → Bool := fun n => M.contains n

/-- **The second checker**: a valuation that makes the hypotheses true and
the conclusion false. -/
def evaluator : Evaluator IPC Valid where
  Model := List Nat
  refutes M s := s.hyps.all (·.eval (valOf M)) && !s.concl.eval (valOf M)
  sound M s h hs := by
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    have := hs (valOf M) h.1
    rw [h.2] at this
    cases this

/-! ## For the editor -/

/-- A formula as text. -/
def Form.show : Form → String
  | .atom n => s!"p{n}"
  | .bot => "⊥"
  | .imp a b => s!"({a.show} → {b.show})"
  | .and a b => s!"({a.show} ∧ {b.show})"
  | .or a b => s!"({a.show} ∨ {b.show})"

/-- A sequent as text. -/
def Seq.show (s : Seq) : String :=
  ", ".intercalate (s.hyps.map Form.show) ++ " ⊢ " ++ s.concl.show

/-- A move as text. -/
def Move.show : Move → String
  | .ax => "ax"
  | .botL => "botL"
  | .impR => "impR"
  | .impL a b => s!"impL {a.show} {b.show}"
  | .andR => "andR"
  | .andL a b => s!"andL {a.show} {b.show}"
  | .orR1 => "orR1"
  | .orR2 => "orR2"
  | .orL a b => s!"orL {a.show} {b.show}"

/-- The moves to try at a sequent: those on the conclusion, and one for each
hypothesis that a left rule takes. -/
def candidates (s : Seq) : List Move :=
  [.ax, .botL, .impR, .andR] ++
    s.hyps.filterMap (fun
      | .and a b => some (.andL a b)
      | .or a b => some (.orL a b)
      | _ => none) ++
    s.hyps.filterMap (fun
      | .imp a b => some (.impL a b)
      | _ => none) ++
    [.orR1, .orR2]

/-- A premise adds nothing if it has the conclusion's conclusion and no new
hypothesis. -/
def within (p j : Seq) : Bool := p.concl == j.concl && p.hyps.all (· ∈ j.hyps)

instance : Explorable IPC where
  candidates := candidates
  showJudg := Seq.show
  showMove := Move.show
  quoteJudg := inferInstanceAs (Lean.ToExpr Seq)
  quoteMove := inferInstanceAs (Lean.ToExpr Move)
  within := within

/-! ## A producer, written with the combinators

Not trusted, and not complete: it takes the first candidate that applies
and adds something, and never goes back on a choice. -/

/-- One move: the first candidate that applies and adds something. -/
def firstMove : Tac IPC := fun s =>
  Tac.first ((candidates s).filter (fun m =>
    match step m s with
    | .ok ps => !ps.any (within · s)
    | .error _ => false) |>.map Tac.move) s

/-- `firstMove` at every goal it leaves, at most `n` deep. -/
def auto (n : Nat) : Tac IPC := Tac.iterate n firstMove

/-- Every script `auto` gives runs without a failing line: it is built with
`iterate`. -/
theorem auto_valid (n : Nat) : (auto n).Valid := Tac.valid_iterate firstMove n

/-- The atoms of a formula. -/
def Form.atoms : Form → List Nat
  | .atom n => [n]
  | .bot => []
  | .imp a b | .and a b | .or a b => a.atoms ++ b.atoms

/-- The sublists of a list. -/
def sublists : List Nat → List (List Nat)
  | [] => [[]]
  | a :: as => (sublists as) ++ (sublists as).map (a :: ·)

/-- **The producer**: a script from `auto`, or a valuation that refutes the
sequent, or `flag`. -/
def produce (s : Seq) (n : Nat) : Certify.Verdict (Script IPC) (List Nat) :=
  match (auto n s).filter (derives IPC s) with
  | some ls => .pass ls
  | none =>
    match (sublists (s.hyps.flatMap Form.atoms ++ s.concl.atoms).eraseDups).find?
        (evaluator.refutes · s) with
    | some M => .fail M
    | none => .flag

/-- **Both checkers and the producer, as one engine.** -/
def ipcEngine : Certify.Engine Seq (Script IPC) (List Nat) Valid := engine sound evaluator produce

end ProofToolsTest.Explore
