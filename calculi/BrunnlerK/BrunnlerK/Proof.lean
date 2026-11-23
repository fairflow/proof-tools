/-
System K as a proof system of proof-tools: the moves, one step, and the
soundness of the moves for the family `K` (S1 of
`campaign/statements.md`).

A move carries what its constructor in `Fam` carries.  `step` asks what the
constructor's side conditions ask, with the same functions
(`BrunnlerK/Sequent.lean`), and leaves the constructor's premises.  There is
no move for `cut`: the proof system is for system K, and `K` is `Fam false`.

Theory: the file ends with its bound on axioms.
-/
import ProofTools.Explore
import ProofTools.Audit
import BrunnlerK.System

namespace BrunnlerK

open ProofTools ProofTools.Explore

/-! ## Moves -/

/-- **A move**: a rule of Figure 2.3, with the path `a` of the node it acts
at and its main formula; for `◇k_c` also the position `i` of the box. -/
inductive Move where
  /-- The axiom `Γ{p, p̄}`, at the node at `a`. -/
  | ax (a : Path) (p : Nat)
  /-- The rule `∧` on `A ∧ B`, at the node at `a`. -/
  | and (a : Path) (A B : Form)
  /-- The rule `∨` on `A ∨ B`, at the node at `a`. -/
  | or (a : Path) (A B : Form)
  /-- The rule `□` on `□A`, at the node at `a`. -/
  | box (a : Path) (A : Form)
  /-- The rule `◇k_c` on `◇A`, at the node at `a`, into its box `i`. -/
  | dia (a : Path) (i : Nat) (A : Form)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- The path of the node a move acts at. -/
def Move.path : Move → Path
  | .ax a _ => a
  | .and a _ _ => a
  | .or a _ _ => a
  | .box a _ => a
  | .dia a _ _ => a

/-- What a move asks of a sequent, what it leaves, and what to say when it
does not apply. -/
structure Rule where
  ok : Bool
  prems : List NSeq
  why : String

/-- The rule `◇k_c`, given the node `Θ` at `a` and what is at position `i`
among its boxes. -/
def diaRule (Γ Θ : NSeq) (a : Path) (A : Form) (i : Nat) : Option NSeq → Rule
  | some Δ =>
    ⟨decide (◇A ∈ Θ.forms), [Γ.setNode a (Θ.setBox i (Δ.add A))],
      "the formula ◇A is not in the node"⟩
  | none => ⟨false, [], "the node has no box at this position"⟩

/-- **The rule of a move**, given the node `Θ` at its path in `Γ`. -/
def Move.ruleAt (Γ Θ : NSeq) : Move → Rule
  | .ax _ p =>
    ⟨decide (Form.atom p ∈ Θ.forms) && decide (Form.natom p ∈ Θ.forms), [],
      if Form.atom p ∈ Θ.forms then "the negated proposition is not in the node"
      else "the proposition is not in the node"⟩
  | .and a A B =>
    ⟨decide (A ⋏ B ∈ Θ.forms),
      [Γ.setNode a ((Θ.erase (A ⋏ B)).add A), Γ.setNode a ((Θ.erase (A ⋏ B)).add B)],
      "the conjunction is not in the node"⟩
  | .or a A B =>
    ⟨decide (A ⋎ B ∈ Θ.forms), [Γ.setNode a (((Θ.erase (A ⋎ B)).add B).add A)],
      "the disjunction is not in the node"⟩
  | .box a A =>
    ⟨decide (□A ∈ Θ.forms), [Γ.setNode a ((Θ.erase (□A)).addBox (.leaf [A]))],
      "the formula □A is not in the node"⟩
  | .dia a i A => diaRule Γ Θ a A i (Θ.box? i)

/-- **The rule of a move at a sequent.** -/
def Move.rule (Γ : NSeq) (m : Move) : Rule :=
  match Γ.node? m.path with
  | some Θ => m.ruleAt Γ Θ
  | none => ⟨false, [], "the sequent has no node at this path"⟩

/-- **One step**: the premises of the move at the sequent, or why it does
not apply. -/
def step (m : Move) (Γ : NSeq) : Except String (List NSeq) :=
  if (m.rule Γ).ok then .ok (m.rule Γ).prems else .error (m.rule Γ).why

/-- **System K as a proof system.**  An `abbrev`, so that `S.Judg` unfolds
to `NSeq` where Lean looks for instances. -/
abbrev S : ProofSystem where
  Judg := NSeq
  Move := Move
  step := step

theorem step_of {m : Move} {Γ : NSeq} (h : (m.rule Γ).ok = true) :
    S.step m Γ = .ok (m.rule Γ).prems := by
  show step m Γ = _
  simp [step, h]

theorem step_ok {m : Move} {Γ : NSeq} {ps : List NSeq} (h : S.step m Γ = .ok ps) :
    (m.rule Γ).ok = true ∧ ps = (m.rule Γ).prems := by
  have h' : step m Γ = .ok ps := h
  unfold step at h'
  split at h'
  · next hok => exact ⟨hok, (Except.ok.inj h').symm⟩
  · cases h'

theorem rule_some {m : Move} {Γ Θ : NSeq} (h : Γ.node? m.path = some Θ) :
    m.rule Γ = m.ruleAt Γ Θ := by
  simp [Move.rule, h]

theorem rule_none {m : Move} {Γ : NSeq} (h : Γ.node? m.path = none) :
    (m.rule Γ).ok = false := by
  simp [Move.rule, h]

/-! ## What holds: the family `K` -/

/-- The case of `◇k_c` in S1, by what is at position `i` among the boxes of
the node. -/
def diaSound {Γ Θ : NSeq} {a : Path} {A : Form} {i : Nat} (hΘ : Γ.node? a = some Θ) :
    (o : Option NSeq) → Θ.box? i = o → (diaRule Γ Θ a A i o).ok = true →
      Each K (diaRule Γ Θ a A i o).prems → K Γ
  | some _, hΔ, hok, e => .dia a i A hΘ (of_decide_eq_true hok) hΔ e.1
  | none, _, hok, _ => nomatch hok

/-- **S1.  The soundness of the moves**: each move that applies is a rule of
system K, applied to the derivations of its premises.  One case for each
move.  This is not the source's soundness theorem (goal 1). -/
def step_sound : S.SoundT K := fun m Γ _ h e =>
  match hΘ : Γ.node? m.path with
  | none => absurd (step_ok h).1 (by simp [rule_none hΘ])
  | some Θ =>
    have hok : (m.ruleAt Γ Θ).ok = true := rule_some hΘ ▸ (step_ok h).1
    let e' : Each K (m.ruleAt Γ Θ).prems := (rule_some hΘ ▸ (step_ok h).2) ▸ e
    match m, hΘ, hok, e' with
    | .ax a p, hΘ, hok, _ =>
      .ax a p hΘ (of_decide_eq_true (Bool.and_eq_true_iff.mp hok).1)
        (of_decide_eq_true (Bool.and_eq_true_iff.mp hok).2)
    | .and a A B, hΘ, hok, e' => .and a A B hΘ (of_decide_eq_true hok) e'.1 e'.2.1
    | .or a A B, hΘ, hok, e' => .or a A B hΘ (of_decide_eq_true hok) e'.1
    | .box a A, hΘ, hok, e' => .box a A hΘ (of_decide_eq_true hok) e'.1
    | .dia a i A, hΘ, hok, e' => diaSound hΘ (Θ.box? i) rfl hok e'

/-- **The map out**: a derivation of the proof system, as a derivation of
system K as the source states it. -/
def famOfDer {Γ : NSeq} (d : Der S Γ) : K Γ := Der.mapOut step_sound d

/-- That there is a derivation in system K. -/
def Derivable (Γ : NSeq) : Prop := Nonempty (K Γ)

theorem step_sound_derivable : S.Sound Derivable := step_sound.nonempty

/-- **S2**, as a proposition: every derivation of system K is one of the
proof system. -/
def FamToDer : Prop := ∀ Γ : NSeq, K Γ → Nonempty (Der S Γ)

/-- S2 for the family with its parameter: a derivation without `cut` is one
of the proof system.  A node for each constructor. -/
theorem der_of_fam {c : Bool} {Γ : NSeq} (d : Fam c Γ) (hc : c = false) :
    Nonempty (Der S Γ) := by
  induction d with
  | @ax Γ Θ a p hΘ hp hn =>
    have h : S.step (.ax a p) Γ = .ok [] := by
      show step _ _ = _
      simp [step, Move.rule, Move.path, hΘ, Move.ruleAt, hp, hn]
    exact ⟨.node (.ax a p) [] h .nil⟩
  | @and Γ Θ a A B hΘ hA _ _ ih₁ ih₂ =>
    let ⟨d₁⟩ := ih₁
    let ⟨d₂⟩ := ih₂
    have h : S.step (.and a A B) Γ = .ok [Γ.setNode a ((Θ.erase (A ⋏ B)).add A),
        Γ.setNode a ((Θ.erase (A ⋏ B)).add B)] := by
      show step _ _ = _
      simp [step, Move.rule, Move.path, hΘ, Move.ruleAt, hA]
    exact ⟨.node (.and a A B) _ h (.cons d₁ (.cons d₂ .nil))⟩
  | @or Γ Θ a A B hΘ hA _ ih =>
    let ⟨d⟩ := ih
    have h : S.step (.or a A B) Γ = .ok [Γ.setNode a (((Θ.erase (A ⋎ B)).add B).add A)] := by
      show step _ _ = _
      simp [step, Move.rule, Move.path, hΘ, Move.ruleAt, hA]
    exact ⟨.node (.or a A B) _ h (.cons d .nil)⟩
  | @box Γ Θ a A hΘ hA _ ih =>
    let ⟨d⟩ := ih
    have h : S.step (.box a A) Γ = .ok [Γ.setNode a ((Θ.erase (□A)).addBox (.leaf [A]))] := by
      show step _ _ = _
      simp [step, Move.rule, Move.path, hΘ, Move.ruleAt, hA]
    exact ⟨.node (.box a A) _ h (.cons d .nil)⟩
  | @dia Γ Θ Δ a i A hΘ hA hΔ _ ih =>
    let ⟨d⟩ := ih
    have h : S.step (.dia a i A) Γ = .ok [Γ.setNode a (Θ.setBox i (Δ.add A))] := by
      show step _ _ = _
      simp [step, Move.rule, Move.path, hΘ, Move.ruleAt, hΔ, diaRule, hA]
    exact ⟨.node (.dia a i A) _ h (.cons d .nil)⟩
  | cut _ _ hc' => exact absurd (hc ▸ hc') (by decide)

/-- **S2**: every derivation of system K is one of the proof system, so
`step` refuses no instance of a rule of system K. -/
theorem famToDer : FamToDer := fun _ d => der_of_fam d rfl

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
