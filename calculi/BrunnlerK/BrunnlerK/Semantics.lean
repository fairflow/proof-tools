/-
Models, truth, the corresponding formula of a sequent, validity; finite
trees as models; and the statements of the goals that are about them.

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1: "the
corresponding formula", p. 7; Definition 2.6 (frames, models, validity),
p. 12; Theorem 2.9 (soundness), p. 13; Theorem 2.23 (completeness),
p. 17; Theorem 2.35 (cut elimination), p. 27.  Theory file: it ends with
its bound on axioms.

The statements at the end of the file are propositions and types with no
proof here.  Each is OPEN until a theorem of that type is in a theory
file (`campaign/statements.md`).
-/
import BrunnlerK.System

namespace BrunnlerK

/-! ## Models and truth (Definition 2.6) -/

/-- **A model** `(S, →, V)` (Definition 2.6): a set of states, a binary
relation on it, and a valuation, "a mapping which assigns a subset of `S`
to each proposition".  A set of states is a type, and a subset of it a
predicate.

The source asks that `S` is nonempty.  That is not asked here: `Valid`
speaks of every state of a model, so a model with no state changes
nothing. -/
structure Model where
  /-- The states, the source's `S`. -/
  W : Type
  /-- The relation of the frame, the source's `→`. -/
  R : W → W → Prop
  /-- The valuation: `V p s` says that the state `s` is in `V(p)`. -/
  V : Nat → W → Prop

/-- **Truth of a formula at a state**, `s ⊨ A` (Definition 2.6), clause by
clause as the source has it: "`s ⊨ p` iff `s ∈ V(p)`, `s ⊨ p̄` iff
`s ∉ V(p)`, `s ⊨ A ∨ B` iff `s ⊨ A` or `s ⊨ B`, `s ⊨ A ∧ B` iff `s ⊨ A` and
`s ⊨ B`, `s ⊨ ◇A` iff there is a state `t` such that `s → t` and `t ⊨ A`,
and `s ⊨ □A` iff for all `t` if `s → t` then `t ⊨ A`."  The words "or",
"not", "there is" are Lean's `∨`, `¬`, `∃`. -/
def Model.sat (M : Model) : M.W → Form → Prop
  | s, .atom p => M.V p s
  | s, .natom p => ¬ M.V p s
  | s, .or A B => M.sat s A ∨ M.sat s B
  | s, .and A B => M.sat s A ∧ M.sat s B
  | s, .dia A => ∃ t, M.R s t ∧ M.sat t A
  | s, .box A => ∀ t, M.R s t → M.sat t A

/-- **A two-valued model**: every formula is true or not true at every
state.  Not in the source, whose metatheory is classical: there every
model is two-valued.  (The plan, "What valid will mean in Lean".) -/
def Model.TwoValued (M : Model) : Prop :=
  ∀ (A : Form) (s : M.W), M.sat s A ∨ ¬ M.sat s A

/-! ## The corresponding formula of a sequent (p. 7) -/

/-- `⊥`, "defined as `p ∧ p̄` … for some proposition `p`" (p. 6).  The
proposition is the one numbered 0. -/
def Form.bot : Form := .atom 0 ⋏ .natom 0

/-- The disjunction `A₁ ∨ … ∨ Aₖ` of a list of formulas, bracketed to the
left as the source's binary connectives are; `⊥` for the empty list. -/
def Form.disj : List Form → Form
  | [] => Form.bot
  | A :: As => As.foldl (· ⋎ ·) A

/-- The formulas `□(Δ₁)_F, …, □(Δₙ)_F` of the boxes of a sequent. -/
def NSeq.boxForms : NSeq → List Form
  | .leaf _ => []
  | .cons Δ r => □(Form.disj (Δ.forms ++ Δ.boxForms)) :: r.boxForms

/-- **The corresponding formula `Γ_F` of a sequent** (p. 7): "the
corresponding formula of a sequent as given above is `⊥` if `m = n = 0`
and otherwise it is

    A₁ ∨ … ∨ Aₘ ∨ □(Δ₁)_F ∨ … ∨ □(Δₙ)_F ".

The source lists formulas and boxes "according to the fixed orders"; here
they are in the order the sequent has them. -/
def NSeq.form (Γ : NSeq) : Form := Form.disj (Γ.forms ++ Γ.boxForms)

/-- **A valid sequent**: its corresponding formula is true at every state
of every two-valued model.  The source's "valid" (Definition 2.6, with
"a model of a sequent is a model of its corresponding formula", p. 7) is
this with "every model"; the two agree under excluded middle. -/
def Valid (Γ : NSeq) : Prop :=
  ∀ M : Model, M.TwoValued → ∀ s : M.W, M.sat s Γ.form

/-! ## Finite trees as models -/

/-- **A finite tree, as data**: at each node the propositions that are
true there, and the node's children. -/
inductive Tree where
  | node (val : List Nat) (kids : List Tree)
  deriving Repr

/-- The propositions true at the root of a tree. -/
def Tree.val : Tree → List Nat
  | .node v _ => v

/-- The children of the root of a tree. -/
def Tree.kids : Tree → List Tree
  | .node _ ks => ks

/-- **The model of finite trees.**  A state is a finite tree; `t → u` if
`u` is a child of the root of `t`; a proposition is true at `t` if it is
in the list at the root of `t`.  The states that can be reached from a
tree `t` are the subtrees of `t`, which are finitely many; the model
itself has every finite tree as a state. -/
def treeModel : Model where
  W := Tree
  R t u := u ∈ t.kids
  V p t := p ∈ t.val

/-- Truth at the root of a tree, computed.  (To be proved: it is truth in
`treeModel`.) -/
def Form.holds : Form → Tree → Bool
  | .atom p, t => t.val.contains p
  | .natom p, t => !t.val.contains p
  | .or A B, t => A.holds t || B.holds t
  | .and A B, t => A.holds t && B.holds t
  | .dia A, t => t.kids.any (fun u => A.holds u)
  | .box A, t => t.kids.all (fun u => A.holds u)

/-- **A refutation of a sequent**: a finite tree, as data, at whose root
the corresponding formula of the sequent is not true. -/
structure Refutation (Γ : NSeq) where
  /-- The tree. -/
  tree : Tree
  /-- `Γ_F` is not true at its root. -/
  refutes : ¬ treeModel.sat tree Γ.form

/-! ## The statements

Each is a proposition or a type, with no proof in this file. -/

/-- **Goal 1, soundness** (Theorem 2.9 (i), (iii), at `X = ∅`):
`K ⊢ Γ → Valid Γ`. -/
def Soundness : Prop := ∀ Γ : NSeq, K Γ → Valid Γ

/-- Soundness of K with `cut`: `K + cut ⊢ Γ → Valid Γ`.  Not stated in
the source.  It is what cut elimination by the short route rests on. -/
def SoundnessCut : Prop := ∀ Γ : NSeq, Kcut Γ → Valid Γ

/-- The model of finite trees is two-valued. -/
def TreeModelTwoValued : Prop := treeModel.TwoValued

/-- **Goal 8, a proof or a countermodel** (Theorem 2.23, at `X = ∅`): a
function that gives, for every sequent, a proof in system K or a
refutation.  A type: what has this type is the function. -/
abbrev ProofOrRefutation : Type := (Γ : NSeq) → K Γ ⊕ Refutation Γ

/-- **Goal 9, completeness** (Theorem 2.23 (i), at `X = ∅`):
`Valid Γ → K ⊢ Γ`. -/
def Completeness : Prop := ∀ Γ : NSeq, Valid Γ → Nonempty (K Γ)

/-- **Goal 9, decidability** (Corollary 2.25, at `X = ∅`): a function that
decides, for every sequent, whether it is valid. -/
abbrev ValidDecidable : Type := (Γ : NSeq) → Decidable (Valid Γ)

/-- **Goal 10, cut elimination** (Theorem 2.35, at `X = ∅`), in the form
"`cut` is admissible": `K + cut ⊢ Γ → K ⊢ Γ`. -/
def CutElimination : Prop := ∀ Γ : NSeq, Kcut Γ → Nonempty (K Γ)

end BrunnlerK

#axioms_within_file [propext, Quot.sound]
