/-
Models, truth and validity for GLS; finite trees as models; and the
statements of the goals, each a proposition or a type with no proof here.

**The semantics is not in the source's Coq files**, which have no models.
It is the usual one for the logic GL: a model is transitive and
conversely well-founded (`campaign/plan.md`, Q2, and
`campaign/decisions.md`, "what valid means").  Theory file: it ends with
its bound on axioms.

Each statement at the end of the file is OPEN until a theorem or a
definition of that type is in a theory file (`campaign/statements.md`).
-/
import GLS.System

namespace GLS

/-! ## Models and truth -/

/-- **A model**: a set of worlds, a relation on it, and a valuation.  A
set of worlds is a type, and a set of worlds a predicate: `V p w` says
that the variable numbered `p` is true at `w`. -/
structure Model where
  /-- The worlds. -/
  W : Type
  /-- The relation. -/
  R : W → W → Prop
  /-- The valuation. -/
  V : Nat → W → Prop

/-- **Truth of a formula at a world**, `w ⊩ A`: a variable by the
valuation; `⊥` never; `A → B` if truth of `A` implies truth of `B`; `□A`
if `A` is true at every world the relation leads to. -/
def Model.sat (M : Model) : M.W → Form → Prop
  | w, .var p => M.V p w
  | _, ⊥ => False
  | w, A ⟶ B => M.sat w A → M.sat w B
  | w, □A => ∀ v, M.R w v → M.sat v A

/-- **A model of GL**: the relation is transitive, and its converse is
well-founded (there is no infinite chain `w R w₁ R w₂ R …`). -/
structure Model.GL (M : Model) : Prop where
  /-- The relation is transitive. -/
  trans : ∀ x y z, M.R x y → M.R y z → M.R x z
  /-- The converse of the relation is well-founded. -/
  cwf : WellFounded (fun x y => M.R y x)

/-- **A two-valued model**: every formula is true or not true at every
world.  Under excluded middle every model is two-valued. -/
def Model.TwoValued (M : Model) : Prop :=
  ∀ (A : Form) (w : M.W), M.sat w A ∨ ¬ M.sat w A

/-- **A finite model**: its worlds can be listed. -/
def Model.Finite (M : Model) : Prop := ∃ l : List M.W, ∀ w : M.W, w ∈ l

/-- **Truth of a sequent at a world**: if every formula of the antecedent
is true there, then some formula of the succedent is. -/
def Model.satSeq (M : Model) (w : M.W) (s : Seq) : Prop :=
  (∀ A ∈ s.ant, M.sat w A) → ∃ B ∈ s.suc, M.sat w B

/-- **A valid sequent**: true at every world of every two-valued model of
GL.  It is validity in every model of GL, under excluded middle. -/
def Valid (s : Seq) : Prop :=
  ∀ M : Model, M.GL → M.TwoValued → ∀ w : M.W, M.satSeq w s

/-! ## Finite trees as models -/

/-- **A finite tree, as data**: at each node the variables that are true
there, and the node's children. -/
inductive Tree where
  | node (val : List Nat) (kids : List Tree)
  deriving Repr, Lean.ToExpr

/-- The variables true at the root of a tree. -/
def Tree.val : Tree → List Nat
  | .node v _ => v

/-- The children of the root of a tree. -/
def Tree.kids : Tree → List Tree
  | .node _ ks => ks

mutual
  /-- **The proper descendants of the root of a tree**: its children, and
  their proper descendants. -/
  def Tree.desc : Tree → List Tree
    | .node _ ks => Tree.descL ks
  /-- The trees of a list, each with its proper descendants. -/
  def Tree.descL : List Tree → List Tree
    | [] => []
    | t :: ts => t :: (t.desc ++ Tree.descL ts)
end

/-- **The model of finite trees.**  A world is a finite tree; `t R u` if
`u` is a proper descendant of the root of `t` (a subtree of `t` other
than `t`); a variable is true at `t` if it is in the list at the root of
`t`.  The worlds that can be reached from a tree are its subtrees,
finitely many; the model itself has every finite tree as a world. -/
def treeModel : Model where
  W := Tree
  R t u := u ∈ t.desc
  V p t := p ∈ t.val

/-- **The part of the model of finite trees below a tree**: the worlds are
`t` and its proper descendants, with the relation and the valuation of
`treeModel`. -/
def subModel (t : Tree) : Model where
  W := { u : Tree // u = t ∨ u ∈ t.desc }
  R u v := v.1 ∈ u.1.desc
  V p u := p ∈ u.1.val

/-- Truth at the root of a tree, computed. -/
def Form.holds : Form → Tree → Bool
  | .var p, t => t.val.contains p
  | ⊥, _ => false
  | A ⟶ B, t => !A.holds t || B.holds t
  | □A, t => t.desc.all (fun u => A.holds u)

/-- A sequent is false at the root of a tree, computed: every formula of
the antecedent holds there and none of the succedent. -/
def Seq.refutedAt (s : Seq) (t : Tree) : Bool :=
  s.ant.all (fun A => A.holds t) && s.suc.all (fun B => !B.holds t)

/-- **A refutation of a sequent**: a finite tree, as data, at whose root
the sequent is not true. -/
structure Refutation (s : Seq) where
  /-- The tree. -/
  tree : Tree
  /-- The sequent is not true at its root. -/
  refutes : ¬ treeModel.satSeq tree s

/-! ## The statements

Each is a proposition or a type, with no proof in this file. -/

/-- **Goal 1, soundness**: what GLS derives is valid. -/
def Soundness : Prop := ∀ s : Seq, Fam s → Valid s

/-- **Goal 2, completeness as data**: for every sequent, a derivation in
GLS or a refutation. -/
abbrev ProofOrRefutation : Type := (s : Seq) → Fam s ⊕ Refutation s

/-- **Goal 2, completeness**: what is valid is derivable in GLS. -/
def Completeness : Prop := ∀ s : Seq, Valid s → Nonempty (Fam s)

/-- **Goal 2, decidability** of validity. -/
abbrev ValidDecidable : Type := (s : Seq) → Decidable (Valid s)

/-- **Goal 2, decidability** of derivability in GLS. -/
abbrev DerivableDecidable : Type := (s : Seq) → Decidable (Nonempty (Fam s))

/-- **Goal 2, the finite model property**: a sequent that is true at every
world of every finite two-valued model of GL is valid. -/
def FiniteModelProperty : Prop :=
  ∀ s : Seq, (∀ M : Model, M.GL → M.TwoValued → M.Finite → ∀ w : M.W, M.satSeq w s) → Valid s

/-- **Goal 2, on the way: the identity on every formula** (the source's
`Id_all_form`). -/
abbrev Identity : Type :=
  (A : Form) → {Γ Δ : List Form} → A ∈ Γ → A ∈ Δ → Fam (Γ ⇒ Δ)

/-- `p` is a premise of an instance of a rule of PSGLS whose conclusion is
`c`. -/
inductive PSPrem (p c : Seq) : Prop where
  /-- The premise of ImpR. -/
  | impR (A B : Form) (h : A ⟶ B ∈ c.suc)
      (e : p = (A :: c.ant ⇒ B :: c.suc.erase (A ⟶ B)))
  /-- The first premise of ImpL. -/
  | impL₁ (A B : Form) (h : A ⟶ B ∈ c.ant)
      (e : p = (c.ant.erase (A ⟶ B) ⇒ A :: c.suc))
  /-- The second premise of ImpL. -/
  | impL₂ (A B : Form) (h : A ⟶ B ∈ c.ant)
      (e : p = (B :: c.ant.erase (A ⟶ B) ⇒ c.suc))
  /-- The premise of GLR, where the conclusion is no axiom of PSGLS. -/
  | glr (A : Form) (nP : ¬ c.IsIdP) (nB : ¬ c.IsIdB) (nBot : ¬ c.IsBotL) (h : □A ∈ c.suc)
      (e : p = (xbox c.ant ++ [□A] ⇒ [A]))

/-- **Goal 2, on the way: the termination of proof search in PSGLS**:
there is no infinite sequence of sequents, each a premise of an instance
of a rule of PSGLS with the one before as conclusion. -/
def PSTermination : Prop := WellFounded PSPrem

/-- **Goal 3, cut admissibility** (the source's `GLS_cut_adm`): the
additive cut, with the cut formula at any place. -/
abbrev CutAdmissible : Type :=
  (A : Form) → (Γ0 Γ1 Δ0 Δ1 : List Form) →
    Fam (Γ0 ++ Γ1 ⇒ Δ0 ++ A :: Δ1) → Fam (Γ0 ++ A :: Γ1 ⇒ Δ0 ++ Δ1) →
    Fam (Γ0 ++ Γ1 ⇒ Δ0 ++ Δ1)

/-- **Goal 4, exchange**, with heights: a derivation of a sequent gives one
no higher of the sequent with its two lists permuted. -/
abbrev Exchange : Type :=
  {Γ Δ Γ' Δ' : List Form} → (d : Fam (Γ ⇒ Δ)) → Γ.Perm Γ' → Δ.Perm Δ' →
    { d' : Fam (Γ' ⇒ Δ') // d'.height ≤ d.height }

/-- **Goal 4, weakening on the left**, with heights (the source's
`GLS_wkn_L`). -/
abbrev WeakeningL : Type :=
  (A : Form) → {Γ0 Γ1 Δ : List Form} → (d : Fam (Γ0 ++ Γ1 ⇒ Δ)) →
    { d' : Fam (Γ0 ++ A :: Γ1 ⇒ Δ) // d'.height ≤ d.height }

/-- **Goal 4, weakening on the right**, with heights (`GLS_wkn_R`). -/
abbrev WeakeningR : Type :=
  (A : Form) → {Γ Δ0 Δ1 : List Form} → (d : Fam (Γ ⇒ Δ0 ++ Δ1)) →
    { d' : Fam (Γ ⇒ Δ0 ++ A :: Δ1) // d'.height ≤ d.height }

/-- **Goal 4, the inversion of ImpR**, with heights (the source's
`ImpR_ImpL_hpinv`, first half). -/
abbrev InversionImpR : Type :=
  (A B : Form) → {Γ Δ : List Form} → (d : Fam (Γ ⇒ Δ)) → A ⟶ B ∈ Δ →
    { d' : Fam (A :: Γ ⇒ B :: Δ.erase (A ⟶ B)) // d'.height ≤ d.height }

/-- **Goal 4, the inversion of ImpL**, with heights (`ImpR_ImpL_hpinv`,
second half). -/
abbrev InversionImpL : Type :=
  (A B : Form) → {Γ Δ : List Form} → (d : Fam (Γ ⇒ Δ)) → A ⟶ B ∈ Γ →
    { d' : Fam (Γ.erase (A ⟶ B) ⇒ A :: Δ) // d'.height ≤ d.height } ×
    { d' : Fam (B :: Γ.erase (A ⟶ B) ⇒ Δ) // d'.height ≤ d.height }

/-- **Goal 4, contraction on the left**, with heights (the source's
`GLS_hpadm_ctr_L`). -/
abbrev ContractionL : Type :=
  (A : Form) → {Γ0 Γ1 Γ2 Δ : List Form} → (d : Fam (Γ0 ++ A :: Γ1 ++ A :: Γ2 ⇒ Δ)) →
    { d' : Fam (Γ0 ++ A :: Γ1 ++ Γ2 ⇒ Δ) // d'.height ≤ d.height }

/-- **Goal 4, contraction on the right**, with heights
(`GLS_hpadm_ctr_R`). -/
abbrev ContractionR : Type :=
  (A : Form) → {Γ Δ0 Δ1 Δ2 : List Form} → (d : Fam (Γ ⇒ Δ0 ++ A :: Δ1 ++ A :: Δ2)) →
    { d' : Fam (Γ ⇒ Δ0 ++ A :: Δ1 ++ Δ2) // d'.height ≤ d.height }

/-- **Goal 5, the two systems derive the same sequents.** -/
abbrev PSEquivalent : Type := (s : Seq) → (Fam s → PSFam s) × (PSFam s → Fam s)

end GLS

#axioms_within_file [propext, Quot.sound]
