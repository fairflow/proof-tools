/-
Tests of the search (`BrunnlerK/Search.lean`) and of what rests on it
(`BrunnlerK/Completeness.lean`): on the sequents of the exercises file,
on the boundary cases, and on a proof with a cut.
-/
import BrunnlerK.Completeness
import BrunnlerK.Show
import BrunnlerK.Test.System

namespace BrunnlerK.Test

open BrunnlerK NSeq

/-- The number of rule instances of a proof, axioms counted. -/
def size {c : Bool} : {Γ : NSeq} → Fam c Γ → Nat
  | _, .ax .. => 1
  | _, .and _ _ _ _ _ d₁ d₂ => size d₁ + size d₂ + 1
  | _, .or _ _ _ _ _ d => size d + 1
  | _, .box _ _ _ _ d => size d + 1
  | _, .dia _ _ _ _ _ _ d => size d + 1
  | _, .cut _ _ _ _ d₁ d₂ => size d₁ + size d₂ + 1

/-- A tree as text: the propositions true at the root in braces, then the
children in brackets. -/
partial def showTree : Tree → String
  | .node v ks =>
    "{" ++ ", ".intercalate (v.map propName) ++ "}"
      ++ (if ks.isEmpty then "" else "[" ++ ", ".intercalate (ks.map showTree) ++ "]")

/-- What the search gives, as text: the size of the proof, or the tree. -/
def found (Γ : NSeq) : String :=
  match search Γ with
  | .inl d => s!"proof, {size d} rule instances"
  | .inr r => "refuted at " ++ showTree r.tree

/-- The search's tree, where there is one, does refute, as `holds`
computes it. -/
def refutationChecks (Γ : NSeq) : Bool :=
  match search Γ with
  | .inl _ => false
  | .inr r => !Γ.form.holds r.tree

/-! ## The sequents of the exercises file that have proofs -/

#guard found (mk [◇(∼a ⋏ ∼b), □a, ◇b] []) == "proof, 6 rule instances"
#guard found (mk [□(a ⋎ b) ⊃ (□a ⋎ ◇b)] []) == "proof, 8 rule instances"
#guard found (mk [□(a ⋏ b) ⊃ (□a ⋏ □b)] []) == "proof, 10 rule instances"
#guard found (mk [(□a ⋏ □b) ⊃ □(a ⋏ b)] []) == "proof, 8 rule instances"
#guard found (mk [□□(a ⋎ ∼a)] []) == "proof, 4 rule instances"

/-! ## Those that have none: the tree the search gives -/

#guard found (mk [□a ⊃ □□a] []) == "refuted at {}[{a}[{}]]"          -- axiom 4
#guard found (mk [◇(∼p), ◇p] []) == "refuted at {}"                   -- axiom d
#guard found (mk [◇(∼p), p] []) == "refuted at {}"                    -- axiom t
#guard found (mk [∼p, □◇p] []) == "refuted at {p}[{}]"                -- axiom b
#guard found (mk [□(∼p), □◇p] []) == "refuted at {}[{p}, {}]"         -- axiom 5
#guard found (mk [◇(∼p ⋏ ∼q), □p, □q] []) == "refuted at {}[{q}, {p}]"

#guard [mk [□a ⊃ □□a] [], mk [◇(∼p), ◇p] [], mk [◇(∼p), p] [], mk [∼p, □◇p] [],
        mk [□(∼p), □◇p] [], mk [◇(∼p ⋏ ∼q), □p, □q] []].all refutationChecks

/-! ## Boundary cases -/

#guard found (.leaf []) == "refuted at {}"                             -- the empty sequent
#guard found (mk [] [mk [] []]) == "refuted at {}[{}]"                 -- `[∅]`
#guard found (mk [p, ∼p] []) == "proof, 1 rule instances"
#guard found (mk [] [mk [] [mk [p, ∼p] []]]) == "proof, 1 rule instances"   -- two boxes deep
#guard found (mk [◇p] [mk [∼p] [], mk [] []]) == "proof, 2 rule instances"
#guard found (mk [◇p] [mk [] [], mk [∼p] []]) == "proof, 2 rule instances"  -- the second box
#guard found (mk [p, p, ∼q] []) == "refuted at {q}"                    -- a formula twice

/-! ## Validity decided -/

#guard decide (Valid (mk [□(a ⋎ b) ⊃ (□a ⋎ ◇b)] []))
#guard !decide (Valid (mk [□a ⊃ □□a] []))

-- The same in the kernel: the search reduces there, so a sequent's
-- validity, or that it is not valid, is a theorem by `decide`.
example : Valid (mk [□(a ⋎ b) ⊃ (□a ⋎ ◇b)] []) := by decide +kernel
example : Valid (mk [(□a ⋏ □b) ⊃ □(a ⋏ b)] []) := by decide +kernel
example : ¬ Valid (mk [□a ⊃ □□a] []) := by decide +kernel
example : ¬ Valid (mk [◇(∼p ⋏ ∼q), □p, □q] []) := by decide +kernel
example : ¬ Valid (.leaf []) := by decide +kernel
-- And with completeness, that there is a proof in system K.
example : Nonempty (K (mk [□(a ⋏ b) ⊃ (□a ⋏ □b)] [])) :=
  completeness _ (by decide +kernel)

/-! ## A cut removed

`cutEx` proves `p̄, p` by a cut on `q`.  `cutElim` gives a proof in system
K: the search's. -/

#guard size cutEx == 3
#guard size (cutElim cutEx) == 1

/-- A cut on a modal formula, inside a box: `[ā, a]` from `[ā, a, □b]`
and `[ā, a, ◇b̄]`. -/
def cutEx₂ : Kcut (mk [] [mk [∼a, a] []]) :=
  .cut [0] (□b) rfl rfl
    (.ax [0] 4 rfl (by decide) (by decide))
    (.ax [0] 4 rfl (by decide) (by decide))

#guard size (cutElim cutEx₂) == 1

end BrunnlerK.Test
