/-
Tests of the two families as transcribed: the source's Example 2.3 written
with the constructors of `Fam`, and small proofs in `FamO` with its
provisos.  No proof system, no moves: these are terms of the families.
-/
import BrunnlerK.System
import BrunnlerK.SystemO
import BrunnlerK.Test.Sequent

namespace BrunnlerK.Test

open BrunnlerK NSeq

/-- **Example 2.3** (p. 9), from the sequent `◇(ā ∧ b̄), □a, ◇b` up:
`□`, `◇k_c`, `∧`, and on the right branch `◇k_c` once more.  Each leaf is
an instance of the axiom. -/
def ex23 : K (mk [◇(∼a ⋏ ∼b), □a, ◇b] []) :=
  .box [] a rfl (by decide) <|                  -- ◇(ā ∧ b̄), ◇b, [a]
  .dia [] 0 (∼a ⋏ ∼b) rfl (by decide) rfl <|   -- ◇(ā ∧ b̄), ◇b, [ā ∧ b̄, a]
  .and [0] (∼a) (∼b) rfl (by decide)
    (.ax [0] 4 rfl (by decide) (by decide))     -- ◇(ā ∧ b̄), ◇b, [ā, a]
    (.dia [] 0 b rfl (by decide) rfl <|         -- ◇(ā ∧ b̄), ◇b, [b, b̄, a]
     .ax [0] 5 rfl (by decide) (by decide))

/-- Example 2.3 from its formula `□(a ∨ b) ⊃ (□a ∨ ◇b)`: the rule `∨`
twice, then as above. -/
def ex23' : K (mk [□(a ⋎ b) ⊃ (□a ⋎ ◇b)] []) :=
  .or [] (◇(∼a ⋏ ∼b)) (□a ⋎ ◇b) rfl (by decide) <|
  .or [] (□a) (◇b) rfl (by decide) <|           -- □a, ◇b, ◇(ā ∧ b̄)
  .box [] a rfl (by decide) <|
  .dia [] 0 (∼a ⋏ ∼b) rfl (by decide) rfl <|
  .and [0] (∼a) (∼b) rfl (by decide)
    (.ax [0] 4 rfl (by decide) (by decide))
    (.dia [] 0 b rfl (by decide) rfl <|
     .ax [0] 5 rfl (by decide) (by decide))

/-- A cut, in K + cut only: `p̄, p` from `p̄, p, q` and `p̄, p, q̄`. -/
def cutEx : Kcut (mk [∼p, p] []) :=
  .cut [] q rfl rfl
    (.ax [] 0 rfl (by decide) (by decide))
    (.ax [] 0 rfl (by decide) (by decide))

-- In system K the constructor `cut` asks for a proof of `false = true`.
example (Γ Δ : NSeq) (A : Form) (h : false = true) (hΔ : Γ.node? [] = some Δ)
    (d₁ : K (Γ.setNode [] (Δ.add A))) (d₂ : K (Γ.setNode [] (Δ.add ∼A))) : K Γ :=
  .cut [] A h hΔ d₁ d₂

/-- In `K°`: `□(p ∨ p̄)`.  The rule `□°` keeps `□(p ∨ p̄)` and adds the box
`[p ∨ p̄]`; `∨°` keeps `p ∨ p̄` and adds `p, p̄`. -/
def boxO : FamO (mk [□(p ⋎ ∼p)] []) :=
  .box [] (p ⋎ ∼p) rfl (by decide) (by decide) (by decide) <|
  .or [0] p (∼p) rfl (by decide) (by decide) <|
  .ax [0] 0 rfl (by decide) (by decide)

-- The side condition of `□°` fails once the box is there: the node of
-- `□(p ∨ p̄)` has a child that contains `p ∨ p̄`.
example : ¬ ∀ Λ ∈ (mk [□(p ⋎ ∼p)] [mk [p ⋎ ∼p] []]).boxes, (p ⋎ ∼p) ∉ Λ.forms := by decide

-- The proviso fails for `∨°` applied a second time: the premise has the
-- set sequent of the conclusion.
example : ((mk [p, ∼p, p ⋎ ∼p] []).setNode [] (((mk [p, ∼p, p ⋎ ∼p] []).add (∼p)).add p)).sameSet
    (mk [p, ∼p, p ⋎ ∼p] []) = true := by decide

end BrunnlerK.Test
