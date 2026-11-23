/-
Tests of the depth of a proof, of `nec`, `wk` and exchange
(`BrunnlerK/Structural.lean`), and of the general axiom
(`BrunnlerK/Identity.lean`).
-/
import BrunnlerK.Structural
import BrunnlerK.Identity
import BrunnlerK.Test.System

namespace BrunnlerK.Test

open BrunnlerK NSeq

/-! ## Depth -/

-- Example 2.3: `□`, `◇k_c`, `∧`, and on the right branch `◇k_c`; the
-- axioms are leaves.
example : ex23.depth = 4 := rfl
example : ex23'.depth = 6 := rfl
example : cutEx.depth = 1 := rfl

/-! ## `nec`, `wk`, exchange: each used once -/

-- `[Γ]` from `Γ`, at most as deep.
example : ∃ d : K (mk [] [mk [◇(∼a ⋏ ∼b), □a, ◇b] []]), d.depth ≤ 4 := nec ex23

-- `Γ{Δ}` from `Γ{∅}`: here at the root, `Δ` is `c, [d]`.
example : ∃ d : K (mk [c, ◇(∼a ⋏ ∼b), □a, ◇b] [mk [d] []]), d.depth ≤ 4 :=
  wk (Ctx.root (mk [◇(∼a ⋏ ∼b), □a, ◇b] [])) (mk [c] [mk [d] []]) ex23

-- and inside a box.
example : ∃ d : K (mk [] [mk [c, a, ∼a] []]), d.depth ≤ 0 :=
  wk (Ctx.at_ (mk [] [mk [a, ∼a] []]) [0] rfl) (.leaf [c])
    (.ax [0] 4 rfl (by decide) (by decide))

-- The first two formulas of the root exchanged.
example : ∃ d : K (mk [□a, ◇(∼a ⋏ ∼b), ◇b] []), d.depth ≤ 4 :=
  exchange (.forms (Θ := mk [◇(∼a ⋏ ∼b), □a, ◇b] []) [] [□a, ◇(∼a ⋏ ∼b), ◇b] rfl
    (List.Perm.swap (□a) (◇(∼a ⋏ ∼b)) [◇b])) ex23

-- Two boxes exchanged.
example : Exch (mk [a] [mk [b] [], mk [c] []]) (mk [a] [mk [c] [], mk [b] []]) :=
  .boxes [] 0 rfl

/-! ## The general axiom -/

/-- `□(a ∨ b), ◇(ā ∧ b̄)`: a formula and its negation. -/
def gaxEx : K (mk [□(a ⋎ b), ◇(∼a ⋏ ∼b)] []) :=
  Fam.gax (□(a ⋎ b)) [] rfl (.head _) (.tail _ (.head _))

example : gaxEx.depth = 4 := by decide +kernel

-- In the source's shape, `Γ{A, Ā}`, two boxes deep.
example : K (mk [c] [mk [] [mk [◇a ⋏ b, □(∼a) ⋎ ∼b] []]]) :=
  Fam.gaxC (Ctx.at_ (mk [c] [mk [] [mk [] []]]) [0, 0] rfl) (◇a ⋏ b)

end BrunnlerK.Test
