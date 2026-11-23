/-
Tests of the depth of a proof, of `nec`, `wk` and exchange
(`BrunnlerK/Structural.lean`), and of the general axiom
(`BrunnlerK/Identity.lean`).
-/
import BrunnlerK.Structural
import BrunnlerK.Identity
import BrunnlerK.Contract
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

/-! ## The inverse rules, and contraction: each used once -/

-- From `□(a ∨ ā)`, `[a ∨ ā]`; from that, `[a, ā]`: each at most as deep.
example : ∃ d : K (mk [] [mk [a ⋎ ∼a] []]), d.depth ≤ 2 :=
  inv_box_C (Ctx.root (.leaf [])) (a ⋎ ∼a)
    (.box [] (a ⋎ ∼a) rfl (by decide) <|
     .or [0] a (∼a) rfl (by decide) <|
     .ax [0] 4 rfl (by decide) (by decide))

example : ∃ d : K (mk [] [mk [a, ∼a] []]), d.depth ≤ 1 :=
  inv_or_C (Ctx.at_ (mk [] [mk [] []]) [0] rfl) a (∼a)
    (.or [0] a (∼a) rfl (by decide) <|
     .ax [0] 4 rfl (by decide) (by decide))

-- From `(a ∨ ā) ∧ b` with `b̄`, the right premise `b, b̄`.
example : ∃ d : K (mk [b, ∼b] []), d.depth ≤ 2 :=
  inv_andR_C (Ctx.root (mk [∼b] [])) (a ⋎ ∼a) b
    (.and [] (a ⋎ ∼a) b rfl (by decide)
      (.or [] a (∼a) rfl (by decide) <| .ax [] 4 rfl (by decide) (by decide))
      (.ax [] 5 rfl (by decide) (by decide)))

-- `ctr`: from `Γ{Δ, Δ}`, `Γ{Δ}`.  Here `Δ` is `◇a, [ā]`, twice at the root.
example : ∃ d : K (mk [◇a] [mk [∼a] []]), d.depth ≤ 1 :=
  ctr (Ctx.root (.leaf [])) (mk [◇a] [mk [∼a] []])
    (.dia [] 0 a rfl (by decide) rfl <|
     .ax [0] 4 rfl (by decide) (by decide))

-- and in a box, `Δ` a formula: from `[a ∨ ā, a ∨ ā]`, `[a ∨ ā]`.
example : ∃ d : K (mk [] [mk [a ⋎ ∼a] []]), d.depth ≤ 1 :=
  ctr (Ctx.at_ (mk [] [mk [] []]) [0] rfl) (.leaf [a ⋎ ∼a])
    (.or [0] a (∼a) rfl (by decide) <|
     .ax [0] 4 rfl (by decide) (by decide))

end BrunnlerK.Test
