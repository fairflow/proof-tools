/-
Tests of contexts and of the rules in the figure's shape
(`BrunnlerK/Ctx.lean`).

A rule in the figure's shape acts on what fills the hole, and `fill` puts
that in front of the node's formulas and after its boxes.  So such a rule
applies as it stands only where the formula it acts on is the first of
its node; elsewhere the constructor of `Fam` is used, which asks for the
formula by membership.  Both are used below.
-/
import BrunnlerK.Ctx
import BrunnlerK.Test.System

namespace BrunnlerK.Test

open BrunnlerK NSeq

/-! ## Filling a hole -/

-- At the root: `Θ, { }` filled with `Δ` is `Θ, Δ`.
example : (Ctx.root (mk [a] [mk [b] []])).fill (mk [c] [mk [d] []])
    = mk [c, a] [mk [b] [], mk [d] []] := rfl
-- In a box, and two boxes deep.
example : (Ctx.at_ (mk [a] [mk [b] []]) [0] rfl).fill (.leaf [c])
    = mk [a] [mk [c, b] []] := rfl
example : (Ctx.at_ (mk [] [mk [] [], mk [a] [mk [] []]]) [1, 0] rfl).fill (mk [c] [mk [d] []])
    = mk [] [mk [] [], mk [a] [mk [c] [mk [d] []]]] := rfl
-- `Γ{∅}` is the context with the hole taken out.
example : (Ctx.at_ (mk [a] [mk [b] []]) [0] rfl).fill (.leaf []) = mk [a] [mk [b] []] := rfl
-- The depth is the number of boxes above the hole.
example : (Ctx.at_ (mk [] [mk [] [], mk [a] [mk [] []]]) [1, 0] rfl).depth = 2 := rfl

/-! ## Each rule, in the figure's shape -/

-- The axiom `Γ{p, p̄}`, in a box.
example : K (mk [b] [mk [a, ∼a, c] []]) :=
  Fam.axC (Ctx.at_ (mk [b] [mk [c] []]) [0] rfl) 4

-- `∧`: from `Γ{A}` and `Γ{B}`, `Γ{A ∧ B}`.
example : K (mk [(a ⋎ ∼a) ⋏ (b ⋎ ∼b)] []) :=
  Fam.andC (Ctx.root (.leaf [])) (a ⋎ ∼a) (b ⋎ ∼b)
    (Fam.orC (Ctx.root (.leaf [])) a (∼a) (Fam.axC (Ctx.root (.leaf [])) 4))
    (Fam.orC (Ctx.root (.leaf [])) b (∼b) (Fam.axC (Ctx.root (.leaf [])) 5))

-- `□`, then `∨` and the axiom inside the new box: `□(a ∨ ā)`.
example : K (mk [□(a ⋎ ∼a)] []) :=
  Fam.boxC (Ctx.root (.leaf [])) (a ⋎ ∼a) <|
  Fam.orC (Ctx.at_ (mk [] [mk [] []]) [0] rfl) a (∼a) <|
  Fam.axC (Ctx.at_ (mk [] [mk [] []]) [0] rfl) 4

-- `◇k_c`: from `Γ{◇A, [Δ, A]}`, `Γ{◇A, [Δ]}`.  Here `◇a, [ā]`.
example : K (mk [◇a] [mk [∼a] []]) :=
  Fam.diaC (Ctx.root (.leaf [])) a (.leaf [∼a]) <|
  Fam.axC (Ctx.at_ (mk [◇a] [mk [] []]) [0] rfl) 4

-- `cut`: from `Γ{A}` and `Γ{Ā}`, `Γ{∅}`.  Here `p̄, p` by a cut on `q`.
example : Kcut (mk [∼p, p] []) :=
  Fam.cutC (Ctx.root (mk [∼p, p] [])) q
    (.ax [] 0 rfl (by decide) (by decide))
    (.ax [] 0 rfl (by decide) (by decide))

/-! ## Example 2.3 (pp. 9–10), the figure's rules where they fit

From `□a, ◇(ā ∧ b̄), ◇b`.  The steps `□`, `◇k_c` and `∧` act on the first
formula of their node and are the rules in the figure's shape.  The two
axioms and the second `◇k_c` do not: `ā, a` has the negated proposition
first, and `◇b` is the second formula of the root.  Those are the
constructors of `Fam`. -/
def ex23C : K (mk [□a, ◇(∼a ⋏ ∼b), ◇b] []) :=
  Fam.boxC (Ctx.root (mk [◇(∼a ⋏ ∼b), ◇b] [])) a <|
  Fam.diaC (Ctx.root (mk [◇b] [])) (∼a ⋏ ∼b) (.leaf [a]) <|
  Fam.andC (Ctx.at_ (mk [◇(∼a ⋏ ∼b), ◇b] [mk [a] []]) [0] rfl) (∼a) (∼b)
    (.ax [0] 4 rfl (by decide) (by decide))
    (.dia [] 0 b rfl (by decide) rfl <|
     .ax [0] 5 rfl (by decide) (by decide))

end BrunnlerK.Test
