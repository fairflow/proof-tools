/-
Screens of the statements of `BrunnlerK/Semantics.lean`, run before any
of them is proved: the corresponding formula on small sequents; each rule
on small trees (no tree may make every premise true and the conclusion
not true); the sequents that are not derivable (each should have a small
tree that refutes it).

A screen is evidence and not a proof.  Truth at a tree is computed by
`Form.holds`.
-/
import BrunnlerK.Semantics
import BrunnlerK.Proof
import BrunnlerK.Show
import BrunnlerK.Test.System

namespace BrunnlerK.Test

open BrunnlerK NSeq

/-! ## The corresponding formula -/

example : (NSeq.leaf []).form = Form.bot := rfl
example : (mk [a] []).form = a := rfl
example : (mk [a, b, c] []).form = a ⋎ b ⋎ c := rfl
example : (mk [] [mk [] []]).form = □Form.bot := rfl
example : (mk [a, b] [mk [c] [mk [] []], mk [d] []]).form
    = a ⋎ b ⋎ □(c ⋎ □Form.bot) ⋎ □d := rfl
#guard (mk [◇(∼a ⋏ ∼b), ◇b] [mk [a] []]).form.show
    == "◇(ā ∧ b̄) ∨ ◇b ∨ □a"

/-! ## A bank of small trees -/

/-- Every list of some of the given propositions. -/
def vals (ps : List Nat) : List (List Nat) :=
  ps.foldr (fun p acc => acc ++ acc.map (p :: ·)) [[]]

/-- Every tree with any of the valuations at the root and none, one or
two of the given trees as children. -/
def grow (ps : List Nat) (ts : List Tree) : List Tree :=
  (vals ps).flatMap fun v =>
    .node v [] :: (ts.map fun t => .node v [t])
      ++ (ts.flatMap fun t => ts.map fun u => .node v [t, u])

/-- The trees of depth at most `n`, at most two children at a node, over
the given propositions. -/
def bank (ps : List Nat) : Nat → List Tree
  | 0 => (vals ps).map (.node · [])
  | n + 1 => grow ps (bank ps n)

/-- Over `a`, `b`, depth at most 2. -/
def bankAB : List Tree := bank [4, 5] 2
/-- Over `p`, `q`, depth at most 2. -/
def bankPQ : List Tree := bank [0, 1] 2

#guard bankAB.length == 28564

/-! ## `Form.holds`, clause by clause -/

#guard a.holds (.node [4] [])
#guard !a.holds (.node [5] [])
#guard (∼a).holds (.node [5] [])
#guard !Form.bot.holds (.node [0] []) && !Form.bot.holds (.node [] [])
#guard (□a).holds (.node [] [])                    -- no child: every box is true
#guard !(◇a).holds (.node [4] [])                  -- and no diamond
#guard (◇a).holds (.node [] [.node [] [], .node [4] []])
#guard !(□a).holds (.node [] [.node [] [], .node [4] []])

/-! ## Soundness, rule by rule

For a move and a sequent: at no tree of the bank is every premise true
and the conclusion not true. -/

/-- The premises of a move, or none where it does not apply. -/
def prems (m : Move) (Γ : NSeq) : List NSeq :=
  match S.step m Γ with
  | .ok ps => ps
  | .error _ => []

/-- The move applies, and no tree of the bank is a counterexample. -/
def stepSound (bk : List Tree) (m : Move) (Γ : NSeq) : Bool :=
  match S.step m Γ with
  | .ok ps => bk.all fun t => !(ps.all fun Δ => Δ.form.holds t) || Γ.form.holds t
  | .error _ => false

/-- The same for an instance of `cut`, at the root or inside a box. -/
def cutSound (bk : List Tree) (pa : Path) (A : Form) (Γ : NSeq) : Bool :=
  match Γ.node? pa with
  | some Θ => bk.all fun t =>
      !((Γ.setNode pa (Θ.add A)).form.holds t && (Γ.setNode pa (Θ.add ∼A)).form.holds t)
        || Γ.form.holds t
  | none => false

-- The six rule instances of Example 2.3, and each of its sequents true
-- at every tree of the bank.
def e0 : NSeq := mk [◇(∼a ⋏ ∼b), □a, ◇b] []
def e1 : NSeq := (prems (.box [] a) e0).getD 0 (.leaf [])
def e2 : NSeq := (prems (.dia [] 0 (∼a ⋏ ∼b)) e1).getD 0 (.leaf [])
def e3 : NSeq := (prems (.and [0] (∼a) (∼b)) e2).getD 0 (.leaf [])
def e4 : NSeq := (prems (.and [0] (∼a) (∼b)) e2).getD 1 (.leaf [])
def e5 : NSeq := (prems (.dia [] 0 b) e4).getD 0 (.leaf [])

#guard stepSound bankAB (.box [] a) e0
#guard stepSound bankAB (.dia [] 0 (∼a ⋏ ∼b)) e1
#guard stepSound bankAB (.and [0] (∼a) (∼b)) e2
#guard stepSound bankAB (.ax [0] 4) e3
#guard stepSound bankAB (.dia [] 0 b) e4
#guard stepSound bankAB (.ax [0] 5) e5
#guard [e0, e1, e2, e3, e4, e5].all fun Γ => bankAB.all fun t => Γ.form.holds t

-- Each rule where its conclusion is not valid: the step is still sound.
#guard stepSound bankAB (.or [] a b) (mk [a ⋎ b] [])
#guard stepSound bankAB (.and [] a b) (mk [a ⋏ b, ∼a] [])
#guard stepSound bankAB (.box [] a) (mk [□a, b] [mk [b] []])
#guard stepSound bankAB (.dia [] 0 a) (mk [◇a] [mk [b] []])
#guard stepSound bankAB (.dia [] 1 a) (mk [◇a, b] [mk [b] [], mk [] []])
-- One box deep, and two.
#guard stepSound bankAB (.or [0] a b) (mk [] [mk [a ⋎ b] []])
#guard stepSound bankAB (.and [0] a b) (mk [∼b] [mk [a ⋏ b] []])
#guard stepSound bankAB (.box [0] a) (mk [] [mk [□a] []])
#guard stepSound bankAB (.dia [0] 0 a) (mk [] [mk [◇a] [mk [b] []]])
#guard stepSound bankAB (.and [0, 0] a b) (mk [] [mk [] [mk [a ⋏ b] []]])
-- The axiom two boxes deep.
#guard stepSound bankAB (.ax [0, 0] 4) (mk [] [mk [] [mk [a, ∼a] []]])

-- `cut`: at the root, in a box, on a modal formula, on the empty node.
#guard cutSound bankAB [] a (mk [b] [])
#guard cutSound bankAB [] (□a) (mk [] [mk [b] []])
#guard cutSound bankAB [0] (a ⋏ ◇b) (mk [b] [mk [] []])
#guard cutSound bankAB [0, 0] (◇a) (mk [] [mk [b] [mk [] []]])

/-! ## Completeness: what is not derivable has a small refutation

The empty sequent, the sequent `[∅]`, and the six sequents of the
exercises file that are not derivable: each is not true at some tree of
the bank. -/

/-- Some tree of the bank refutes the sequent. -/
def refuted (bk : List Tree) (Γ : NSeq) : Bool :=
  bk.any fun t => !Γ.form.holds t

#guard refuted bankPQ (.leaf [])
#guard refuted bankPQ (mk [] [mk [] []])
#guard refuted bankAB (mk [□a ⊃ □□a] [])                 -- axiom 4
#guard refuted bankPQ (mk [◇(∼p), ◇p] [])                -- axiom d
#guard refuted bankPQ (mk [◇(∼p), p] [])                 -- axiom t
#guard refuted bankPQ (mk [∼p, □◇p] [])                  -- axiom b
#guard refuted bankPQ (mk [□(∼p), □◇p] [])               -- axiom 5
#guard refuted bankPQ (mk [◇(∼p ⋏ ∼q), □p, □q] [])

-- The chain the exercises file describes refutes axiom 4.
#guard !(□a ⊃ □□a).holds (.node [] [.node [4] [.node [] []]])

-- And what is derivable has none in the bank: the five sequents of the
-- exercises file that have derivations.
#guard !refuted bankAB (mk [□(a ⋎ b) ⊃ (□a ⋎ ◇b)] [])
#guard !refuted bankAB (mk [□(a ⋏ b) ⊃ (□a ⋏ □b)] [])
#guard !refuted bankAB (mk [(□a ⋏ □b) ⊃ □(a ⋏ b)] [])
#guard !refuted bankAB (mk [□□(a ⋎ ∼a)] [])

end BrunnlerK.Test
