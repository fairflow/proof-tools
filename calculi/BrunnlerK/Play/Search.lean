/-
# `Play/Search.lean`: the search of system K, to try

Prepared by the operator (2026-11-23) with the report of Prove.  It is in
no library.  Build the instance first (`lake build`, in
`calculi/BrunnlerK/`), then open this file in the editor.

`search Γ` gives a proof of `Γ` in system K or a finite tree that refutes
it (`BrunnlerK/Search.lean`).  `found Γ` says which, as text: the number
of rule instances of the proof, or the tree, written with the
propositions true at a node in braces and its children in brackets.

Change a sequent and see the answer change.  How a sequent is typed:
`Play/BrunnlerK.lean`, the header.
-/
import BrunnlerK.Tactic
import BrunnlerK.Test.Search

open BrunnlerK BrunnlerK.Test

-- Example 2.3 of the source, and its formula.
#eval found seq[◇(∼a ⋏ ∼b), □a, ◇b]
#eval found seq[□(a ⋎ b) ⊃ (□a ⋎ ◇b)]

-- Axiom 4 is not valid: a chain of three states, `a` true at the second only.
#eval found seq[□a ⊃ □□a]

-- `□(p ∨ q) ⊃ (□p ∨ □q)` is not valid: two children.
#eval found seq[◇(∼p ⋏ ∼q), □p, □q]

-- The empty sequent, and the sequent `[∅]`.
#eval found seq[]
#eval found seq[[]]

-- Validity as a theorem, decided in the kernel by the search.
example : Valid seq[□(a ⋏ b) ⊃ (□a ⋏ □b)] := by decide +kernel
example : ¬ Valid seq[□a ⊃ □□a] := by decide +kernel

-- A proof in system K from validity (completeness), and from a proof
-- with a cut (cut elimination).  `cutEx` proves `p̄, p` by a cut on `q`.
example : Nonempty (K seq[□(a ⋏ b) ⊃ (□a ⋏ □b)]) := completeness _ (by decide +kernel)
#eval size cutEx
#eval size (cutElim cutEx)
