/-
The corpus of the Run stage: sequents of known status, each with where
its status comes from, and four families that grow.

Code and data: nothing here is trusted, and the file has no bound on
axioms.  A status written here is a claim to be checked: the facts file
(`BrunnlerK/Corpus/Facts.lean`) holds what the kernel has checked.
-/
import BrunnlerK.Run
import BrunnlerK.Tactic

namespace BrunnlerK.Corpus

open BrunnlerK

abbrev p : Form := .atom 0
abbrev q : Form := .atom 1
abbrev r : Form := .atom 2
abbrev a : Form := .atom 4
abbrev b : Form := .atom 5

/-- The number of rule instances of a proof, axioms counted. -/
def rules {c : Bool} : {Γ : NSeq} → Fam c Γ → Nat
  | _, .ax .. => 1
  | _, .and _ _ _ _ _ d₁ d₂ => rules d₁ + rules d₂ + 1
  | _, .or _ _ _ _ _ d => rules d + 1
  | _, .box _ _ _ _ d => rules d + 1
  | _, .dia _ _ _ _ _ _ d => rules d + 1
  | _, .cut _ _ _ _ d₁ d₂ => rules d₁ + rules d₂ + 1

/-- The number of nodes of a tree. -/
partial def nodes : Tree → Nat
  | .node _ ks => 1 + (ks.map nodes).sum

/-! ## The families -/

/-- The conjunction of `f 0, …, f (n - 1)`, bracketed to the left; `n` at
least 1. -/
def bigAnd (f : Nat → Form) : Nat → Form
  | 0 => f 0
  | 1 => f 0
  | n + 2 => bigAnd f (n + 1) ⋏ f (n + 1)

/-- The same for disjunction. -/
def bigOr (f : Nat → Form) : Nat → Form
  | 0 => f 0
  | 1 => f 0
  | n + 2 => bigOr f (n + 1) ⋎ f (n + 1)

/-- A proposition of the families: numbered from 10, so that they are not
the named ones. -/
def x (i : Nat) : Form := .atom (10 + i)

/-- **`boxAnd n`**: `□(x₀ ∧ … ∧ xₙ₋₁) ⊃ (□x₀ ∧ … ∧ □xₙ₋₁)`.  Valid: `□`
distributes over `∧`. -/
def boxAnd (n : Nat) : NSeq := .leaf [□(bigAnd x n) ⊃ bigAnd (fun i => □(x i)) n]

/-- **`nest n`**: `□ⁿ(p ∨ p̄)`.  Valid, by `n` necessitations. -/
def nest (n : Nat) : NSeq := .leaf [Nat.rec (p ⋎ ∼p) (fun _ A => □A) n]

/-- **`boxOr n`**: `□(x₀ ∨ … ∨ xₙ₋₁) ⊃ (□x₀ ∨ … ∨ □xₙ₋₁)`.  Not valid for
`n` at least 2: `□` does not distribute over `∨`. -/
def boxOr (n : Nat) : NSeq := .leaf [□(bigOr x n) ⊃ bigOr (fun i => □(x i)) n]

/-- **`late n`**: `r, r̄, x₀ ∧ x₀, …, xₙ₋₁ ∧ xₙ₋₁`.  Valid, and an instance
of the axiom as it stands.  The search applies `∧` first. -/
def late (n : Nat) : NSeq := .leaf (r :: ∼r :: (List.range n).map fun i => x i ⋏ x i)

/-! ## The corpus -/

/-- An entry: a name, the sequent, the sequent as Lean source, the status
claimed, and where the claim comes from. -/
structure Entry where
  name : String
  seq : NSeq
  src : String
  valid : Bool
  source : String

/-- The sequents of known status. -/
def entries : List Entry := [
  ⟨"ex23", seq[◇(∼a ⋏ ∼b), □a, ◇b], "seq[◇(∼a ⋏ ∼b), □a, ◇b]", true,
    "the source's Example 2.3, pp. 9–10"⟩,
  ⟨"ex23_formula", seq[□(a ⋎ b) ⊃ (□a ⋎ ◇b)], "seq[□(a ⋎ b) ⊃ (□a ⋎ ◇b)]", true,
    "the source's Example 2.3, its last line; the axiom k in the form of p. 4"⟩,
  ⟨"k_axiom", seq[□(a ⊃ b) ⊃ (□a ⊃ □b)], "seq[□(a ⊃ b) ⊃ (□a ⊃ □b)]", true,
    "the axiom k of the modal logic K"⟩,
  ⟨"box_and", seq[□(a ⋏ b) ⊃ (□a ⋏ □b)], "seq[□(a ⋏ b) ⊃ (□a ⋏ □b)]", true,
    "a theorem of K; the exercises file, 3"⟩,
  ⟨"and_box", seq[(□a ⋏ □b) ⊃ □(a ⋏ b)], "seq[(□a ⋏ □b) ⊃ □(a ⋏ b)]", true,
    "a theorem of K; the exercises file, 4"⟩,
  ⟨"nec_taut", seq[□□(a ⋎ ∼a)], "seq[□□(a ⋎ ∼a)]", true,
    "necessitation of a tautology, twice; the exercises file, 5"⟩,
  ⟨"dia_or", seq[◇(a ⋎ b) ⊃ (◇a ⋎ ◇b)], "seq[◇(a ⋎ b) ⊃ (◇a ⋎ ◇b)]", true,
    "a theorem of K: ◇ distributes over ∨"⟩,
  ⟨"dual", seq[∼(□a) ⊃ ◇(∼a)], "seq[∼(□a) ⊃ ◇(∼a)]", true,
    "the duality of □ and ◇"⟩,
  ⟨"axiom_4", seq[□a ⊃ □□a], "seq[□a ⊃ □□a]", false,
    "the axiom 4: valid on transitive frames only (the source's Figure 2.1, p. 4)"⟩,
  ⟨"axiom_d", seq[□p ⊃ ◇p], "seq[□p ⊃ ◇p]", false,
    "the axiom d: serial frames only (Figure 2.1)"⟩,
  ⟨"axiom_t", seq[□p ⊃ p], "seq[□p ⊃ p]", false,
    "the axiom t: reflexive frames only (Figure 2.1)"⟩,
  ⟨"axiom_b", seq[p ⊃ □◇p], "seq[p ⊃ □◇p]", false,
    "the axiom b: symmetric frames only (Figure 2.1)"⟩,
  ⟨"axiom_5", seq[◇p ⊃ □◇p], "seq[◇p ⊃ □◇p]", false,
    "the axiom 5: euclidean frames only (Figure 2.1)"⟩,
  ⟨"box_or", seq[□(p ⋎ q) ⊃ (□p ⋎ □q)], "seq[□(p ⋎ q) ⊃ (□p ⋎ □q)]", false,
    "□ does not distribute over ∨"⟩,
  ⟨"dia_and", seq[(◇p ⋏ ◇q) ⊃ ◇(p ⋏ q)], "seq[(◇p ⋏ ◇q) ⊃ ◇(p ⋏ q)]", false,
    "◇ does not distribute over ∧"⟩,
  ⟨"empty", seq[], "seq[]", false, "the empty sequent: its formula is ⊥"⟩,
  ⟨"empty_box", seq[[]], "seq[[]]", false, "the sequent [∅]: its formula is □⊥"⟩,
  ⟨"dia_top", seq[◇(p ⋎ ∼p)], "seq[◇(p ⋎ ∼p)]", false,
    "◇⊤: false at a state with no successor"⟩,
  ⟨"boxAnd_4", boxAnd 4, "Corpus.boxAnd 4", true, "the family boxAnd"⟩,
  ⟨"nest_6", nest 6, "Corpus.nest 6", true, "the family nest"⟩,
  ⟨"boxOr_4", boxOr 4, "Corpus.boxOr 4", false, "the family boxOr"⟩,
  ⟨"late_4", late 4, "Corpus.late 4", true, "the family late"⟩]

/-- A member of a family, by the family's name. -/
def family (name : String) (n : Nat) : Option (NSeq × Bool) :=
  if name == "boxAnd" then some (boxAnd n, true)
  else if name == "nest" then some (nest n, true)
  else if name == "boxOr" then some (boxOr n, decide (n < 2))
  else if name == "late" then some (late n, true)
  else none

end BrunnlerK.Corpus
