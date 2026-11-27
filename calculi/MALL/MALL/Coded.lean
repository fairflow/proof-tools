/-
A saturated set written in numbers: the check of `MALL/Saturated.lean` in
a form that Lean's kernel evaluates cheaply.

The kernel does arithmetic on numerals by a library for large numbers, one
step for an addition or a comparison whatever the size, and pays some
thousands of bytes for every step of a recursion over a list.  So:

* the formulas of the set are listed once, in a table, each given by its
  connective and the places of its two parts (`Node`);
* a sequent is one number: its digit in base `B` at the place of a formula
  is the number of times the formula occurs (`dec`).  Putting a formula
  in a sequent is an addition, and two sequents are the same multiset
  when the numbers are equal;
* the set is a search tree of those numbers (`Tree`);
* the ways to divide the context of a ⊗ are counted without repetition:
  `k` copies of one formula give `k + 1` ways, not `2 ^ k` (`allParts`).

`codeRefutes C Γ = true` is what the kernel evaluates.  It implies
`refutedBy C.sequents Γ = true` (`refutedBy_of_code`), so the theorems of
`MALL/Saturated.lean` hold of the set that the numbers stand for.

Theory file: it ends with its bound on axioms.
-/
import MALL.Saturated
import MALL.Split

namespace MALL

open List

/-! ## The table of formulas -/

/-- A formula of a table: its connective, and for each of its two parts
how many entries after it the part stands (0 for the next entry). -/
inductive Node where
  | atom (a : Nat)
  | natom (a : Nat)
  | one
  | bot
  | top
  | zero
  | tensor (a c : Nat)
  | par (a c : Nat)
  | wth (a c : Nat)
  | plus (a c : Nat)
  deriving DecidableEq, Repr

/-- The formula of an entry, given the formulas of the entries after it. -/
def Node.form (fs : List Form) : Node → Form
  | .atom a => .atom a
  | .natom a => .natom a
  | .one => .one
  | .bot => .bot
  | .top => .top
  | .zero => .zero
  | .tensor a c => .tensor (fs.getD a .one) (fs.getD c .one)
  | .par a c => .par (fs.getD a .one) (fs.getD c .one)
  | .wth a c => .wth (fs.getD a .one) (fs.getD c .one)
  | .plus a c => .plus (fs.getD a .one) (fs.getD c .one)

/-- The formulas of a table, in its order. -/
def forms : List Node → List Form
  | [] => []
  | N :: T => N.form (forms T) :: forms T

/-! ## A sequent as a number -/

/-- **The sequent of a number**, over a list of formulas: the digit in base
`B` at a formula's place is the number of times it occurs. -/
def dec (B : Nat) : List Form → Nat → List Form
  | [], _ => []
  | X :: fs, d => List.replicate (d % B) X ++ dec B fs (d / B)

/-! ## The set as a search tree -/

/-- A search tree of numbers. -/
inductive Tree where
  | leaf
  | node (l : Tree) (k : Nat) (r : Tree)
  deriving Repr

/-- Is the number in the tree?  (By the order of the keys: a tree that is
not in order only fails to find.) -/
def Tree.has : Tree → Nat → Bool
  | .leaf, _ => false
  | .node l k r, c => bif Nat.ble k c then (bif Nat.ble c k then true else r.has c) else l.has c

/-- The numbers of a tree, from the left. -/
def Tree.keys : Tree → List Nat
  | .leaf => []
  | .node l k r => l.keys ++ k :: r.keys

/-- A property of every number of a tree. -/
def Tree.all (P : Nat → Bool) : Tree → Bool
  | .leaf => true
  | .node l k r => Tree.all P l && P k && Tree.all P r

/-! ## The parts of a multiset -/

/-- The formulas present in a number, each as its unit `B ^ i` (given
`u = B ^ i` at the start) and its digit. -/
def support (B : Nat) : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | n + 1, q, u =>
    bif Nat.beq (q % B) 0 then support B n (q / B) (u * B)
    else (u, q % B) :: support B n (q / B) (u * B)

/-- `f x`, `f (x + u)`, …, `f (x + c * u)`. -/
def upTo (f : Nat → Bool) (u : Nat) : Nat → Nat → Bool
  | 0, x => f x
  | c + 1, x => f x && upTo f u c (x + u)

/-- A property of every part of a multiset given by its support, each part
added to `x`: every choice of at most the digit, at every formula. -/
def allParts (P : Nat → Bool) : List (Nat × Nat) → Nat → Bool
  | [], x => P x
  | (u, c) :: s, x => upTo (allParts P s) u c x

/-! ## The check -/

/-- **The condition at one formula of a member**: `r` is the rest of the
member, `i` the place of the formula, `n` the length of the table. -/
def nodeOK (B n : Nat) (t : Tree) (r i : Nat) : Node → Bool
  | .atom _ => true
  | .natom _ => true
  | .one => true
  | .zero => true
  | .top => false
  | .bot => t.has r
  | .par a c =>
    Nat.blt (i + 1 + a) n && Nat.blt (i + 1 + c) n && t.has (r + B ^ (i + 1 + a) + B ^ (i + 1 + c))
  | .wth a c =>
    Nat.blt (i + 1 + a) n && Nat.blt (i + 1 + c) n &&
      (t.has (r + B ^ (i + 1 + a)) || t.has (r + B ^ (i + 1 + c)))
  | .plus a c =>
    Nat.blt (i + 1 + a) n && Nat.blt (i + 1 + c) n &&
      (t.has (r + B ^ (i + 1 + a)) && t.has (r + B ^ (i + 1 + c)))
  | .tensor a c =>
    Nat.blt (i + 1 + a) n && Nat.blt (i + 1 + c) n &&
      allParts (fun x => t.has (x + B ^ (i + 1 + a)) || t.has (r - x + B ^ (i + 1 + c)))
        (support B n r 1) 0

/-- A sequent that is not the conclusion of the logical axiom at a letter
nor of the rule 1. -/
def axFree : List Form → Bool
  | [.one] => false
  | [.atom a, .natom b] => !(Nat.beq a b)
  | [.natom a, .atom b] => !(Nat.beq a b)
  | _ => true

/-- The walk along the table for one member `d`: `i` is the place, `q` the
digits not yet read, `s` the sum of the digits read. -/
def walk (B n : Nat) (t : Tree) (fs : List Form) (d : Nat) : List Node → Nat → Nat → Nat → Bool
  | [], _, q, s => Nat.beq q 0 && (Nat.blt 2 s || axFree (dec B fs d))
  | N :: T, i, q, s =>
    Nat.blt (q % B + 2) B &&
    (bif Nat.beq (q % B) 0 then true else nodeOK B n t (d - B ^ i) i N) &&
    walk B n t fs d T (i + 1) (q / B) (s + q % B)

/-- **A saturated set, in numbers.** -/
structure CodeCert where
  /-- The base of the digits: more than any multiplicity, by 3. -/
  B : Nat
  /-- The formulas. -/
  table : List Node
  /-- The members. -/
  tree : Tree
  /-- The sequent refuted: the place of each of its formulas, in its order. -/
  goal : List Nat
  deriving Repr

namespace CodeCert

variable (C : CodeCert)

/-- The condition of saturation at one member. -/
def memberOK (d : Nat) : Bool :=
  walk C.B C.table.length C.tree (forms C.table) d C.table 0 d 0

/-- The sequents that the numbers stand for. -/
def sequents : List (List Form) := C.tree.keys.map (dec C.B (forms C.table))

/-- The number of a list of places. -/
def code (B : Nat) : List Nat → Nat
  | [] => 0
  | i :: l => B ^ i + code B l

/-- The formulas at the places can be taken out of the number one by one,
and nothing is left. -/
def drain (B n : Nat) : Nat → List Nat → Bool
  | g, [] => Nat.beq g 0
  | g, i :: l => Nat.blt i n && Nat.ble 1 (g / B ^ i % B) && drain B n (g - B ^ i) l

/-- The sequent is the one at the places `goal`, and its number is in the
tree. -/
def goalOK (Γ : List Form) : Bool :=
  decide (Γ = C.goal.map fun i => (forms C.table).getD i .one) &&
  C.tree.has (code C.B C.goal) &&
  drain C.B C.table.length (code C.B C.goal) C.goal

end CodeCert

/-- **The check that the kernel runs.** -/
def codeRefutes (C : CodeCert) (Γ : List Form) : Bool :=
  C.goalOK Γ && C.tree.all C.memberOK

/-- **The statement** (S27 of `campaign/statements.md`): a certificate in
numbers that passes stands for a set of sequents that passes the check of
`MALL/Saturated.lean`.  Proved in `MALL/CodedSound.lean`. -/
def CodeSoundness : Prop :=
  ∀ (C : CodeCert) (Γ : List Form), codeRefutes C Γ = true → refutedBy C.sequents Γ = true

end MALL
