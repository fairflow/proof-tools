/-
A second evaluation of truth at the root of a finite tree, for the program
`glsrun`: by a table, one row for each world and one column for each
subformula.

`Seq.refutedAt` (`GLS/Semantics.lean`) is the check of the certifiers
`noValid` and `noDerivable`, and the one the kernel runs.  It evaluates
`□A` at a world by evaluating `A` at every world below, with nothing
kept: compiled, that is one evaluation for every chain of worlds, and
`□³³⊥ → □³²⊥` on a chain of 33 worlds was not checked in 10 s.  (The
kernel shares the terms it has reduced, and checks the same tree in under
a second.)  So the program checks a tree by the table below before it
prints it, and the kernel checks the printed tree by `Seq.refutedAt`.

Code: nothing here is trusted or proved, and the file has no bound on
axioms.  `GLS/ParseTest.lean` compares the two evaluations on the
screens' sequents and trees.
-/
import GLS.Semantics

namespace GLS

/-- The subformulas of a formula, the parts of each before it. -/
def Form.subs : Form → List Form
  | .var p => [.var p]
  | ⊥ => [⊥]
  | A ⟶ B => A.subs ++ B.subs ++ [A ⟶ B]
  | □A => A.subs ++ [□A]

namespace FastCheck

/-- A column of the table: a subformula, its parts given by their
columns. -/
inductive Col where
  | var (p : Nat)
  | bot
  | imp (i j : Nat)
  | box (i : Nat)
  deriving Inhabited

/-- The subformulas of a sequent, each once, the parts of each before
it. -/
def subsOf (s : Seq) : Array Form :=
  ((s.ant ++ s.suc).flatMap Form.subs).foldl (fun acc A => if acc.contains A then acc else acc.push A) #[]

/-- The column of a formula. -/
def col (subs : Array Form) (A : Form) : Nat := (subs.idxOf? A).getD 0

/-- The columns, from the subformulas. -/
def cols (subs : Array Form) : Array Col :=
  subs.map fun
    | .var p => .var p
    | ⊥ => .bot
    | A ⟶ B => .imp (col subs A) (col subs B)
    | □A => .box (col subs A)

/-- The row of a world, and with it the row "true here and at every world
below". -/
partial def rows (cs : Array Col) : Tree → Array Bool × Array Bool
  | .node val kids =>
    let ks := kids.map (rows cs)
    -- true at every world below: at each child, and at every world below it
    let below (i : Nat) : Bool := ks.all fun k => k.2[i]!
    let here := cs.foldl (init := (#[] : Array Bool)) fun acc c =>
      acc.push (match c with
        | .var p => val.contains p
        | .bot => false
        | .imp i j => !acc[i]! || acc[j]!
        | .box i => below i)
    (here, (Array.range cs.size).map fun i => here[i]! && below i)

/-- **The sequent is false at the root of the tree**, by the table: every
formula of the antecedent is true there and none of the succedent. -/
def refuted (s : Seq) (t : Tree) : Bool :=
  let subs := subsOf s
  let here := (rows (cols subs) t).1
  s.ant.all (fun A => here[col subs A]!) && s.suc.all (fun B => !here[col subs B]!)

end FastCheck

end GLS
