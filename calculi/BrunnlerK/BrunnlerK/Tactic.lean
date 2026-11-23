/-
The editor's part for system K: how a sequent is typed, how a move is shown
and suggested, the moves to try at a sequent, and the tactic `kmove`
(`apply_move` of proof-tools, fixed to system K).

Code for the editor: nothing here is trusted, and the file has no bound on
axioms.
-/
import BrunnlerK.Proof
import BrunnlerK.Show

namespace BrunnlerK

open ProofTools ProofTools.Explore

/-! ## Typing a sequent

`seq[A, B, [C, [D]], []]` is the nested sequent `A, B, [C, [D]], [∅]`: an
item in square brackets is a box, anything else a formula.  Formulas and
boxes may be mixed, as the source mixes them; the term keeps the formulas in
their order and the boxes in theirs. -/

/-- A nested sequent, written as the source writes it: formulas, and boxes
in square brackets. -/
scoped syntax "seq[" term,* "]" : term

open Lean in
scoped macro_rules
  | `(seq[$items,*]) => do
    let mut fs : Array Term := #[]
    let mut bs : Array Term := #[]
    for it in items.getElems do
      match it with
      | `([$xs,*]) => bs := bs.push (← `(seq[$xs,*]))
      | _ => fs := fs.push it
    let mut r ← `(NSeq.leaf [$fs,*])
    for b in bs.reverse do
      r ← `(NSeq.cons $b $r)
    return r

/-! ## Moves as text -/

/-- A path as it is typed: `[]`, `[0]`, `[0, 1]`. -/
def Path.show (a : Path) : String :=
  "[" ++ ", ".intercalate (a.map toString) ++ "]"

/-- A move as text, for drawings of an attempt: the rule's name in the
source, where it acts, and its main formula. -/
def Move.show : Move → String
  | .ax a p => s!"ax at {Path.show a}: {(Form.atom p).show}, {(Form.natom p).show}"
  | .and a A B => s!"∧ at {Path.show a}: {(A ⋏ B).show}"
  | .or a A B => s!"∨ at {Path.show a}: {(A ⋎ B).show}"
  | .box a A => s!"□ at {Path.show a}: {(□A).show}"
  | .dia a i A => s!"◇k_c at {Path.show a}: {(◇A).show}, into box {i}"

/-- A formula as Lean source, with the notations of `BrunnlerK.Form`.  The
propositions 0 to 7 are written `p q r s a b c d`: a file that uses the
suggested lines declares them under those names. -/
def Form.srcPrec : Form → Nat → String
  | .atom n, k => if n < 8 then propName n else
      (if k > 70 then s!"(Form.atom {n})" else s!"Form.atom {n}")
  | .natom n, k => if n < 8 then "∼" ++ propName n else
      (if k > 70 then s!"(Form.natom {n})" else s!"Form.natom {n}")
  | .or A B, k =>
    let s := A.srcPrec 65 ++ " ⋎ " ++ B.srcPrec 66
    if k > 65 then "(" ++ s ++ ")" else s
  | .and A B, k =>
    let s := A.srcPrec 70 ++ " ⋏ " ++ B.srcPrec 71
    if k > 70 then "(" ++ s ++ ")" else s
  | .dia A, _ => "◇" ++ A.srcPrec 100
  | .box A, _ => "□" ++ A.srcPrec 100

/-- A formula as Lean source, as an argument of a move. -/
def Form.src (A : Form) : String :=
  match A with
  | .natom n => if n < 8 then "(∼" ++ propName n ++ ")" else A.srcPrec 100
  | _ => A.srcPrec 100

/-- A move as it is typed after `kmove`. -/
def Move.src : Move → String
  | .ax a p => s!"ax {Path.show a} {p}"
  | .and a A B => s!"and {Path.show a} {A.src} {B.src}"
  | .or a A B => s!"or {Path.show a} {A.src} {B.src}"
  | .box a A => s!"box {Path.show a} {A.src}"
  | .dia a i A => s!"dia {Path.show a} {i} {A.src}"

/-! ## The moves to try -/

/-- The paths of the nodes inside the boxes of a sequent, its first box
numbered `k`. -/
def NSeq.boxPaths : NSeq → Nat → List Path
  | .leaf _, _ => []
  | .cons Δ r, k => ([] :: Δ.boxPaths 0).map (k :: ·) ++ r.boxPaths (k + 1)

/-- The paths of all nodes of a sequent, the root first. -/
def NSeq.paths (Γ : NSeq) : List Path := [] :: Γ.boxPaths 0

/-- The moves to try at the node `Θ` at path `a`: for each formula of the
node, the rule of its main connective; `◇k_c` into each box. -/
def nodeMoves (a : Path) (Θ : NSeq) : List Move :=
  (Θ.forms.eraseDups.map fun
    | .atom p => [Move.ax a p]
    | .natom _ => []
    | .or A B => [Move.or a A B]
    | .and A B => [Move.and a A B]
    | .box A => [Move.box a A]
    | .dia A => (List.range Θ.boxes.length).map fun i => Move.dia a i A).flatten

/-- The moves to try at a sequent: those of each of its nodes. -/
def candidates (Γ : NSeq) : List Move :=
  (Γ.paths.map fun a =>
    match Γ.node? a with
    | some Θ => nodeMoves a Θ
    | none => []).flatten

/-- The premise adds nothing to the conclusion: they have the same set
sequent (Definition 2.13).  In system K this is a `◇k_c` that puts into a
box a formula the box already has. -/
def within (Γ' Γ : NSeq) : Bool := Γ'.sameSet Γ

instance : Explorable S where
  candidates := candidates
  showJudg := NSeq.show
  showMove := Move.show
  quoteJudg := inferInstanceAs (Lean.ToExpr NSeq)
  quoteMove := inferInstanceAs (Lean.ToExpr Move)
  within := within
  moveSource m := some m.src

-- `kmove` is `apply_move`, fixed to system K.
declare_move_tactic kmove for S

end BrunnlerK
