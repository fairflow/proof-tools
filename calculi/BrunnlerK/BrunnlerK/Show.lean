/-
Formulas and nested sequents as text, in the source's notation.

Code for the editor: nothing here is trusted, and the file has no bound
on axioms.
-/
import BrunnlerK.Sequent

namespace BrunnlerK

/-- The name a proposition is shown under: `p q r s a b c d` for the
first eight, then `p8`, `p9`, …  (The source writes `p` for a proposition
and uses `a`, `b` in its example.) -/
def propName (n : Nat) : String :=
  match ["p", "q", "r", "s", "a", "b", "c", "d"][n]? with
  | some s => s
  | none => s!"p{n}"

private def paren (b : Bool) (s : String) : String :=
  if b then "(" ++ s ++ ")" else s

/-- A formula as the source writes it: `∨`, `∧`, `◇`, `□`, and a bar over
a negated proposition.  The second argument is the binding strength of
what surrounds it. -/
def Form.showPrec : Form → Nat → String
  | .atom n, _ => propName n
  | .natom n, _ => propName n ++ "̄"
  | .or A B, k => paren (k > 65) (A.showPrec 65 ++ " ∨ " ++ B.showPrec 66)
  | .and A B, k => paren (k > 70) (A.showPrec 70 ++ " ∧ " ++ B.showPrec 71)
  | .dia A, _ => "◇" ++ A.showPrec 100
  | .box A, _ => "□" ++ A.showPrec 100

/-- A formula as text. -/
def Form.show (A : Form) : String := A.showPrec 0

/-- The members of a sequent as texts: its formulas, then its boxes, each
box in brackets with the empty sequent written `∅`. -/
def NSeq.showItems : NSeq → List String
  | .leaf fs => fs.map Form.show
  | .cons Δ r =>
    r.showItems.take r.forms.length
      ++ ("[" ++ (match Δ.showItems with
                  | [] => "∅"
                  | xs => ", ".intercalate xs) ++ "]")
      :: r.showItems.drop r.forms.length

/-- A nested sequent as the source displays it: `A₁, …, Aₘ, [Δ₁], …, [Δₙ]`.
The empty sequent is `∅`. -/
def NSeq.show (Γ : NSeq) : String :=
  match Γ.showItems with
  | [] => "∅"
  | xs => ", ".intercalate xs

end BrunnlerK
