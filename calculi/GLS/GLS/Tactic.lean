/-
The editor's part of the GLS instance: how a sequent and a move are
written, the moves to try, and the tactic `glsmove`.

Code, not theory: nothing here is trusted, and the file carries no bound
on axioms.
-/
import GLS.Proof

namespace GLS

open ProofTools ProofTools.Explore

/-- The name of a variable: `p q r s` for the numbers 0 to 3, then `p4`,
`p5`, … -/
def varName (n : Nat) : String :=
  match n with
  | 0 => "p" | 1 => "q" | 2 => "r" | 3 => "s"
  | n => "p" ++ toString n

/-- A formula as text, in the source's notation: `→` associates to the
right, `□` binds tightest. -/
def Form.showPrec : Form → Nat → String
  | .var n, _ => varName n
  | ⊥, _ => "⊥"
  | A ⟶ B, k =>
      let s := A.showPrec 61 ++ " → " ++ B.showPrec 60
      if k > 60 then "(" ++ s ++ ")" else s
  | □A, _ => "□" ++ A.showPrec 100

/-- A formula as text. -/
def Form.show (A : Form) : String := A.showPrec 0

/-- A list of formulas as text, with commas. -/
def showForms (Γ : List Form) : String := ", ".intercalate (Γ.map Form.show)

/-- A sequent as text: `Γ ⇒ Δ`. -/
def Seq.show (j : Seq) : String :=
  (if j.ant.isEmpty then "" else showForms j.ant ++ " ") ++ "⇒" ++
    (if j.suc.isEmpty then "" else " " ++ showForms j.suc)

/-- A move as text: the source's name of the rule, and its principal
formula. -/
def Move.show : Move → String
  | .idP p => "IdP " ++ varName p
  | .botL => "BotL"
  | .impR A B => "ImpR " ++ (A ⟶ B).show
  | .impL A B => "ImpL " ++ (A ⟶ B).show
  | .glr A => "GLR " ++ (□A).show

/-- A formula as Lean source, with the notations of `GLS.Form`.  The
variables 0 to 3 are written `p q r s`: a file that uses the suggested
lines declares them under those names. -/
def Form.srcPrec : Form → Nat → String
  | .var n, k => if n < 4 then varName n else
      (if k > 60 then s!"(Form.var {n})" else s!"Form.var {n}")
  | ⊥, _ => "⊥"
  | A ⟶ B, k =>
      let s := A.srcPrec 61 ++ " ⟶ " ++ B.srcPrec 60
      if k > 60 then "(" ++ s ++ ")" else s
  | □A, _ => "□" ++ A.srcPrec 100

/-- A formula as an argument of a move, in Lean source. -/
def Form.src (A : Form) : String := A.srcPrec 100

/-- A move as it is typed after the tactic's name. -/
def Move.src : Move → String
  | .idP p => s!"idP {p}"
  | .botL => "botL"
  | .impR A B => s!"impR {A.src} {B.src}"
  | .impL A B => s!"impL {A.src} {B.src}"
  | .glr A => s!"glr {A.src}"

/-- **The moves to try at a sequent**: IdP for each variable of the
antecedent, BotL, ImpR for each implication of the succedent, ImpL for
each of the antecedent, GLR for each boxed formula of the succedent.
More than can apply; those that do not are dropped by the library. -/
def candidates (j : Seq) : List Move :=
  (j.ant.filterMap fun A => match A with | .var p => some (Move.idP p) | _ => none).eraseDups ++
  [Move.botL] ++
  (j.suc.filterMap fun A => match A with | A ⟶ B => some (Move.impR A B) | _ => none).eraseDups ++
  (j.ant.filterMap fun A => match A with | A ⟶ B => some (Move.impL A B) | _ => none).eraseDups ++
  (j.suc.filterMap fun A => match A with | □A => some (Move.glr A) | _ => none).eraseDups

instance : Explorable S where
  candidates := candidates
  showJudg := Seq.show
  showMove := Move.show
  quoteJudg := inferInstanceAs (Lean.ToExpr Seq)
  quoteMove := inferInstanceAs (Lean.ToExpr Move)
  moveSource m := some m.src

-- `glsmove` is `apply_move`, fixed to GLS.
declare_move_tactic glsmove for S

end GLS
