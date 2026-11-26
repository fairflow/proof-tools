/-
The editor's part of the MALL instance: how a sequent and a move are
written, the moves to try, and the tactic `mallmove`.

Code, not theory: nothing here is trusted, and the file carries no bound
on axioms.
-/
import MALL.Proof

namespace MALL

open ProofTools ProofTools.Explore

/-- The name of a letter: `p q r s` for the numbers 0 to 3, then `a4`,
`a5`, … -/
def letterName (n : Nat) : String :=
  match n with
  | 0 => "p" | 1 => "q" | 2 => "r" | 3 => "s"
  | n => "a" ++ toString n

/-- A formula as text, in the source's notation.  A compound formula
inside another is in parentheses: the source gives the connectives no
precedence.  `inner` says whether this one is inside another. -/
def Form.showIn : Form → Bool → String
  | .atom n, _ => letterName n
  | .natom n, _ => letterName n ++ "⊥"
  | .one, _ => "1"
  | .bot, _ => "⊥"
  | .top, _ => "⊤"
  | .zero, _ => "0"
  | .tensor A B, inner => let s := A.showIn true ++ " ⊗ " ++ B.showIn true
      if inner then "(" ++ s ++ ")" else s
  | .par A B, inner => let s := A.showIn true ++ " ⅋ " ++ B.showIn true
      if inner then "(" ++ s ++ ")" else s
  | .wth A B, inner => let s := A.showIn true ++ " & " ++ B.showIn true
      if inner then "(" ++ s ++ ")" else s
  | .plus A B, inner => let s := A.showIn true ++ " ⊕ " ++ B.showIn true
      if inner then "(" ++ s ++ ")" else s

/-- A formula as text. -/
def Form.show (A : Form) : String := A.showIn false

/-- A list of formulas as text, with commas. -/
def showForms (Γ : List Form) : String := ", ".intercalate (Γ.map Form.show)

/-- A sequent as text: `⊢ A₁, …, Aₙ`. -/
def showSeq (j : List Form) : String :=
  if j.isEmpty then "⊢" else "⊢ " ++ showForms j

/-- A move as text: the source's name of the rule, its principal formula,
and for the rules that split, the context of the first premise. -/
def Move.show : Move → String
  | .ax A => "ax " ++ A.show
  | .cut A Γ => "cut " ++ A.showIn true ++ " [" ++ showForms Γ ++ "]"
  | .top => "⊤"
  | .wth A B => "& " ++ (A & B).show
  | .plus₁ A B => "1⊕ " ++ (A ⊕ B).show
  | .plus₂ A B => "2⊕ " ++ (A ⊕ B).show
  | .one => "1"
  | .bot => "⊥"
  | .tensor A B Γ => "⊗ " ++ (A ⊗ B).show ++ " [" ++ showForms Γ ++ "]"
  | .par A B => "⅋ " ++ (A ⅋ B).show

/-- A formula as Lean source, with the notations of `MALL.Form`.  The
letters 0 to 3 are written `p q r s`, and their duals `pᗮ`: a file that
uses the suggested lines declares them under those names. -/
def Form.srcIn : Form → Bool → String
  | .atom n, inner => if n < 4 then letterName n else
      (if inner then s!"(Form.atom {n})" else s!"Form.atom {n}")
  | .natom n, inner => if n < 4 then letterName n ++ "ᗮ" else
      (if inner then s!"(Form.natom {n})" else s!"Form.natom {n}")
  | .one, _ => "𝟏"
  | .bot, _ => "⊥"
  | .top, _ => "⊤"
  | .zero, _ => "𝟎"
  | .tensor A B, inner => let s := A.srcIn true ++ " ⊗ " ++ B.srcIn true
      if inner then "(" ++ s ++ ")" else s
  | .par A B, inner => let s := A.srcIn true ++ " ⅋ " ++ B.srcIn true
      if inner then "(" ++ s ++ ")" else s
  | .wth A B, inner => let s := A.srcIn true ++ " & " ++ B.srcIn true
      if inner then "(" ++ s ++ ")" else s
  | .plus A B, inner => let s := A.srcIn true ++ " ⊕ " ++ B.srcIn true
      if inner then "(" ++ s ++ ")" else s

/-- A formula as an argument of a move, in Lean source. -/
def Form.src (A : Form) : String := A.srcIn true

/-- A list of formulas, in Lean source. -/
def srcForms (Γ : List Form) : String :=
  "[" ++ ", ".intercalate (Γ.map fun A => A.srcIn false) ++ "]"

/-- A move as it is typed after the tactic's name. -/
def Move.src : Move → String
  | .ax A => s!"ax {A.src}"
  | .cut A Γ => s!"cut {A.src} {srcForms Γ}"
  | .top => "top"
  | .wth A B => s!"wth {A.src} {B.src}"
  | .plus₁ A B => s!"plus₁ {A.src} {B.src}"
  | .plus₂ A B => s!"plus₂ {A.src} {B.src}"
  | .one => "one"
  | .bot => "bot"
  | .tensor A B Γ => s!"tensor {A.src} {B.src} {srcForms Γ}"
  | .par A B => s!"par {A.src} {B.src}"

/-- The sublists of a list: every way to keep some of its members, in
order. -/
def sublists : List Form → List (List Form)
  | [] => [[]]
  | A :: Γ => let r := sublists Γ; r ++ r.map (A :: ·)

/-- **The moves to try at a sequent**: the axiom on its first formula, the
three rules with no formula to name, and for each formula of the sequent
the rule of its connective; for ⊗, once for each part of the rest of the
sequent (2ⁿ of them, less the repetitions).  No cut is proposed: its
formula is not in the sequent.  More than can apply; those that do not are
dropped by the library. -/
def candidates (j : List Form) : List Move :=
  (match j with | A :: _ => [Move.ax A] | [] => []) ++
  [Move.one, Move.top, Move.bot] ++
  (j.eraseDups.flatMap fun C =>
    match C with
    | .par A B => [Move.par A B]
    | .wth A B => [Move.wth A B]
    | .plus A B => [Move.plus₁ A B, Move.plus₂ A B]
    | .tensor A B => (sublists (j.erase C)).eraseDups.map fun Γ => Move.tensor A B Γ
    | _ => [])

instance : Explorable S where
  candidates := candidates
  showJudg := showSeq
  showMove := Move.show
  quoteJudg := inferInstanceAs (Lean.ToExpr (List Form))
  quoteMove := inferInstanceAs (Lean.ToExpr Move)
  moveSource m := some m.src

-- `mallmove` is `apply_move`, fixed to MALL.
declare_move_tactic mallmove for S

end MALL
