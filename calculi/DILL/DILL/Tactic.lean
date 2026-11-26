/-
The editor's part of the DILL instance: how a sequent and a move are
written, the moves to try, and the tactic `dillmove`.

Code, not theory: nothing here is trusted, and the file carries no bound
on axioms.
-/
import DILL.Proof

namespace DILL

open ProofTools ProofTools.Explore

/-- The name of an atom: `p q r s` for the numbers 0 to 3, then `a4`,
`a5`, … -/
def atomName (n : Nat) : String :=
  match n with
  | 0 => "p" | 1 => "q" | 2 => "r" | 3 => "s"
  | n => "a" ++ toString n

/-- A formula as text, in the source's notation.  A formula with a binary
connective inside another formula is in parentheses; `!` binds closest.
`inner` says whether this one is inside another. -/
def Form.showIn : Form → Bool → String
  | .atom n, _ => atomName n
  | .one, _ => "1"
  | .top, _ => "⊤"
  | .zero, _ => "0"
  | .tensor A B, inner => let s := A.showIn true ++ " ⊗ " ++ B.showIn true
      if inner then "(" ++ s ++ ")" else s
  | .lolli A B, inner => let s := A.showIn true ++ " ⊸ " ++ B.showIn true
      if inner then "(" ++ s ++ ")" else s
  | .wth A B, inner => let s := A.showIn true ++ " & " ++ B.showIn true
      if inner then "(" ++ s ++ ")" else s
  | .plus A B, inner => let s := A.showIn true ++ " ⊕ " ++ B.showIn true
      if inner then "(" ++ s ++ ")" else s
  | .bang A, _ => "!" ++ A.showIn true

/-- A formula as text. -/
def Form.show (A : Form) : String := A.showIn false

/-- A zone as text: its formulas with commas, `·` where it is empty. -/
def showZone (Γ : List Form) : String :=
  if Γ.isEmpty then "·" else ", ".intercalate (Γ.map Form.show)

/-- A sequent as text: `Γ ; Δ ⟹ C`, as the source writes it. -/
def showSeq (j : Seq) : String :=
  showZone j.unr ++ " ; " ++ showZone j.lin ++ " ⟹ " ++ j.goal.show

/-- A list of formulas as text, in brackets. -/
def showList (Γ : List Form) : String := "[" ++ ", ".intercalate (Γ.map Form.show) ++ "]"

/-- A move as text: the source's name of the rule, its principal formula,
and for the rules that divide the linear zone, the part that goes to the
first premise. -/
def Move.show : Move → String
  | .init => "init"
  | .copy A => "copy " ++ A.showIn true
  | .tensorL A B => "⊗L " ++ (A ⊗ B).show
  | .tensorR A B Δ => "⊗R " ++ (A ⊗ B).show ++ " " ++ showList Δ
  | .oneL => "1L"
  | .oneR => "1R"
  | .lolliL A B Δ => "⊸L " ++ (A ⊸ B).show ++ " " ++ showList Δ
  | .lolliR A B => "⊸R " ++ (A ⊸ B).show
  | .withL₁ A B => "&L₁ " ++ (A & B).show
  | .withL₂ A B => "&L₂ " ++ (A & B).show
  | .withR A B => "&R " ++ (A & B).show
  | .topR => "⊤R"
  | .zeroL => "0L"
  | .plusL A B => "⊕L " ++ (A ⊕ B).show
  | .plusR₁ A B => "⊕R₁ " ++ (A ⊕ B).show
  | .plusR₂ A B => "⊕R₂ " ++ (A ⊕ B).show
  | .bangL A => "!L " ++ (!A).show
  | .bangR A => "!R " ++ (!A).show
  | .cut A Δ => "cut " ++ A.showIn true ++ " " ++ showList Δ
  | .cutU A => "cut! " ++ A.showIn true

/-- A formula as Lean source, with the notations of `DILL.Form`.  The
atoms 0 to 3 are written `p q r s`: a file that uses the suggested lines
declares them under those names.  `!A` inside anything is `(!A)`: core
Lean's `!` would otherwise take what follows. -/
def Form.srcIn : Form → Bool → String
  | .atom n, inner => if n < 4 then atomName n else
      (if inner then s!"(Form.atom {n})" else s!"Form.atom {n}")
  | .one, _ => "𝟏"
  | .top, _ => "⊤"
  | .zero, _ => "𝟎"
  | .tensor A B, inner => let s := A.srcIn true ++ " ⊗ " ++ B.srcIn true
      if inner then "(" ++ s ++ ")" else s
  | .lolli A B, inner => let s := A.srcIn true ++ " ⊸ " ++ B.srcIn true
      if inner then "(" ++ s ++ ")" else s
  | .wth A B, inner => let s := A.srcIn true ++ " & " ++ B.srcIn true
      if inner then "(" ++ s ++ ")" else s
  | .plus A B, inner => let s := A.srcIn true ++ " ⊕ " ++ B.srcIn true
      if inner then "(" ++ s ++ ")" else s
  | .bang A, inner => if inner then "(!" ++ A.srcIn true ++ ")" else "!" ++ A.srcIn true

/-- A formula as an argument of a move, in Lean source. -/
def Form.src (A : Form) : String := A.srcIn true

/-- A list of formulas, in Lean source. -/
def srcForms (Γ : List Form) : String :=
  "[" ++ ", ".intercalate (Γ.map fun A => A.srcIn false) ++ "]"

/-- A move as it is typed after the tactic's name. -/
def Move.src : Move → String
  | .init => "init"
  | .copy A => s!"copy {A.src}"
  | .tensorL A B => s!"tensorL {A.src} {B.src}"
  | .tensorR A B Δ => s!"tensorR {A.src} {B.src} {srcForms Δ}"
  | .oneL => "oneL"
  | .oneR => "oneR"
  | .lolliL A B Δ => s!"lolliL {A.src} {B.src} {srcForms Δ}"
  | .lolliR A B => s!"lolliR {A.src} {B.src}"
  | .withL₁ A B => s!"withL₁ {A.src} {B.src}"
  | .withL₂ A B => s!"withL₂ {A.src} {B.src}"
  | .withR A B => s!"withR {A.src} {B.src}"
  | .topR => "topR"
  | .zeroL => "zeroL"
  | .plusL A B => s!"plusL {A.src} {B.src}"
  | .plusR₁ A B => s!"plusR₁ {A.src} {B.src}"
  | .plusR₂ A B => s!"plusR₂ {A.src} {B.src}"
  | .bangL A => s!"bangL {A.src}"
  | .bangR A => s!"bangR {A.src}"
  | .cut A Δ => s!"cut {A.src} {srcForms Δ}"
  | .cutU A => s!"cutU {A.src}"

/-- The sublists of a list: every way to keep some of its members, in
order. -/
def sublists : List Form → List (List Form)
  | [] => [[]]
  | A :: Γ => let r := sublists Γ; r ++ r.map (A :: ·)

/-- **The moves to try at a sequent**, the rules that lose nothing first
(CCP Lemma 6): the rules with nothing to name; ⊸R and &R; ⊗L, ⊕L and !L
at each formula of the linear zone; then the choices: ⊕R₁, ⊕R₂, !R, and
⊗R once for each part of the linear zone; &L₁, &L₂, and ⊸L once for each
part of the rest; last, a copy of each valid hypothesis.  (2ⁿ divisions,
less the repetitions.)  No cut is proposed: its formula is not in the
sequent.  More than can apply; those that do not are dropped by the
library. -/
def candidates (j : Seq) : List Move :=
  [Move.init, Move.oneR, Move.topR, Move.zeroL, Move.oneL] ++
  (match j.goal with
    | .lolli A B => [Move.lolliR A B]
    | .wth A B => [Move.withR A B]
    | _ => []) ++
  (j.lin.eraseDups.flatMap fun C =>
    match C with
    | .tensor A B => [Move.tensorL A B]
    | .plus A B => [Move.plusL A B]
    | .bang A => [Move.bangL A]
    | _ => []) ++
  (match j.goal with
    | .plus A B => [Move.plusR₁ A B, Move.plusR₂ A B]
    | .bang A => [Move.bangR A]
    | .tensor A B => (sublists j.lin).eraseDups.map fun Δ => Move.tensorR A B Δ
    | _ => []) ++
  (j.lin.eraseDups.flatMap fun C =>
    match C with
    | .wth A B => [Move.withL₁ A B, Move.withL₂ A B]
    | .lolli A B => (sublists (j.lin.erase C)).eraseDups.map fun Δ => Move.lolliL A B Δ
    | _ => []) ++
  (j.unr.eraseDups.map fun A => Move.copy A)

instance : Explorable S where
  candidates := candidates
  showJudg := showSeq
  showMove := Move.show
  quoteJudg := inferInstanceAs (Lean.ToExpr Seq)
  quoteMove := inferInstanceAs (Lean.ToExpr Move)
  moveSource m := some m.src

-- `dillmove` is `apply_move`, fixed to DILL.
declare_move_tactic dillmove for S

end DILL
