/-
A sequent read from text, for `dillrun prove` (`Main.lean`), and a
sequent written with the signs of a keyboard.

    sequent  ::=  zone ; zone => formula   |   zone => formula
    zone     ::=  formula , … , formula    |   .   |   (nothing)
    formula  ::=  p q r s  a4 a5 …  1  0  T
               |  ! A  |  A * B  |  A & B  |  A + B  |  A -o B  |  ( A )

`*` is ⊗, `-o` is ⊸, `+` is ⊕, `T` (or `top`) is ⊤, `=>` (or `|-`) is ⟹,
`.` is the empty zone.  The signs of the source (`⊗ ⊸ ⊕ ⊤ ⟹ ·`, and `⨾`
for `;`) are read as well, so what `showSeq` writes is read back.  With
no `;` the zone given is the linear one and the unrestricted zone is
empty.  The connectives bind as the notations of `DILL/Form.lean` do: `!`
closest, then `*`, `&`, `+`, `-o`, each to the right.

Code, not theory: nothing here is trusted, and the file carries no bound
on axioms.  A sequent misread is a wrong question, not a wrong answer:
`dillrun prove` prints the sequent it read.
-/
import DILL.Tactic

namespace DILL.Parse

/-- The signs of the text. -/
inductive Tok where
  | id (s : String)
  | one | zero | top
  | lp | rp | comma | semi | turn | dot
  | tensor | wth | plus | lolli | bang
  deriving DecidableEq, Repr, Inhabited

/-- A sign as the messages name it. -/
def Tok.show : Tok → String
  | .id s => s
  | .one => "1" | .zero => "0" | .top => "T"
  | .lp => "(" | .rp => ")" | .comma => "," | .semi => ";" | .turn => "=>" | .dot => "."
  | .tensor => "*" | .wth => "&" | .plus => "+" | .lolli => "-o" | .bang => "!"

/-- The signs of a text, each with the number of the character at which
it starts. -/
partial def lex (cs : List Char) (i : Nat) (acc : List (Tok × Nat)) :
    Except String (List (Tok × Nat)) :=
  match cs with
  | [] => .ok acc.reverse
  | c :: rest =>
    if c.isWhitespace then lex rest (i + 1) acc
    else
      let one (t : Tok) := lex rest (i + 1) ((t, i) :: acc)
      let two (t : Tok) := lex (rest.drop 1) (i + 2) ((t, i) :: acc)
      match c, rest with
      | '(', _ => one .lp
      | ')', _ => one .rp
      | ',', _ => one .comma
      | ';', _ => one .semi
      | '⨾', _ => one .semi
      | '=', '>' :: _ => two .turn
      | '|', '-' :: _ => two .turn
      | '⟹', _ => one .turn
      | '-', 'o' :: _ => two .lolli
      | '⊸', _ => one .lolli
      | '*', _ => one .tensor
      | '⊗', _ => one .tensor
      | '&', _ => one .wth
      | '+', _ => one .plus
      | '⊕', _ => one .plus
      | '!', _ => one .bang
      | '1', _ => one .one
      | '𝟏', _ => one .one
      | '0', _ => one .zero
      | '𝟎', _ => one .zero
      | '⊤', _ => one .top
      | '.', _ => one .dot
      | '·', _ => one .dot
      | _, _ =>
        if c.isAlpha then
          let w := cs.takeWhile fun d => d.isAlphanum
          let t : Tok := if w == ['T'] || w == "top".toList then .top else .id (String.ofList w)
          lex (cs.drop w.length) (i + w.length) ((t, i) :: acc)
        else .error s!"character {i + 1}: '{c}' is not a sign of a sequent"

/-- The atom that a name is: `p q r s`, and `a<n>`. -/
def atomOf (s : String) : Option Nat :=
  match s with
  | "p" => some 0 | "q" => some 1 | "r" => some 2 | "s" => some 3
  | _ =>
    match s.toList with
    | 'a' :: ds => if !ds.isEmpty && ds.all Char.isDigit then (String.ofList ds).toNat? else none
    | _ => none

/-- An infix connective: how closely it binds, and what it makes. -/
def infixOf : Tok → Option (Nat × (Form → Form → Form))
  | .lolli => some (70, .lolli)
  | .plus => some (72, .plus)
  | .wth => some (74, .wth)
  | .tensor => some (75, .tensor)
  | _ => none

/-- Where a list of signs starts, for a message. -/
def place : List (Tok × Nat) → String
  | (t, i) :: _ => s!"character {i + 1}, at '{t.show}'"
  | [] => "the end"

mutual

/-- A formula with no infix connective outside parentheses. -/
partial def prim (ts : List (Tok × Nat)) : Except String (Form × List (Tok × Nat)) :=
  match ts with
  | (.id s, i) :: ts =>
    match atomOf s with
    | some n => .ok (.atom n, ts)
    | none => .error s!"character {i + 1}: '{s}' is not an atom (the atoms are p q r s, then a4, a5, …)"
  | (.one, _) :: ts => .ok (.one, ts)
  | (.zero, _) :: ts => .ok (.zero, ts)
  | (.top, _) :: ts => .ok (.top, ts)
  | (.bang, _) :: ts => do
    let (A, ts) ← prim ts
    return (.bang A, ts)
  | (.lp, i) :: ts => do
    let (A, ts) ← form 0 ts
    match ts with
    | (.rp, _) :: ts => return (A, ts)
    | _ => throw s!"{place ts}: ')' expected, for the '(' at character {i + 1}"
  | _ => .error s!"{place ts}: a formula expected"

/-- `A`, then the infix connectives that bind at least as closely as
`min`, each with what is to its right. -/
partial def more (min : Nat) (A : Form) (ts : List (Tok × Nat)) :
    Except String (Form × List (Tok × Nat)) :=
  match ts with
  | (t, _) :: ts' =>
    match infixOf t with
    | some (pr, mk) =>
      if pr ≥ min then do
        let (B, ts'') ← form pr ts'
        more min (mk A B) ts''
      else .ok (A, ts)
    | none => .ok (A, ts)
  | [] => .ok (A, [])

/-- A formula whose outer connectives bind at least as closely as `min`. -/
partial def form (min : Nat) (ts : List (Tok × Nat)) : Except String (Form × List (Tok × Nat)) := do
  let (A, ts) ← prim ts
  more min A ts

end

/-- Formulas with commas between them, one at least. -/
partial def forms (ts : List (Tok × Nat)) : Except String (List Form × List (Tok × Nat)) := do
  let (A, ts) ← form 0 ts
  match ts with
  | (.comma, _) :: ts =>
    let (Γ, ts) ← forms ts
    return (A :: Γ, ts)
  | _ => return ([A], ts)

/-- A zone: `.`, or nothing before `;` or `=>`, or formulas. -/
def zone (ts : List (Tok × Nat)) : Except String (List Form × List (Tok × Nat)) :=
  match ts with
  | (.dot, _) :: ts => .ok ([], ts)
  | (.semi, _) :: _ => .ok ([], ts)
  | (.turn, _) :: _ => .ok ([], ts)
  | _ => forms ts

/-- **A sequent, read.**  The answer is the sequent, or what is wrong
with the text and where. -/
def seq (text : String) : Except String Seq := do
  let ts ← lex text.toList 0 []
  let (Γ, ts) ← zone ts
  let goal (unr lin : List Form) (ts : List (Tok × Nat)) : Except String Seq := do
    let (C, ts) ← form 0 ts
    match ts with
    | [] => return unr ⨾ lin ⟹ C
    | _ => throw s!"{place ts}: the sequent has ended (one conclusion, and no comma in it)"
  match ts with
  | (.semi, _) :: ts =>
    let (Δ, ts) ← zone ts
    match ts with
    | (.turn, _) :: ts => goal Γ Δ ts
    | _ => throw s!"{place ts}: '=>' expected"
  | (.turn, _) :: ts => goal [] Γ ts
  | _ => throw s!"{place ts}: ';' or '=>' expected"

/-! ## Written with the signs of a keyboard -/

/-- A formula with `* & + -o T` for `⊗ & ⊕ ⊸ ⊤`.  `inner` says whether it
is inside another. -/
def asciiIn : Form → Bool → String
  | .atom n, _ => atomName n
  | .one, _ => "1"
  | .top, _ => "T"
  | .zero, _ => "0"
  | .tensor A B, inner => let s := asciiIn A true ++ " * " ++ asciiIn B true
      if inner then "(" ++ s ++ ")" else s
  | .lolli A B, inner => let s := asciiIn A true ++ " -o " ++ asciiIn B true
      if inner then "(" ++ s ++ ")" else s
  | .wth A B, inner => let s := asciiIn A true ++ " & " ++ asciiIn B true
      if inner then "(" ++ s ++ ")" else s
  | .plus A B, inner => let s := asciiIn A true ++ " + " ++ asciiIn B true
      if inner then "(" ++ s ++ ")" else s
  | .bang A, _ => "!" ++ asciiIn A true

/-- A zone: `.` where it is empty. -/
def asciiZone (Γ : List Form) : String :=
  if Γ.isEmpty then "." else ", ".intercalate (Γ.map fun A => asciiIn A false)

/-- A sequent as `seq` reads it, with no sign outside ASCII. -/
def asciiSeq (j : Seq) : String :=
  asciiZone j.unr ++ " ; " ++ asciiZone j.lin ++ " => " ++ asciiIn j.goal false

end DILL.Parse
