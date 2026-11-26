/-
A sequent read from text, for `glsrun prove '<sequent>'`; and a sequent
written as Lean source, and with the signs of a keyboard.

The reader takes what the three printers write (`Seq.show`, the source's
notation; `Seq.src`, Lean source; `Seq.ascii`, the signs of a keyboard):

    a sequent     `Γ ⇒ Δ`: two sides, each a list of formulas separated
                  by commas, or nothing; the arrow is `⇒`, `=>`, `⊢` or
                  `|-`.  A side may stand in brackets, `[A, B] ⇒ [C]`, as
                  Lean source has it.  A text with no arrow is one
                  formula `A`, read as `⇒ A`
    a variable    `p q r s`, and `p0`, `p1`, `p2`, … (`p0` is `p`, …,
                  `p3` is `s`); `Form.var n`
    `⊥`           `⊥`, `bot`, `_|_`
    `A → B`       `→`, `⟶`, `⊃`, `->`
    `□A`          `□`, `[]`

and five signs that are not connectives of the calculus, whose language
is `⊥`, `→`, `□`.  The reader computes the formula each stands for, by
the definitions of `GLS/Connectives.lean` (`Form.top`, `Form.neg`,
`Form.dia`, `Form.or`, `Form.and`: the classical ones, which are the
library's and not the source's):

    `⊤`           `⊤`, `top`: the formula `⊥ → ⊥`
    `¬A`          `¬`, `~`, `∼`, `!`: the formula `A → ⊥`
    `◇A`          `◇`, `⋄`, `<>`: the formula `□(A → ⊥) → ⊥`
    `A ∨ B`       `∨`, `⋎`, `|`, `\/`: the formula `(A → ⊥) → B`
    `A ∧ B`       `∧`, `⋏`, `&`, `/\`: the formula `(A → B → ⊥) → ⊥`

`→` groups to the right, and `□` takes the formula that follows it, a
variable or one in parentheses: the strengths of the notations of
`GLS/Form.lean` (`⟶` is `infixr:60`, `□` is `prefix:max`).  `∧` binds
tighter than `∨`, and `∨` tighter than `→`; `∧` and `∨` group to the
left: the strengths of `⋏` (`infixl:65`) and `⋎` (`infixl:64`) in
`GLS/Connectives.lean`.  `¬` and `◇` have no notation there; here they
bind as `□` does.

**`[]` is two things.**  Before a formula it is `□`.  Before the arrow or
the end of the text it is a side with nothing in it, as Lean source
writes it.  So `[]p ⇒ q` is the sequent `□p ⇒ q`, `[] ⇒ []p` is `⇒ □p`,
and `[[]p] ⇒ [q]` is `□p ⇒ q`.  A bracket that is not `[]` opens a list,
and only at the start of a side.

A text that is not a sequent is refused with the place of the fault.  A
`Fault` counts characters from 0; the report of it, and the messages,
count from 1, as a person does.

Code: nothing here is trusted, and the file has no bound on axioms.  What
is read is printed back in the first line of the answer, and the fact the
kernel checks is stated of the sequent as it was read.
-/
import GLS.Tactic
import GLS.Connectives

namespace GLS

/-! ## A sequent as Lean source -/

/-- A list of formulas as Lean source. -/
def srcForms (Γ : List Form) : String :=
  "[" ++ ", ".intercalate (Γ.map fun A => A.srcPrec 0) ++ "]"

/-- A sequent as Lean source, with the notations of `GLS/Form.lean`.  The
variables 0 to 3 are written `p q r s`: a file that uses the text declares
them. -/
def Seq.src (j : Seq) : String := srcForms j.ant ++ " ⇒ " ++ srcForms j.suc

/-! ## A sequent with the signs of a keyboard -/

/-- A formula with the signs of a keyboard: `->`, `[]`, `bot`.  The second
argument is the binding strength of what surrounds it, as in
`Form.showPrec`. -/
def Form.asciiPrec : Form → Nat → String
  | .var n, _ => varName n
  | ⊥, _ => "bot"
  | A ⟶ B, k =>
      let s := A.asciiPrec 61 ++ " -> " ++ B.asciiPrec 60
      if k > 60 then "(" ++ s ++ ")" else s
  | □A, _ => "[]" ++ A.asciiPrec 100

/-- A list of formulas with the signs of a keyboard, with commas. -/
def asciiForms (Γ : List Form) : String := ", ".intercalate (Γ.map fun A => A.asciiPrec 0)

/-- A sequent with the signs of a keyboard: `Γ => Δ`. -/
def Seq.ascii (j : Seq) : String :=
  (if j.ant.isEmpty then "" else asciiForms j.ant ++ " ") ++ "=>" ++
    (if j.suc.isEmpty then "" else " " ++ asciiForms j.suc)

/-- The numbers of the variables of a formula. -/
def Form.vars : Form → List Nat
  | .var n => [n]
  | ⊥ => []
  | A ⟶ B => A.vars ++ B.vars
  | □A => A.vars

/-- The numbers of the variables of a sequent. -/
def Seq.vars (j : Seq) : List Nat := (j.ant ++ j.suc).flatMap Form.vars

/-- How deep the connectives of a formula nest. -/
def Form.depth : Form → Nat
  | .var _ => 0
  | ⊥ => 0
  | A ⟶ B => max A.depth B.depth + 1
  | □A => A.depth + 1

/-- The greatest depth of a formula of a sequent. -/
def Seq.depth (j : Seq) : Nat := ((j.ant ++ j.suc).map Form.depth).foldl max 0

namespace Parse

/-! ## Faults and signs -/

/-- A fault in a text: the place, counted in characters from 0, and what
is wrong there. -/
structure Fault where
  pos : Nat
  msg : String
  deriving Repr, Inhabited

/-- The signs of a text. -/
inductive Tok where
  /-- A variable, by its number. -/
  | var (n : Nat)
  /-- `Form.var`, as the printer of Lean source writes the variables from
  4 on. -/
  | varK
  | num (n : Nat)
  | bot
  | top
  | neg
  | and
  | or
  | imp
  | dia
  | box
  | lpar
  | rpar
  | lbr
  | rbr
  | comma
  /-- The arrow of a sequent. -/
  | arrow
  deriving DecidableEq, Repr, Inhabited

/-- A text's signs, each with its place. -/
abbrev Toks := List (Nat × Tok)

/-- The sign of a word: a variable by its name, `bot`, `top`. -/
def wordSign : List Char → Option Tok
  | ['p'] => some (.var 0)
  | ['q'] => some (.var 1)
  | ['r'] => some (.var 2)
  | ['s'] => some (.var 3)
  | ['b', 'o', 't'] => some .bot
  | ['t', 'o', 'p'] => some .top
  | 'p' :: ds =>
    if ds.all Char.isDigit then some (.var (ds.foldl (fun n c => 10 * n + (c.toNat - 48)) 0))
    else none
  | _ => none

/-- `cs` with `pre` taken off its front, where it begins with `pre`. -/
def dropPrefix? : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | _ :: _, [] => none
  | x :: pre, c :: cs => if x == c then dropPrefix? pre cs else none

/-- The signs of more than one character.  `_|_` and `|-` stand before
the sign `|` of one character, which is `∨`. -/
def longSigns : List (List Char × Tok) :=
  [("Form.var".toList, .varK), ("_|_".toList, .bot), ("|-".toList, .arrow),
   ("=>".toList, .arrow), ("/\\".toList, .and), ("\\/".toList, .or), ("->".toList, .imp),
   ("<>".toList, .dia)]

/-- The signs of one character. -/
def sign? (c : Char) : Option Tok :=
  if c == '¬' || c == '~' || c == '∼' || c == '!' then some .neg
  else if c == '∧' || c == '⋏' || c == '&' then some .and
  else if c == '∨' || c == '⋎' || c == '|' then some .or
  else if c == '→' || c == '⟶' || c == '⊃' then some .imp
  else if c == '◇' || c == '⋄' then some .dia
  else if c == '□' then some .box
  else if c == '⊥' then some .bot
  else if c == '⊤' then some .top
  else if c == '⇒' || c == '⊢' then some .arrow
  else if c == '(' then some .lpar
  else if c == ')' then some .rpar
  else if c == '[' then some .lbr
  else if c == ']' then some .rbr
  else if c == ',' then some .comma
  else none

/-- The text cut into its signs. -/
partial def lexLoop (i : Nat) (cs : List Char) (acc : Array (Nat × Tok)) :
    Except Fault (Array (Nat × Tok)) :=
  match cs with
  | [] => .ok acc
  | c :: r =>
    if c.isWhitespace then lexLoop (i + 1) r acc
    else
      match longSigns.findSome? fun (pre, t) => (dropPrefix? pre cs).map fun r' => (pre.length, t, r') with
      | some (k, t, r') => lexLoop (i + k) r' (acc.push (i, t))
      | none =>
        match sign? c with
        | some t => lexLoop (i + 1) r (acc.push (i, t))
        | none =>
          if c.isDigit then
            let ds := cs.takeWhile Char.isDigit
            lexLoop (i + ds.length) (cs.dropWhile Char.isDigit)
              (acc.push (i, .num (ds.foldl (fun n c => 10 * n + (c.toNat - 48)) 0)))
          else if c.isAlpha then
            let w := cs.takeWhile Char.isAlphanum
            match wordSign w with
            | some t => lexLoop (i + w.length) (cs.dropWhile Char.isAlphanum) (acc.push (i, t))
            | none => .error ⟨i, s!"'{String.ofList w}' is not a variable: the variables are \
p q r s and p0, p1, p2, …"⟩
          else .error ⟨i, s!"the sign '{c}' is not one of this calculus"⟩

/-! ## The reader -/

-- A reader returns what it read and the signs that are left.

/-- The place of the first sign left; the end of the text, `n`, where
none is left. -/
def place (n : Nat) : Toks → Nat
  | (i, _) :: _ => i
  | [] => n

/-- The signs begin a formula.  `[` does where it is `[]` before a
formula: the sign `□` of a keyboard. -/
partial def startsFormula : Toks → Bool
  | (_, .lbr) :: (_, .rbr) :: r => startsFormula r
  | (_, .var _) :: _ => true
  | (_, .varK) :: _ => true
  | (_, .bot) :: _ => true
  | (_, .top) :: _ => true
  | (_, .neg) :: _ => true
  | (_, .dia) :: _ => true
  | (_, .box) :: _ => true
  | (_, .lpar) :: _ => true
  | _ => false

/-- What is wrong with a sign where a comma, a connective, the arrow or
the end was expected. -/
def leftover (inList : Bool) : Tok → String
  | .rpar => "a closing parenthesis with no opening parenthesis"
  | .rbr => if inList then "a comma, a connective or the closing bracket was expected"
      else "a closing bracket with no opening bracket"
  | .lbr => "a bracket opens a list only at the start of a side of the sequent; \
before a formula, [] is □"
  | .arrow => if inList then "the bracket of the list is not closed before the arrow"
      else "a sequent has one arrow"
  | _ =>
    if inList then "a comma, a connective or the closing bracket was expected"
    else "a comma, a connective or the arrow ⇒ was expected"

mutual

/-- A variable, `⊥`, `⊤`, a formula in parentheses, or `□`, `¬`, `◇`
before one. -/
partial def pUnary (n : Nat) (ts : Toks) : Except Fault (Form × Toks) :=
  match ts with
  | (_, .neg) :: r => do
    let (A, r) ← pUnary n r
    pure (A.neg, r)
  | (_, .dia) :: r => do
    let (A, r) ← pUnary n r
    pure (A.dia, r)
  | (_, .box) :: r => do
    let (A, r) ← pUnary n r
    pure (□A, r)
  | (_, .lbr) :: (_, .rbr) :: r => do
    let (A, r) ← pUnary n r
    pure (□A, r)
  | (_, .var k) :: r => pure (.var k, r)
  | (_, .bot) :: r => pure (⊥, r)
  | (_, .top) :: r => pure (Form.top, r)
  | (_, .varK) :: (_, .num k) :: r => pure (.var k, r)
  | (_, .varK) :: r => throw ⟨place n r, "a number was expected after Form.var"⟩
  | (i, .lpar) :: r => do
    let (A, r) ← pImp n r
    match r with
    | (_, .rpar) :: r => pure (A, r)
    | [] => throw ⟨n, s!"the parenthesis opened at character {i + 1} is not closed"⟩
    | (j, _) :: _ => throw ⟨j, "a connective or a closing parenthesis was expected"⟩
  | (i, .lbr) :: _ =>
    throw ⟨i, "a formula was expected: " ++ leftover false .lbr⟩
  | _ => throw ⟨place n ts, "a formula was expected"⟩

/-- `A ∧ B ∧ …`, grouped to the left. -/
partial def pAndRest (n : Nat) (A : Form) (ts : Toks) : Except Fault (Form × Toks) :=
  match ts with
  | (_, .and) :: r => do
    let (B, r) ← pUnary n r
    pAndRest n (A.and B) r
  | _ => pure (A, ts)

partial def pAnd (n : Nat) (ts : Toks) : Except Fault (Form × Toks) := do
  let (A, r) ← pUnary n ts
  pAndRest n A r

/-- `A ∨ B ∨ …`, grouped to the left. -/
partial def pOrRest (n : Nat) (A : Form) (ts : Toks) : Except Fault (Form × Toks) :=
  match ts with
  | (_, .or) :: r => do
    let (B, r) ← pAnd n r
    pOrRest n (A.or B) r
  | _ => pure (A, ts)

partial def pOr (n : Nat) (ts : Toks) : Except Fault (Form × Toks) := do
  let (A, r) ← pAnd n ts
  pOrRest n A r

/-- A formula: `A → B → …`, grouped to the right. -/
partial def pImp (n : Nat) (ts : Toks) : Except Fault (Form × Toks) := do
  let (A, r) ← pOr n ts
  match r with
  | (_, .imp) :: r => do
    let (B, r) ← pImp n r
    pure (A ⟶ B, r)
  | _ => pure (A, r)

end

/-- Formulas separated by commas, one at least. -/
partial def pItems (n : Nat) (ts : Toks) (acc : Array Form) : Except Fault (List Form × Toks) := do
  let (A, r) ← pImp n ts
  match r with
  | (_, .comma) :: r => pItems n r (acc.push A)
  | _ => pure ((acc.push A).toList, r)

/-- A side of a sequent, up to the arrow or the end, which is left: its
formulas, and whether it stood in brackets. -/
def pSide (n : Nat) (ts : Toks) : Except Fault (List Form × Bool × Toks) :=
  match ts with
  | [] => pure ([], false, [])
  | (_, .arrow) :: _ => pure ([], false, ts)
  | (i, .lbr) :: r =>
    if startsFormula ts then do
      let (Γ, r) ← pItems n ts #[]
      pure (Γ, false, r)
    else
      match r with
      | (_, .rbr) :: r => pure ([], true, r)
      | _ => do
        let (Γ, r) ← pItems n r #[]
        match r with
        | (_, .rbr) :: r => pure (Γ, true, r)
        | [] => throw ⟨n, s!"the bracket opened at character {i + 1} is not closed"⟩
        | (j, t) :: _ => throw ⟨j, leftover true t⟩
  | _ => do
    let (Γ, r) ← pItems n ts #[]
    pure (Γ, false, r)

/-- What is wrong with a sign after a side of the sequent: `br` says that
the side stood in brackets. -/
def afterSide (br : Bool) (t : Tok) : String :=
  if br then "a list in brackets is a whole side of the sequent: the arrow ⇒ or the end \
was expected after it"
  else leftover false t

/-- **A sequent read from text**, or the fault and its place. -/
def parseSeq (s : String) : Except Fault Seq := do
  let cs := s.toList
  let n := cs.length
  let ts := (← lexLoop 0 cs #[]).toList
  if ts.isEmpty then throw ⟨n, "a sequent was expected: formulas, the arrow ⇒, formulas"⟩
  let (Γ, br, r) ← pSide n ts
  match r with
  | (_, .arrow) :: r =>
    let (Δ, br, r) ← pSide n r
    match r with
    | [] => pure (Γ ⇒ Δ)
    | (j, .arrow) :: _ => throw ⟨j, leftover false .arrow⟩
    | (j, t) :: _ => throw ⟨j, afterSide br t⟩
  | [] =>
    match Γ, br with
    | [A], false => pure ([] ⇒ [A])
    | _, _ => throw ⟨n, "the arrow ⇒ was expected: a text with no arrow is one formula A, \
read as ⇒ A"⟩
  | (j, t) :: _ => throw ⟨j, afterSide br t⟩

/-- A fault as the command reports it: what is wrong and at which
character, the first being 1; the text; and a mark under the place. -/
def Fault.report (f : Fault) (s : String) : String :=
  let line := String.ofList (s.toList.map fun c => if c == '\n' || c == '\t' then ' ' else c)
  s!"not a sequent, at character {f.pos + 1}: {f.msg}\n  {line}\n  {String.ofList (List.replicate f.pos ' ')}^"

end Parse

end GLS
