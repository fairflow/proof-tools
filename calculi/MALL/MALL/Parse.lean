/-
A sequent read from text, for `mallrun prove '<sequent>'`; and a sequent
written with the signs of a keyboard.

The reader takes what the three printers write (`showSeq`, the source's
notation; `srcForms`, Lean source; `asciiSeq`, the signs of a keyboard):

    a sequent     formulas separated by commas, after `⊢` or `|-`, or
                  with nothing before them; in `[ … ]`, as Lean writes a
                  list; nothing, `⊢` alone, or `[]`: the empty sequent
    two-sided     `A, B ⊢ C, D` (also `|-`, `=>`, `⟹`) is read as the
                  one-sided `⊢ A⊥, B⊥, C, D`
    a letter      `p q r s`, and `a0`, `a1`, `a2`, … (`a0` is `p`, …,
                  `a3` is `s`); `Form.atom n`
    the dual      after a formula: `A⊥`, `Aᗮ`, `A^`; before one: `~A`,
                  `¬A`.  It is the function `A⊥`, so the formula read is
                  in negation normal form.  `Form.natom n`
    the units     `1` `𝟏`;  `⊥` `bot`;  `⊤` `top` `T`;  `0` `𝟎`
    `A ⊗ B`       `⊗`, `*`
    `A ⅋ B`       `⅋`, `|`, `par`
    `A & B`       `&`
    `A ⊕ B`       `⊕`, `+`
    `A ⊸ B`       `⊸`, `-o`: the formula `A⊥ ⅋ B`

`⊗` binds tighter than `&`, `&` than `⅋`, `⅋` than `⊕`, and `⊸` least; each
groups to the right.  These are the strengths of the notations of
`MALL/Form.lean` (75, 74, 72, 71), which has no sign for `⊸`.  The dual
after a formula binds closest, and `~` takes the formula that follows it,
with its duals.

**`⊥` is two things.**  Where a formula is expected it is the unit `⊥`;
after a formula it is the dual.  So `p⊥` is the dual of `p`, `⊥ ⅋ p` has
the unit, `⊥⊥` is the dual of the unit, which is `1`, and `p ⅋ ⊥⊥` is
`p ⅋ 1`.  The word `bot` is the unit only, and `^` the dual only.

A text that is not a sequent is refused with the place of the fault.  A
`Fault` counts characters from 0; the report of it, and the messages,
count from 1, as a person does.

Code: nothing here is trusted, and the file has no bound on axioms.  What
is read is printed back in the first line of the answer, and the fact the
kernel checks is stated of the sequent as it was read.
-/
import MALL.Tactic

namespace MALL

/-! ## A sequent with the signs of a keyboard -/

/-- A formula with the signs of a keyboard: `*`, `|`, `&`, `+`, `^` after
a negated letter, and `1`, `bot`, `top`, `0`.  A compound formula inside
another is in parentheses, as in `Form.showIn`. -/
def Form.asciiIn : Form → Bool → String
  | .atom n, _ => letterName n
  | .natom n, _ => letterName n ++ "^"
  | .one, _ => "1"
  | .bot, _ => "bot"
  | .top, _ => "top"
  | .zero, _ => "0"
  | .tensor A B, inner => let s := A.asciiIn true ++ " * " ++ B.asciiIn true
      if inner then "(" ++ s ++ ")" else s
  | .par A B, inner => let s := A.asciiIn true ++ " | " ++ B.asciiIn true
      if inner then "(" ++ s ++ ")" else s
  | .wth A B, inner => let s := A.asciiIn true ++ " & " ++ B.asciiIn true
      if inner then "(" ++ s ++ ")" else s
  | .plus A B, inner => let s := A.asciiIn true ++ " + " ++ B.asciiIn true
      if inner then "(" ++ s ++ ")" else s

/-- A sequent with the signs of a keyboard: `|- A, B`. -/
def asciiSeq (j : List Form) : String :=
  if j.isEmpty then "|-" else "|- " ++ ", ".intercalate (j.map fun A => A.asciiIn false)

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
  /-- A letter, by its number. -/
  | letter (n : Nat)
  /-- `Form.atom` and `Form.natom`, as the printer of Lean source writes
  the letters from 4 on. -/
  | atomK
  | natomK
  | num (n : Nat)
  | one
  | zero
  | top
  /-- The word `bot`: the unit only. -/
  | botWord
  /-- `⊥`: the unit where a formula is expected, the dual after one. -/
  | perp
  /-- `ᗮ`, `^`: the dual, after a formula. -/
  | dual
  /-- `~`, `¬`: the dual, before a formula. -/
  | neg
  | tensor
  | par
  | wth
  | plus
  | lolli
  | lpar
  | rpar
  | lbr
  | rbr
  | comma
  /-- `⊢`, `|-`, `=>`, `⟹`. -/
  | turn
  deriving DecidableEq, Repr, Inhabited

/-- A text's signs, each with its place. -/
abbrev Toks := List (Nat × Tok)

/-- A word: a letter, a unit, or `par`. -/
def wordTok (w : List Char) : Option Tok :=
  match w with
  | ['p'] => some (.letter 0)
  | ['q'] => some (.letter 1)
  | ['r'] => some (.letter 2)
  | ['s'] => some (.letter 3)
  | ['T'] => some .top
  | ['t', 'o', 'p'] => some .top
  | ['b', 'o', 't'] => some .botWord
  | ['p', 'a', 'r'] => some .par
  | 'a' :: ds =>
    if !ds.isEmpty && ds.all Char.isDigit then
      some (.letter (ds.foldl (fun n c => 10 * n + (c.toNat - 48)) 0))
    else none
  | _ => none

/-- `cs` with `pre` taken off its front, where it begins with `pre`. -/
def dropPrefix? : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | _ :: _, [] => none
  | x :: pre, c :: cs => if x == c then dropPrefix? pre cs else none

/-- The signs of more than one character. -/
def longSigns : List (List Char × Tok) :=
  [("Form.natom".toList, .natomK), ("Form.atom".toList, .atomK),
   ("|-".toList, .turn), ("=>".toList, .turn), ("-o".toList, .lolli)]

/-- The signs of one character. -/
def sign? (c : Char) : Option Tok :=
  if c == '⊗' || c == '*' then some .tensor
  else if c == '⅋' || c == '|' then some .par
  else if c == '&' then some .wth
  else if c == '⊕' || c == '+' then some .plus
  else if c == '⊸' then some .lolli
  else if c == 'ᗮ' || c == '^' then some .dual
  else if c == '~' || c == '¬' then some .neg
  else if c == '⊥' then some .perp
  else if c == '⊤' then some .top
  else if c == '𝟏' then some .one
  else if c == '𝟎' then some .zero
  else if c == '(' then some .lpar
  else if c == ')' then some .rpar
  else if c == '[' then some .lbr
  else if c == ']' then some .rbr
  else if c == ',' then some .comma
  else if c == '⊢' || c == '⟹' then some .turn
  else none

/-- The text cut into its signs. -/
partial def lexLoop (i : Nat) (cs : List Char) (acc : Array (Nat × Tok)) :
    Except Fault (Array (Nat × Tok)) :=
  match cs with
  | [] => .ok acc
  | c :: r =>
    if c.isWhitespace then lexLoop (i + 1) r acc
    else
      match longSigns.findSome? fun (pre, t) =>
          (dropPrefix? pre cs).map fun r' => (pre.length, t, r') with
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
            match wordTok w with
            | some t => lexLoop (i + w.length) (cs.dropWhile Char.isAlphanum) (acc.push (i, t))
            | none => .error ⟨i, s!"'{String.ofList w}' is not a letter: the letters are \
p q r s and a0, a1, a2, …; the words are bot, top, par"⟩
          else .error ⟨i, s!"the sign '{c}' is not one of this calculus"⟩

/-! ## The reader -/

-- A reader returns what it read and the signs that are left.

/-- The place of the first sign left; the end of the text, `n`, where
none is left. -/
def place (n : Nat) : Toks → Nat
  | (i, _) :: _ => i
  | [] => n

/-- The duals written after a formula: `⊥`, `ᗮ`, `^`, each negating what
is before it. -/
def pDuals (A : Form) : Toks → Form × Toks
  | (_, .dual) :: r => pDuals A.neg r
  | (_, .perp) :: r => pDuals A.neg r
  | ts => (A, ts)

mutual

/-- A letter, a unit or a formula in parentheses, with the duals after
it; or `~` before one. -/
partial def pUnary (n : Nat) (ts : Toks) : Except Fault (Form × Toks) :=
  match ts with
  | (_, .neg) :: r => do
    let (A, r) ← pUnary n r
    pure (A.neg, r)
  | (_, .letter k) :: r => pure (pDuals (.atom k) r)
  | (_, .atomK) :: (_, .num k) :: r => pure (pDuals (.atom k) r)
  | (_, .natomK) :: (_, .num k) :: r => pure (pDuals (.natom k) r)
  | (_, .atomK) :: r => throw ⟨place n r, "a number was expected after Form.atom"⟩
  | (_, .natomK) :: r => throw ⟨place n r, "a number was expected after Form.natom"⟩
  | (_, .one) :: r => pure (pDuals .one r)
  | (_, .num 1) :: r => pure (pDuals .one r)
  | (_, .zero) :: r => pure (pDuals .zero r)
  | (_, .num 0) :: r => pure (pDuals .zero r)
  | (i, .num _) :: _ =>
    throw ⟨i, "a formula was expected: 1 and 0 are the units, and a letter is p q r s or a0, a1, …"⟩
  | (_, .top) :: r => pure (pDuals .top r)
  | (_, .botWord) :: r => pure (pDuals .bot r)
  | (_, .perp) :: r => pure (pDuals .bot r)
  | (i, .lpar) :: r => do
    let (A, r) ← pLolli n r
    match r with
    | (_, .rpar) :: r => pure (pDuals A r)
    | [] => throw ⟨n, s!"the parenthesis opened at character {i + 1} is not closed"⟩
    | (j, _) :: _ => throw ⟨j, "a connective or a closing parenthesis was expected"⟩
  | (i, .dual) :: _ => throw ⟨i, "a formula was expected: the dual stands after a formula"⟩
  | _ => throw ⟨place n ts, "a formula was expected"⟩

/-- `A ⊗ B ⊗ …`, grouped to the right. -/
partial def pTensor (n : Nat) (ts : Toks) : Except Fault (Form × Toks) := do
  let (A, r) ← pUnary n ts
  match r with
  | (_, .tensor) :: r => do
    let (B, r) ← pTensor n r
    pure (.tensor A B, r)
  | _ => pure (A, r)

/-- `A & B & …`, grouped to the right. -/
partial def pWith (n : Nat) (ts : Toks) : Except Fault (Form × Toks) := do
  let (A, r) ← pTensor n ts
  match r with
  | (_, .wth) :: r => do
    let (B, r) ← pWith n r
    pure (.wth A B, r)
  | _ => pure (A, r)

/-- `A ⅋ B ⅋ …`, grouped to the right. -/
partial def pPar (n : Nat) (ts : Toks) : Except Fault (Form × Toks) := do
  let (A, r) ← pWith n ts
  match r with
  | (_, .par) :: r => do
    let (B, r) ← pPar n r
    pure (.par A B, r)
  | _ => pure (A, r)

/-- `A ⊕ B ⊕ …`, grouped to the right. -/
partial def pPlus (n : Nat) (ts : Toks) : Except Fault (Form × Toks) := do
  let (A, r) ← pPar n ts
  match r with
  | (_, .plus) :: r => do
    let (B, r) ← pPlus n r
    pure (.plus A B, r)
  | _ => pure (A, r)

/-- A formula: `A ⊸ B ⊸ …`, grouped to the right; `A ⊸ B` is `A⊥ ⅋ B`. -/
partial def pLolli (n : Nat) (ts : Toks) : Except Fault (Form × Toks) := do
  let (A, r) ← pPlus n ts
  match r with
  | (_, .lolli) :: r => do
    let (B, r) ← pLolli n r
    pure (.par A.neg B, r)
  | _ => pure (A, r)

end

/-- The signs end a list of formulas. -/
def endsList : Toks → Bool
  | [] => true
  | (_, .turn) :: _ => true
  | (_, .rbr) :: _ => true
  | _ => false

/-- Formulas separated by commas, after the first. -/
partial def pMore (n : Nat) (ts : Toks) (acc : Array Form) : Except Fault (List Form × Toks) :=
  match ts with
  | (_, .comma) :: r => do
    let (A, r) ← pLolli n r
    pMore n r (acc.push A)
  | _ => pure (acc.toList, ts)

/-- Formulas separated by commas, or none, up to a turnstile, a closing
bracket or the end, which is left. -/
def pList (n : Nat) (ts : Toks) : Except Fault (List Form × Toks) :=
  if endsList ts then pure ([], ts)
  else do
    let (A, r) ← pLolli n ts
    pMore n r #[A]

/-- What is wrong with a sign where a comma, a connective or the end was
expected. -/
def leftover : Tok → String
  | .rpar => "a closing parenthesis with no opening parenthesis"
  | .rbr => "a closing bracket with no opening bracket"
  | .lbr => "brackets stand only around the whole sequent"
  | .turn => "a second turnstile"
  | .neg => "a comma or a connective was expected: ~ stands before a formula"
  | _ => "a comma or a connective was expected"

/-- **A sequent read from text**, or the fault and its place.  A text
with formulas before the turnstile is two-sided: those formulas are
negated. -/
def parseSeq (s : String) : Except Fault (List Form) := do
  let cs := s.toList
  let n := cs.length
  let ts := (← lexLoop 0 cs #[]).toList
  match ts with
  | (i, .lbr) :: ts =>
    let (Γ, r) ← pList n ts
    match r with
    | [(_, .rbr)] => pure Γ
    | [] => throw ⟨n, s!"the bracket opened at character {i + 1} is not closed"⟩
    | (_, .rbr) :: (j, _) :: _ => throw ⟨j, "the text goes on after the sequent"⟩
    | (j, .turn) :: _ => throw ⟨j, "a turnstile inside brackets"⟩
    | (j, t) :: _ => throw ⟨j, leftover t⟩
  | _ =>
    let (Γ, r) ← pList n ts
    match r with
    | [] => pure Γ
    | (_, .turn) :: r =>
      let (Δ, r) ← pList n r
      match r with
      | [] => pure (Γ.map Form.neg ++ Δ)
      | (j, t) :: _ => throw ⟨j, leftover t⟩
    | (j, t) :: _ => throw ⟨j, leftover t⟩

/-- A fault as the command reports it: what is wrong and at which
character, the first being 1; the text; and a mark under the place,
counted in characters. -/
def Fault.report (f : Fault) (s : String) : String :=
  let line := String.ofList (s.toList.map fun c => if c == '\n' || c == '\t' then ' ' else c)
  s!"not a sequent, at character {f.pos + 1}: {f.msg}\n  {line}\n  \
{String.ofList (List.replicate f.pos ' ')}^"

end Parse

end MALL
