/-
A nested sequent read from text, for `ksearch prove '<sequent>'`; and a
sequent written as Lean source, and with the signs of a keyboard.

The reader takes what the three printers write (`NSeq.show`, the source's
notation; `NSeq.src`, Lean source; `NSeq.ascii`, the signs of a keyboard):

    a sequent     members separated by commas; `∅` or nothing for the
                  empty sequent; `seq[ … ]` around the whole, or not
    a box         `[ … ]`, a sequent in square brackets; `[]`, `[∅]` empty
    a proposition `p q r s a b c d`, and `p0`, `p1`, `p2`, …
                  (`p0` is `p`, …, `p7` is `d`); `Form.atom n`
    negation      `∼A`, `~A`, `¬A`, `!A`: the function `Ā`, so the formula
                  read is in negation normal form; `p̄` (the proposition
                  and U+0304), as the printer writes it; `Form.natom n`
    `A ∧ B`       `∧`, `⋏`, `&`, `/\`
    `A ∨ B`       `∨`, `⋎`, `|`, `\/`
    `A ⊃ B`       `⊃`, `→`, `->`: the formula `Ā ∨ B`
    `◇A`          `◇`, `⋄`, `<>`
    `□A`          `□`, `[]`

`∧` binds tighter than `∨`, and `∨` tighter than `⊃`; `∧` and `∨` group
to the left and `⊃` to the right; `∼`, `◇`, `□` take the formula that
follows them, a proposition or one in parentheses.  These are the
strengths of the notations of `BrunnlerK/Form.lean`.

**`[]` is two things.**  Before a formula it is `□`; before a comma, a
closing bracket or the end it is the empty box `[∅]`.  So `[]a` is `□a`,
`[[]a]` is the box `[□a]`, and `[], a` is the sequent `a, [∅]`.

A text that is not a sequent is refused with the place of the fault.  A
`Fault` counts characters from 0; the report of it, and the messages,
count from 1, as a person does.

Code: nothing here is trusted, and the file has no bound on axioms.  What
is read is printed back in the first line of the answer, and the fact the
kernel checks is stated of the sequent as it was read.
-/
import BrunnlerK.Tactic

namespace BrunnlerK

/-! ## A sequent as Lean source -/

/-- The members of a sequent as Lean source: its formulas, then its boxes
in brackets. -/
def NSeq.srcItems : NSeq → List String
  | .leaf fs => fs.map (Form.srcPrec · 0)
  | .cons Δ r =>
    r.srcItems.take r.forms.length
      ++ ("[" ++ ", ".intercalate Δ.srcItems ++ "]")
      :: r.srcItems.drop r.forms.length

/-- A sequent as Lean source, in the notation `seq[…]` of
`BrunnlerK/Tactic.lean`.  The propositions 0 to 7 are written
`p q r s a b c d`: a file that uses the text declares them. -/
def NSeq.src (Γ : NSeq) : String := "seq[" ++ ", ".intercalate Γ.srcItems ++ "]"

/-! ## A sequent with the signs of a keyboard -/

/-- A formula with the signs of a keyboard: `|`, `&`, `<>`, `[]`, and `~`
before a negated proposition.  The second argument is the binding
strength of what surrounds it, as in `Form.showPrec`. -/
def Form.asciiPrec : Form → Nat → String
  | .atom n, _ => propName n
  | .natom n, _ => "~" ++ propName n
  | .or A B, k =>
    let s := A.asciiPrec 65 ++ " | " ++ B.asciiPrec 66
    if k > 65 then "(" ++ s ++ ")" else s
  | .and A B, k =>
    let s := A.asciiPrec 70 ++ " & " ++ B.asciiPrec 71
    if k > 70 then "(" ++ s ++ ")" else s
  | .dia A, _ => "<>" ++ A.asciiPrec 100
  | .box A, _ => "[]" ++ A.asciiPrec 100

/-- The members of a sequent with the signs of a keyboard: its formulas,
then its boxes in brackets, the empty box `[]`. -/
def NSeq.asciiItems : NSeq → List String
  | .leaf fs => fs.map (Form.asciiPrec · 0)
  | .cons Δ r =>
    r.asciiItems.take r.forms.length
      ++ ("[" ++ ", ".intercalate Δ.asciiItems ++ "]")
      :: r.asciiItems.drop r.forms.length

/-- A sequent with the signs of a keyboard.  The empty sequent is written
`seq[]`, there being no sign of a keyboard for `∅`. -/
def NSeq.ascii (Γ : NSeq) : String :=
  match Γ.asciiItems with
  | [] => "seq[]"
  | xs => ", ".intercalate xs

/-- The numbers of the propositions of a formula. -/
def Form.props : Form → List Nat
  | .atom n => [n]
  | .natom n => [n]
  | .or A B => A.props ++ B.props
  | .and A B => A.props ++ B.props
  | .dia A => A.props
  | .box A => A.props

/-- The numbers of the propositions of a sequent. -/
def NSeq.props : NSeq → List Nat
  | .leaf fs => (fs.map Form.props).flatten
  | .cons Δ r => Δ.props ++ r.props

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
  /-- A proposition, by its number. -/
  | prop (n : Nat)
  /-- The bar the printer puts after a negated proposition (U+0304). -/
  | bar
  /-- `Form.atom` and `Form.natom`, as the printer of Lean source writes
  the propositions from 8 on. -/
  | atomK
  | natomK
  | num (n : Nat)
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
  /-- `∅`. -/
  | empty
  /-- `seq[`. -/
  | seqOpen
  deriving DecidableEq, Repr, Inhabited

/-- A text's signs, each with its place. -/
abbrev Toks := List (Nat × Tok)

/-- The number of a proposition, by its name. -/
def propOfName : List Char → Option Nat
  | ['p'] => some 0
  | ['q'] => some 1
  | ['r'] => some 2
  | ['s'] => some 3
  | ['a'] => some 4
  | ['b'] => some 5
  | ['c'] => some 6
  | ['d'] => some 7
  | 'p' :: ds =>
    if ds.all Char.isDigit then some (ds.foldl (fun n c => 10 * n + (c.toNat - 48)) 0)
    else none
  | _ => none

/-- `cs` with `pre` taken off its front, where it begins with `pre`. -/
def dropPrefix? : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | _ :: _, [] => none
  | x :: pre, c :: cs => if x == c then dropPrefix? pre cs else none

/-- The signs of more than one character. -/
def longSigns : List (List Char × Tok) :=
  [("seq[".toList, .seqOpen), ("Form.natom".toList, .natomK), ("Form.atom".toList, .atomK),
   ("/\\".toList, .and), ("\\/".toList, .or), ("->".toList, .imp), ("<>".toList, .dia)]

/-- The signs of one character. -/
def sign? (c : Char) : Option Tok :=
  if c == '∼' || c == '~' || c == '¬' || c == '!' then some .neg
  else if c == '∧' || c == '⋏' || c == '&' then some .and
  else if c == '∨' || c == '⋎' || c == '|' then some .or
  else if c == '⊃' || c == '→' then some .imp
  else if c == '◇' || c == '⋄' then some .dia
  else if c == '□' then some .box
  else if c == '(' then some .lpar
  else if c == ')' then some .rpar
  else if c == '[' then some .lbr
  else if c == ']' then some .rbr
  else if c == ',' then some .comma
  else if c == '∅' then some .empty
  else if c == '̄' then some .bar
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
            match propOfName w with
            | some n => lexLoop (i + w.length) (cs.dropWhile Char.isAlphanum) (acc.push (i, .prop n))
            | none => .error ⟨i, s!"'{String.ofList w}' is not a proposition: the propositions \
are p q r s a b c d and p0, p1, p2, …"⟩
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
  | (_, .prop _) :: _ => true
  | (_, .atomK) :: _ => true
  | (_, .natomK) :: _ => true
  | (_, .neg) :: _ => true
  | (_, .dia) :: _ => true
  | (_, .box) :: _ => true
  | (_, .lpar) :: _ => true
  | _ => false

/-- What is wrong with a sign where a comma, a connective or the end was
expected. -/
def leftover (inBox : Bool) : Tok → String
  | .bar => "the bar stands only after a proposition"
  | .rpar => "a closing parenthesis with no opening parenthesis"
  | .rbr => "a closing bracket with no opening bracket"
  | .seqOpen => "seq[ stands only at the start of the text"
  | .empty => "∅ is the whole of an empty sequent: nothing stands beside it"
  | _ =>
    if inBox then "a comma, a connective or a closing bracket was expected"
    else "a comma or a connective was expected"

mutual

/-- A proposition, a formula in parentheses, or `∼`, `◇`, `□` before
one. -/
partial def pUnary (n : Nat) (ts : Toks) : Except Fault (Form × Toks) :=
  match ts with
  | (_, .neg) :: r => do
    let (A, r) ← pUnary n r
    pure (A.dual, r)
  | (_, .dia) :: r => do
    let (A, r) ← pUnary n r
    pure (.dia A, r)
  | (_, .box) :: r => do
    let (A, r) ← pUnary n r
    pure (.box A, r)
  | (_, .lbr) :: (_, .rbr) :: r => do
    let (A, r) ← pUnary n r
    pure (.box A, r)
  | (_, .prop k) :: (_, .bar) :: r => pure (.natom k, r)
  | (_, .prop k) :: r => pure (.atom k, r)
  | (_, .atomK) :: (_, .num k) :: r => pure (.atom k, r)
  | (_, .natomK) :: (_, .num k) :: r => pure (.natom k, r)
  | (_, .atomK) :: r => throw ⟨place n r, "a number was expected after Form.atom"⟩
  | (_, .natomK) :: r => throw ⟨place n r, "a number was expected after Form.natom"⟩
  | (i, .lpar) :: r => do
    let (A, r) ← pImp n r
    match r with
    | (_, .rpar) :: r => pure (A, r)
    | [] => throw ⟨n, s!"the parenthesis opened at character {i + 1} is not closed"⟩
    | (j, _) :: _ => throw ⟨j, "a connective or a closing parenthesis was expected"⟩
  | (i, .lbr) :: _ =>
    throw ⟨i, "a formula was expected: a box in brackets is a member of a sequent, \
not a part of a formula"⟩
  | _ => throw ⟨place n ts, "a formula was expected"⟩

/-- `A ∧ B ∧ …`, grouped to the left. -/
partial def pAndRest (n : Nat) (A : Form) (ts : Toks) : Except Fault (Form × Toks) :=
  match ts with
  | (_, .and) :: r => do
    let (B, r) ← pUnary n r
    pAndRest n (.and A B) r
  | _ => pure (A, ts)

partial def pAnd (n : Nat) (ts : Toks) : Except Fault (Form × Toks) := do
  let (A, r) ← pUnary n ts
  pAndRest n A r

/-- `A ∨ B ∨ …`, grouped to the left. -/
partial def pOrRest (n : Nat) (A : Form) (ts : Toks) : Except Fault (Form × Toks) :=
  match ts with
  | (_, .or) :: r => do
    let (B, r) ← pAnd n r
    pOrRest n (.or A B) r
  | _ => pure (A, ts)

partial def pOr (n : Nat) (ts : Toks) : Except Fault (Form × Toks) := do
  let (A, r) ← pAnd n ts
  pOrRest n A r

/-- A formula: `A ⊃ B ⊃ …`, grouped to the right. -/
partial def pImp (n : Nat) (ts : Toks) : Except Fault (Form × Toks) := do
  let (A, r) ← pOr n ts
  match r with
  | (_, .imp) :: r => do
    let (B, r) ← pImp n r
    pure (A.imp B, r)
  | _ => pure (A, r)

end

mutual

/-- A sequent, up to a closing bracket or the end, which is left. -/
partial def pSeq (n : Nat) (ts : Toks) : Except Fault (NSeq × Toks) :=
  match ts with
  | [] => pure (.leaf [], [])
  | (_, .rbr) :: _ => pure (.leaf [], ts)
  | (_, .empty) :: r =>
    match r with
    | [] => pure (.leaf [], r)
    | (_, .rbr) :: _ => pure (.leaf [], r)
    | (j, _) :: _ => throw ⟨j, leftover false .empty⟩
  | _ => pItems n ts #[] #[]

/-- The members of a sequent that is not empty: the formulas in their
order and the boxes in theirs, as `seq[…]` keeps them. -/
partial def pItems (n : Nat) (ts : Toks) (fs : Array Form) (bs : Array NSeq) : Except Fault (NSeq × Toks) := do
  let (fs, bs, r) ←
    match ts with
    | (i, .lbr) :: r' =>
      if startsFormula ts then do
        let (A, r) ← pImp n ts
        pure (fs.push A, bs, r)
      else do
        let (Δ, r) ← pSeq n r'
        match r with
        | (_, .rbr) :: r => pure (fs, bs.push Δ, r)
        | [] => throw ⟨n, s!"the bracket opened at character {i + 1} is not closed"⟩
        | (j, t) :: _ => throw ⟨j, leftover true t⟩
    | [] => throw ⟨n, "a formula or a box was expected"⟩
    | (i, .comma) :: _ => throw ⟨i, "a formula or a box was expected"⟩
    | (i, .rbr) :: _ => throw ⟨i, "a formula or a box was expected"⟩
    | (i, .empty) :: _ => throw ⟨i, leftover false .empty⟩
    | _ => do
      let (A, r) ← pImp n ts
      pure (fs.push A, bs, r)
  match r with
  | (_, .comma) :: r => pItems n r fs bs
  | _ => pure (bs.foldr NSeq.cons (.leaf fs.toList), r)

end

/-- **A nested sequent read from text**, or the fault and its place. -/
def parseSeq (s : String) : Except Fault NSeq := do
  let cs := s.toList
  let n := cs.length
  let ts := (← lexLoop 0 cs #[]).toList
  match ts with
  | (_, .seqOpen) :: ts =>
    let (Γ, r) ← pSeq n ts
    match r with
    | [(_, .rbr)] => pure Γ
    | [] => throw ⟨n, "the bracket of seq[ is not closed"⟩
    | (_, .rbr) :: (j, _) :: _ => throw ⟨j, "the text goes on after the sequent"⟩
    | (j, t) :: _ => throw ⟨j, leftover true t⟩
  | _ =>
    let (Γ, r) ← pSeq n ts
    match r with
    | [] => pure Γ
    | (j, t) :: _ => throw ⟨j, leftover false t⟩

/-- A fault as the command reports it: what is wrong and at which
character, the first being 1; the text; and a mark under the place.  (A bar over a proposition is a character of its
own, and the mark is counted in characters.) -/
def Fault.report (f : Fault) (s : String) : String :=
  let line := String.ofList (s.toList.map fun c => if c == '\n' || c == '\t' then ' ' else c)
  s!"not a sequent, at character {f.pos + 1}: {f.msg}\n  {line}\n  {String.ofList (List.replicate f.pos ' ')}^"

end Parse

end BrunnlerK
