/-
Tests of the reader (`BrunnlerK/Parse.lean`): every entry of the corpus is
read back from what each of the three printers writes; Lean reads what
the printer of Lean source writes as the same sequent; how the
connectives and the brackets bind; texts that are refused, each with the
place of the fault.
-/
import BrunnlerK.Parse
import BrunnlerK.Corpus.Basic
import Lean

namespace BrunnlerK.Test.Parse

open BrunnlerK BrunnlerK.Parse BrunnlerK.Corpus

abbrev s : Form := .atom 3
abbrev c : Form := .atom 6
abbrev d : Form := .atom 7

/-- The text is read, as the sequent `Γ`. -/
def reads (text : String) (Γ : NSeq) : Bool :=
  match parseSeq text with
  | .ok Δ => Δ == Γ
  | .error _ => false

/-- The text is refused, with the fault at character `i`. -/
def refusedAt (text : String) (i : Nat) : Bool :=
  match parseSeq text with
  | .ok _ => false
  | .error f => f.pos == i

/-! ## The corpus, read back from each printer -/

-- 22 entries.
#guard entries.length == 22

-- From the source's notation (`NSeq.show`).
#guard entries.all fun e => reads e.seq.show e.seq

-- From Lean source (`NSeq.src`).
#guard entries.all fun e => reads e.seq.src e.seq

-- With the signs of a keyboard (`NSeq.ascii`), which are of a keyboard.
#guard entries.all fun e => reads e.seq.ascii e.seq
#guard entries.all fun e => e.seq.ascii.toList.all fun (c : Char) => c.toNat < 128

-- From the text of the entry itself, where it is a `seq[…]` and not a
-- member of a family: 18 of the 22.
#guard (entries.filter fun e => e.src.startsWith "seq[").length == 18
#guard (entries.filter fun e => e.src.startsWith "seq[").all fun e => reads e.src e.seq

-- The families, further than the corpus has them, from both printers.
#guard [boxAnd 9, nest 12, boxOr 9, late 9].all fun Γ =>
  reads Γ.show Γ && reads Γ.src Γ && reads Γ.ascii Γ

-- Boxes among formulas, the empty box beside `□`, and boxes in boxes.
#guard [(seq[□a, [], [□b, [], [[]]], ◇(∼c ⋎ d)] : NSeq), seq[[[[]]]], seq[[], []]].all fun Γ =>
  reads Γ.show Γ && reads Γ.src Γ && reads Γ.ascii Γ

-- What the printers write, for three entries, so that a change of a
-- printer is seen here.
#guard (seq[◇(∼a ⋏ ∼b), □a, ◇b] : NSeq).show == "◇(ā ∧ b̄), □a, ◇b"
#guard (seq[◇(∼a ⋏ ∼b), □a, ◇b] : NSeq).src == "seq[◇(∼a ⋏ ∼b), □a, ◇b]"
#guard (seq[[]] : NSeq).show == "[∅]"
#guard (seq[[]] : NSeq).src == "seq[[]]"
#guard (seq[] : NSeq).show == "∅"
#guard (late 1).src == "seq[r, ∼r, Form.atom 10 ⋏ (Form.atom 10)]"
#guard (late 1).show == "r, r\u0304, p10 ∧ p10"
#guard (seq[◇(∼a ⋏ ∼b), □a, ◇b] : NSeq).ascii == "<>(~a & ~b), []a, <>b"
#guard (seq[□a, [], [□b, []]] : NSeq).ascii == "[]a, [], [[]b, []]"
#guard (seq[] : NSeq).ascii == "seq[]"
#guard (late 1).ascii == "r, ~r, p10 & p10"

/-! ## Lean reads what `NSeq.src` writes as the same sequent

`ksearch prove` states its fact of `seq[…]` as `NSeq.src` writes it, and
its first line shows the sequent as `NSeq.show` writes it.  The two are
the same sequent only if Lean reads the first text as the sequent it was
written from.  Here each text is given to Lean's own parser and
elaborator, and the value compared. -/

open Lean Elab Command Term Meta in
/-- Lean's reading of a text as a term of type `NSeq`. -/
unsafe def leanReads (text : String) : TermElabM NSeq := do
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term text)
  let e ← elabTermEnsuringType stx (some (mkConst ``NSeq))
  synthesizeSyntheticMVarsNoPostponing
  evalExpr NSeq (mkConst ``NSeq) (← instantiateMVars e)

open Lean Elab Command Term Meta in
run_cmd liftTermElabM do
  let extra : List NSeq := [boxAnd 9, nest 12, boxOr 9, late 9,
    seq[□a, [], [□b, [], [[]]], ◇(∼c ⋎ d)], seq[[[[]]]], seq[s, ∼s ⋏ ∼(Form.atom 9)]]
  for Γ in entries.map (·.seq) ++ extra do
    let Δ ← unsafe leanReads Γ.src
    unless Δ == Γ do
      throwError "Lean reads {Γ.src} as another sequent than it was written from"

/-! ## The signs of a keyboard -/

#guard reads "a & b" seq[a ⋏ b]
#guard reads "a /\\ b" seq[a ⋏ b]
#guard reads "a | b" seq[a ⋎ b]
#guard reads "a \\/ b" seq[a ⋎ b]
#guard reads "a -> b" seq[a ⊃ b]
#guard reads "a → b" seq[a ⊃ b]
#guard reads "<>a, []a, ⋄a" seq[◇a, □a, ◇a]
#guard reads "~a, ¬a, !a, ∼a, ā" seq[∼a, ∼a, ∼a, ∼a, ∼a]
#guard reads "p, q, r, s, a, b, c, d" seq[p, q, r, s, a, b, c, d]
#guard reads "p0, p7, p8, p12, ~p12" seq[p, d, Form.atom 8, Form.atom 12, Form.natom 12]
#guard reads "Form.atom 12, (Form.natom 12), ◇(Form.atom 9)"
  seq[Form.atom 12, Form.natom 12, ◇(Form.atom 9)]
#guard reads "  a ,\n b  " seq[a, b]
-- The whole of the axiom k, typed on a keyboard.
#guard reads "[](a -> b) -> ([]a -> []b)" seq[□(a ⊃ b) ⊃ (□a ⊃ □b)]

/-! ## How the connectives bind -/

-- `∧` tighter than `∨`, on either side.
#guard reads "a | b & c" seq[a ⋎ (b ⋏ c)]
#guard reads "a & b | c" seq[(a ⋏ b) ⋎ c]
#guard reads "(a | b) & c" seq[(a ⋎ b) ⋏ c]
-- `∧` and `∨` group to the left.
#guard reads "a | b | c" seq[(a ⋎ b) ⋎ c]
#guard reads "a & b & c" seq[(a ⋏ b) ⋏ c]
#guard reads "a | (b | c)" seq[a ⋎ (b ⋎ c)]
#guard !reads "a | b | c" seq[a ⋎ (b ⋎ c)]
-- `⊃` weakest, and to the right.
#guard reads "a -> b -> c" seq[a ⊃ (b ⊃ c)]
#guard reads "(a -> b) -> c" seq[(a ⊃ b) ⊃ c]
#guard !reads "a -> b -> c" seq[(a ⊃ b) ⊃ c]
#guard reads "a | b -> c & d" seq[(a ⋎ b) ⊃ (c ⋏ d)]
-- `∼`, `◇`, `□` take the formula that follows them, no more.
#guard reads "~a & b" seq[(∼a) ⋏ b]
#guard reads "~(a & b)" seq[∼a ⋎ ∼b]
#guard reads "[]a | b" seq[(□a) ⋎ b]
#guard reads "[](a | b)" seq[□(a ⋎ b)]
#guard reads "<>a -> b" seq[(◇a) ⊃ b]
#guard reads "<>[]~a" seq[◇□(∼a)]
#guard reads "~[]a" seq[◇(∼a)]
#guard reads "~~a" seq[a]
-- As Lean reads the same signs.
#guard reads "a ⋎ b ⋏ c ⊃ ∼a ⋏ □b ⋎ c" seq[a ⋎ b ⋏ c ⊃ ∼a ⋏ □b ⋎ c]

/-! ## How the brackets bind -/

-- The empty sequent, four ways.
#guard reads "" seq[]
#guard reads "∅" seq[]
#guard reads "seq[]" seq[]
#guard reads "seq[∅]" seq[]
-- The empty box.
#guard reads "[]" seq[[]]
#guard reads "[∅]" seq[[]]
#guard reads "[ ]" seq[[]]
#guard reads "[[]]" seq[[[]]]
#guard reads "[], []" seq[[], []]
-- `[]` before a formula is `□`; before a comma, a bracket or the end it
-- is the empty box.
#guard reads "[]a" seq[□a]
#guard reads "[] a" seq[□a]
#guard reads "[][]a" seq[□□a]
#guard reads "[]<>[]a" seq[□◇□a]
#guard reads "[](a), []" seq[□a, []]
#guard reads "[], a" seq[a, []]
#guard reads "[[]a]" seq[[□a]]
#guard reads "[[], a]" seq[[a, []]]
#guard reads "[[]a, []]" seq[[□a, []]]
-- A box is not `□`: `[a]` is a box, `[]a` a formula.
#guard reads "[a]" (.cons (.leaf [a]) (.leaf []))
#guard !reads "[a]" seq[□a]
-- Formulas and boxes mixed: the formulas keep their order, and the boxes
-- theirs, as `seq[…]` keeps them.
#guard reads "[a], b, [c], d" seq[b, d, [a], [c]]
#guard reads "[a], b, [c], d" (.cons (.leaf [a]) (.cons (.leaf [c]) (.leaf [b, d])))
#guard reads "b, [a, [c, [d]], [s]], []" seq[b, [a, [c, [d]], [s]], []]
-- A comma separates members of a sequent, and binds less than any
-- connective.
#guard reads "a -> b, c" seq[a ⊃ b, c]
#guard reads "seq[a, [b]]" seq[a, [b]]

/-! ## Texts that are refused, and where -/

-- A member is missing.
#guard refusedAt "a," 2
#guard refusedAt ", a" 0
#guard refusedAt "a,, b" 2
#guard refusedAt "[a,]" 3
-- A formula is missing.
#guard refusedAt "a |" 3
#guard refusedAt "a & | b" 4
#guard refusedAt "<>" 2
#guard refusedAt "~" 1
#guard refusedAt "()" 1
-- Two formulas with nothing between them.
#guard refusedAt "a b" 2
#guard refusedAt "[a b]" 3
-- Parentheses and brackets that do not match.
#guard refusedAt "(a" 2
#guard refusedAt "a)" 1
#guard refusedAt "[a" 2
#guard refusedAt "a]" 1
#guard refusedAt "[a)" 2
#guard refusedAt "(a]" 2
#guard refusedAt "seq[a" 5
#guard refusedAt "seq[a] b" 7
#guard refusedAt "a, seq[b]" 3
-- A box inside a formula; an empty box before a box, with no comma.
#guard refusedAt "a | [b]" 4
#guard refusedAt "[][a]" 2
#guard refusedAt "<>[a]" 2
#guard refusedAt "[a] | b" 4
-- `∅` beside something.
#guard refusedAt "a, ∅" 3
#guard refusedAt "∅, a" 1
-- The bar after what is not a proposition.
#guard refusedAt "(a)̄" 3
#guard refusedAt "ā̄" 2
-- Names and signs that are not of this calculus.
#guard refusedAt "a | x" 4
#guard refusedAt "box a" 0
#guard refusedAt "A" 0
#guard refusedAt "a # b" 2
#guard refusedAt "a - b" 2
#guard refusedAt "a <-> b" 2
#guard refusedAt "a |- b" 3
#guard refusedAt "7" 0
#guard refusedAt "Form.atom" 9
#guard refusedAt "Form.atom a" 10

/-! ## The report of a fault

The places above are counted from 0, as a `Fault` has them; the report
counts from 1. -/

#guard (match parseSeq "b, (a" with
  | .error f => f.pos == 5 && f.msg == "the parenthesis opened at character 4 is not closed"
  | .ok _ => false)

#guard (match parseSeq "a /\\ , b" with
  | .error f => f.report "a /\\ , b" ==
      "not a sequent, at character 6: a formula was expected\n  a /\\ , b\n       ^"
  | .ok _ => false)

end BrunnlerK.Test.Parse
