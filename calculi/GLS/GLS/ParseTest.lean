/-
Tests of the reader (`GLS/Parse.lean`): every entry of the corpus is read
back from what each of the three printers writes; Lean reads what the
printer of Lean source writes as the same sequent; how the connectives
bind; the two uses of `[]`; texts that are refused, each with the place of
the fault.
-/
import GLS.Parse
import GLS.Corpus.Basic
import GLS.SetSearch
import GLS.FastCheck
import GLS.Screen
import Lean

namespace GLS.ParseTest

open GLS GLS.Parse GLS.Corpus
open GLS.Screen (seqsSmall worlds trees2)

abbrev s : Form := .var 3

/-- The text is read, as the sequent `j`. -/
def reads (text : String) (j : Seq) : Bool :=
  match parseSeq text with
  | .ok k => k == j
  | .error _ => false

/-- The text is refused, with the fault at character `i`, counted from 0. -/
def refusedAt (text : String) (i : Nat) : Bool :=
  match parseSeq text with
  | .ok _ => false
  | .error f => f.pos == i

/-! ## The corpus, read back from each printer -/

-- 16 entries.
#guard entries.length == 16

-- From the source's notation (`Seq.show`).
#guard entries.all fun e => reads e.seq.show e.seq

-- From Lean source (`Seq.src`), which is the text the corpus keeps.
#guard entries.all fun e => reads e.seq.src e.seq
#guard entries.all fun e => e.src == e.seq.src

-- With the signs of a keyboard (`Seq.ascii`), which are of a keyboard.
#guard entries.all fun e => reads e.seq.ascii e.seq
#guard entries.all fun e => e.seq.ascii.toList.all fun (c : Char) => c.toNat < 128

/-- Members of the four families, further than `glsrun families` lists
them, and sequents with formulas on both sides, with none, and with
variables from 4 on. -/
def extra : List Seq :=
  [boxChain 9, kChain 9, consis 9, binTree 3,
   [□(p ⟶ q), □p, ⊥ ⟶ r] ⇒ [□q, s, (p ⟶ q) ⟶ r],
   [] ⇒ [], [p] ⇒ [], [] ⇒ [p], [□□p] ⇒ [],
   [Form.var 4 ⟶ Form.var 12, □(Form.var 4)] ⇒ [Form.var 12, (Form.var 5 ⟶ ⊥) ⟶ Form.var 6]]

#guard extra.all fun j => reads j.show j && reads j.src j && reads j.ascii j

-- What the printers write, so that a change of a printer is seen here.
#guard ([□(p ⟶ q), □p] ⇒ [□q, ⊥] : Seq).show == "□(p → q), □p ⇒ □q, ⊥"
#guard ([□(p ⟶ q), □p] ⇒ [□q, ⊥] : Seq).src == "[□(p ⟶ q), □p] ⇒ [□q, ⊥]"
#guard ([□(p ⟶ q), □p] ⇒ [□q, ⊥] : Seq).ascii == "[](p -> q), []p => []q, bot"
#guard ([] ⇒ [(p ⟶ q) ⟶ r] : Seq).show == "⇒ (p → q) → r"
#guard ([] ⇒ [(p ⟶ q) ⟶ r] : Seq).src == "[] ⇒ [(p ⟶ q) ⟶ r]"
#guard ([] ⇒ [(p ⟶ q) ⟶ r] : Seq).ascii == "=> (p -> q) -> r"
#guard ([] ⇒ [] : Seq).show == "⇒"
#guard ([] ⇒ [] : Seq).src == "[] ⇒ []"
#guard ([] ⇒ [] : Seq).ascii == "=>"
#guard ([□(Form.var 4)] ⇒ [Form.var 4 ⟶ Form.var 5] : Seq).show == "□p4 ⇒ p4 → p5"
#guard ([□(Form.var 4)] ⇒ [Form.var 4 ⟶ Form.var 5] : Seq).src
  == "[□(Form.var 4)] ⇒ [(Form.var 4) ⟶ Form.var 5]"
#guard ([□(Form.var 4)] ⇒ [Form.var 4 ⟶ Form.var 5] : Seq).ascii == "[]p4 => p4 -> p5"

/-! ## Lean reads what `Seq.src` writes as the same sequent

`glsrun prove` states its fact of the sequent as `Seq.src` writes it, and
its first line shows the sequent as `Seq.show` writes it.  The two are
the same sequent only if Lean reads the first text as the sequent it was
written from.  Here each text is given to Lean's own parser and
elaborator, and the value compared. -/

open Lean Elab Command Term Meta in
/-- Lean's reading of a text as a term of type `Seq`. -/
unsafe def leanReads (text : String) : TermElabM Seq := do
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term text)
  let e ← elabTermEnsuringType stx (some (mkConst ``Seq))
  synthesizeSyntheticMVarsNoPostponing
  evalExpr Seq (mkConst ``Seq) (← instantiateMVars e)

open Lean Elab Command Term Meta in
run_cmd liftTermElabM do
  for j in entries.map (·.seq) ++ extra do
    let k ← unsafe leanReads j.src
    unless k == j do
      throwError "Lean reads {j.src} as another sequent than it was written from"

-- A control: the comparison can fail.
open Lean Elab Command Term Meta in
run_cmd liftTermElabM do
  let k ← unsafe leanReads "[] ⇒ [(p ⟶ q) ⟶ r]"
  if k == ([] ⇒ [p ⟶ q ⟶ r]) then
    throwError "the comparison of Lean's reading does not tell two sequents apart"

/-! ## The signs of a keyboard, and the arrow -/

#guard reads "p -> q" ([] ⇒ [p ⟶ q])
#guard reads "p → q" ([] ⇒ [p ⟶ q])
#guard reads "p ⟶ q" ([] ⇒ [p ⟶ q])
#guard reads "p ⊃ q" ([] ⇒ [p ⟶ q])
#guard reads "[]p, □p => q" ([□p, □p] ⇒ [q])
#guard reads "bot, ⊥, _|_ => p" ([⊥, ⊥, ⊥] ⇒ [p])
#guard reads "p => q" ([p] ⇒ [q])
#guard reads "p ⇒ q" ([p] ⇒ [q])
#guard reads "p |- q" ([p] ⇒ [q])
#guard reads "p ⊢ q" ([p] ⇒ [q])
#guard reads "p, q, r, s => p0, p1, p2, p3" ([p, q, r, s] ⇒ [p, q, r, s])
#guard reads "p4, p12 => Form.var 12, (Form.var 4)" ([.var 4, .var 12] ⇒ [.var 12, .var 4])
-- Spaces are not needed, and are allowed inside `[]`.
#guard reads "[]p->[][]p" ([] ⇒ [□p ⟶ □□p])
#guard reads "[ ] p  =>q" ([□p] ⇒ [q])

/-! ## The signs that are not connectives of the calculus

The reader computes the formula each stands for, by the definitions of
`GLS/Connectives.lean`; the first line of the answer shows that formula,
and not the text typed. -/

#guard reads "top" ([] ⇒ [Form.top])
#guard reads "⊤" ([] ⇒ [Form.top])
#guard reads "~p" ([] ⇒ [p.neg])
#guard reads "¬p, !p, ∼p =>" ([p.neg, p.neg, p.neg] ⇒ [])
#guard reads "<>p" ([] ⇒ [p.dia])
#guard reads "◇p, ⋄p =>" ([p.dia, p.dia] ⇒ [])
#guard reads "p | q" ([] ⇒ [p ⋎ q])
#guard reads "p ∨ q, p ⋎ q, p \\/ q =>" ([p ⋎ q, p ⋎ q, p ⋎ q] ⇒ [])
#guard reads "p & q" ([] ⇒ [p ⋏ q])
#guard reads "p ∧ q, p ⋏ q, p /\\ q =>" ([p ⋏ q, p ⋏ q, p ⋏ q] ⇒ [])
-- The formulas themselves, in the calculus's own connectives.
#guard reads "top, ~p, <>p =>" ([⊥ ⟶ ⊥, p ⟶ ⊥, □(p ⟶ ⊥) ⟶ ⊥] ⇒ [])
#guard reads "p | q, p & q =>" ([(p ⟶ ⊥) ⟶ q, (p ⟶ q ⟶ ⊥) ⟶ ⊥] ⇒ [])
-- What the answer shows for a text typed with them.
#guard (parseSeq "<>top -> ~[]bot").toOption.map Seq.show
  == some "⇒ (□((⊥ → ⊥) → ⊥) → ⊥) → □⊥ → ⊥"

/-! ## How the connectives bind

The right-hand sides are Lean terms: Lean's notations do the binding
there, and the reader's reading is compared with Lean's. -/

-- `→` groups to the right.
#guard reads "p -> q -> r" ([] ⇒ [p ⟶ q ⟶ r])
#guard reads "p -> q -> r" ([] ⇒ [p ⟶ (q ⟶ r)])
#guard reads "(p -> q) -> r" ([] ⇒ [(p ⟶ q) ⟶ r])
-- `□` takes the formula that follows it, and no more.
#guard reads "[]p -> q" ([] ⇒ [□p ⟶ q])
#guard reads "[]p -> q" ([] ⇒ [(□p) ⟶ q])
#guard reads "[](p -> q)" ([] ⇒ [□(p ⟶ q)])
#guard reads "[][]p -> []q" ([] ⇒ [□□p ⟶ □q])
-- `¬` and `◇` bind as `□` does.
#guard reads "~p -> q" ([] ⇒ [p.neg ⟶ q])
#guard reads "~(p -> q)" ([] ⇒ [(p ⟶ q).neg])
#guard reads "~[]p" ([] ⇒ [(□p).neg])
#guard reads "[]~p" ([] ⇒ [□p.neg])
#guard reads "<>p -> q" ([] ⇒ [p.dia ⟶ q])
#guard reads "~p & q" ([] ⇒ [p.neg ⋏ q])
-- `∧` binds tighter than `∨`, and `∨` tighter than `→`.
#guard reads "p & q | r" ([] ⇒ [p ⋏ q ⋎ r])
#guard reads "p & q | r" ([] ⇒ [(p ⋏ q) ⋎ r])
#guard reads "p | q & r" ([] ⇒ [p ⋎ q ⋏ r])
#guard reads "p | q & r" ([] ⇒ [p ⋎ (q ⋏ r)])
#guard reads "p | q -> r" ([] ⇒ [p ⋎ q ⟶ r])
#guard reads "p | q -> r" ([] ⇒ [(p ⋎ q) ⟶ r])
#guard reads "p -> q | r" ([] ⇒ [p ⟶ q ⋎ r])
#guard reads "p -> q & r" ([] ⇒ [p ⟶ (q ⋏ r)])
#guard reads "[]p & q" ([] ⇒ [□p ⋏ q])
-- `∧` and `∨` group to the left.
#guard reads "p | q | r" ([] ⇒ [p ⋎ q ⋎ r])
#guard reads "p | q | r" ([] ⇒ [(p ⋎ q) ⋎ r])
#guard reads "p & q & r" ([] ⇒ [p ⋏ q ⋏ r])
#guard reads "p & q & r" ([] ⇒ [(p ⋏ q) ⋏ r])
-- A comma separates formulas, whatever stands beside it.
#guard reads "p -> q, r => s -> p, q" ([p ⟶ q, r] ⇒ [s ⟶ p, q])

/-! ## `[]`: the sign `□`, and a side with nothing in it -/

-- Before a formula, `□`.
#guard reads "[]p ⇒ q" ([□p] ⇒ [q])
#guard reads "[][]p, []bot ⇒ [](p -> q)" ([□□p, □⊥] ⇒ [□(p ⟶ q)])
-- Before the arrow or the end, a side with nothing in it.
#guard reads "[] ⇒ []p" ([] ⇒ [□p])
#guard reads "[]p ⇒ []" ([□p] ⇒ [])
#guard reads "[] ⇒ []" ([] ⇒ [])
#guard reads "⇒" ([] ⇒ [])
#guard reads "p ⇒" ([p] ⇒ [])
-- A bracket that is not `[]` opens a list, a whole side.
#guard reads "[p, q] ⇒ [r]" ([p, q] ⇒ [r])
#guard reads "[[]p] ⇒ [q]" ([□p] ⇒ [q])
#guard reads "[[]p, [][]q] ⇒ [[]r]" ([□p, □□q] ⇒ [□r])
#guard reads "[p] ⇒ q, r" ([p] ⇒ [q, r])
#guard reads "p, q ⇒ [r]" ([p, q] ⇒ [r])
-- `[]` alone is not a formula: no arrow, and nothing to read as `⇒ A`.
#guard refusedAt "[]" 2
-- `[]` before a comma is neither.
#guard refusedAt "[], p ⇒ q" 2
#guard refusedAt "[[], p] ⇒ q" 3

/-! ## A text with no arrow -/

#guard reads "[]([]p -> p) -> []p" ([] ⇒ [□(□p ⟶ p) ⟶ □p])
#guard reads "p" ([] ⇒ [p])
-- Two formulas and no arrow: on which side?  Refused, at the end.
#guard refusedAt "p, q" 4
-- A list in brackets and no arrow: refused, at the end.
#guard refusedAt "[p]" 3

/-! ## Texts that are refused, and where -/

#guard refusedAt "" 0
#guard refusedAt "   " 3
#guard refusedAt "p ->" 4
#guard refusedAt "p → → q" 4
#guard refusedAt "□" 1
#guard refusedAt "~" 1
#guard refusedAt "()" 1
#guard refusedAt "p & | q" 4
#guard refusedAt "p q" 2
#guard refusedAt "p ⇒ q r" 6
#guard refusedAt "p -> (q" 7
#guard refusedAt "p)" 1
#guard refusedAt "p ⇒ q)" 5
#guard refusedAt "(p ⇒ q)" 3
#guard refusedAt "p ⇒ q ⇒ r" 6
#guard refusedAt "p, ⇒ q" 3
#guard refusedAt ", p ⇒ q" 0
#guard refusedAt "p,, q ⇒" 2
#guard refusedAt "[p" 2
#guard refusedAt "p]" 1
#guard refusedAt "[p, q ⇒ r" 6
#guard refusedAt "[p,] ⇒ q" 3
#guard refusedAt "[p] q ⇒ r" 4
#guard refusedAt "[p], q ⇒ r" 3
#guard refusedAt "p ⇒ [q] r" 8
#guard refusedAt "p ⇒ q, [r]" 7
#guard refusedAt "p -> [q]" 5
#guard refusedAt "x" 0
#guard refusedAt "p -> pq" 5
#guard refusedAt "p # q" 2
#guard refusedAt "Form.var" 8
#guard refusedAt "Form.var p" 9

-- Controls: `reads` and `refusedAt` can say no.
#guard !(reads "p -> q -> r" ([] ⇒ [(p ⟶ q) ⟶ r]))
#guard !(reads "p, q ⇒ r" ([q, p] ⇒ [r]))
#guard !(refusedAt "p q" 3)
#guard !(refusedAt "p ⇒ q" 0)

/-! ## The program's check of a tree of worlds

`glsrun prove` checks a tree by the table of `GLS/FastCheck.lean` before
it prints it; the kernel checks the printed tree by `Seq.refutedAt`.  The
two are compared here: on the 1 024 small sequents of the screens at 200
worlds, of which some refute and some do not; and on the tree the search
over sets returns for each sequent of the corpus and of the families that
is not derivable. -/

#guard seqsSmall.length == 1024
#guard ((worlds trees2).take 200).length == 200
#guard seqsSmall.all fun j => ((worlds trees2).take 200).all fun w =>
  FastCheck.refuted j w == j.refutedAt w
-- Both answers occur among them.
#guard seqsSmall.any fun j => ((worlds trees2).take 200).any fun w => FastCheck.refuted j w
#guard seqsSmall.any fun j => ((worlds trees2).take 200).any fun w => !FastCheck.refuted j w

/-- The tree the search over sets returns, where it returns one. -/
def treeOf (j : Seq) : Option Tree :=
  match produceSet j with
  | some (.inr t) => some t
  | _ => none

#guard ((entries.map (·.seq)) ++ [consis 3, consis 9, binTree 2, binTree 4]).all fun j =>
  match treeOf j with
  | some t => FastCheck.refuted j t && j.refutedAt t
  | none => true
#guard ((entries.map (·.seq)).filterMap treeOf).length == 8
-- The tree of one sequent does not refute another.
#guard (treeOf (consis 3)).all fun t => !FastCheck.refuted (consis 4) t && !(consis 4).refutedAt t

/-! ## The report of a fault -/

/--
info: not a sequent, at character 8: the parenthesis opened at character 6 is not closed
  p -> (q
         ^
-/
#guard_msgs in
#eval match parseSeq "p -> (q" with
  | .error f => IO.println (f.report "p -> (q")
  | .ok _ => IO.println "read"

/--
info: not a sequent, at character 3: a list in brackets is a whole side of the sequent: the arrow ⇒ or the end was expected after it
  [], p ⇒ q
    ^
-/
#guard_msgs in
#eval match parseSeq "[], p ⇒ q" with
  | .error f => IO.println (f.report "[], p ⇒ q")
  | .ok _ => IO.println "read"

/--
info: not a sequent, at character 5: the arrow ⇒ was expected: a text with no arrow is one formula A, read as ⇒ A
  p, q
      ^
-/
#guard_msgs in
#eval match parseSeq "p, q" with
  | .error f => IO.println (f.report "p, q")
  | .ok _ => IO.println "read"

end GLS.ParseTest
