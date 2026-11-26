/-
Tests of the reader (`MALL/Parse.lean`): every entry of the corpus is read
back from what each of the three printers writes; Lean reads what the
printer of Lean source writes as the same sequent; the reader binds the
connectives as Lean does; the two readings of `⊥`; two-sided texts; texts
that are refused, each with the place of the fault.

Every value pinned here was printed by Lean first.
-/
import MALL.Parse
import MALL.Corpus.Basic
import Lean

namespace MALL.ParseTest

open MALL MALL.Parse MALL.Corpus

/-- The text is read, as the sequent `Γ`. -/
def reads (text : String) (Γ : List Form) : Bool :=
  match parseSeq text with
  | .ok Δ => Δ == Γ
  | .error _ => false

/-- The text is refused, with the fault at character `i`, counted from 0. -/
def refusedAt (text : String) (i : Nat) : Bool :=
  match parseSeq text with
  | .ok _ => false
  | .error f => f.pos == i

/-! ## The corpus, read back from each printer -/

-- 38 entries.
#guard entries.length == 38

-- From the source's notation (`showSeq`).
#guard entries.all fun e => reads (showSeq e.seq) e.seq

-- From Lean source (`srcForms`), which is also the text of the entry.
#guard entries.all fun e => reads (srcForms e.seq) e.seq
#guard entries.all fun e => e.src == srcForms e.seq

-- With the signs of a keyboard (`asciiSeq`), which are of a keyboard.
#guard entries.all fun e => reads (asciiSeq e.seq) e.seq
#guard entries.all fun e => (asciiSeq e.seq).toList.all fun (c : Char) => c.toNat < 128

-- The families, further than the corpus has them (letters from `a4` on),
-- from the three printers.
#guard [chain 9, chainBad 7, fan 9, fanBad 6, withTree 4, slack 9].all fun Γ =>
  reads (showSeq Γ) Γ && reads (srcForms Γ) Γ && reads (asciiSeq Γ) Γ

-- What the printers write, so that a change of a printer is seen here.
#guard showSeq (chain 2) == "⊢ p⊥, p ⊗ q⊥, q ⊗ r⊥, r"
#guard srcForms (chain 2) == "[pᗮ, p ⊗ qᗮ, q ⊗ rᗮ, r]"
#guard asciiSeq (chain 2) == "|- p^, p * q^, q * r^, r"
#guard showSeq (fan 5) == "⊢ p ⊗ (q ⊗ (r ⊗ (s ⊗ (a4 ⊗ a5)))), a5⊥, a4⊥, s⊥, r⊥, q⊥, p⊥"
#guard srcForms (fan 5) ==
  "[p ⊗ (q ⊗ (r ⊗ (s ⊗ ((Form.atom 4) ⊗ (Form.atom 5))))), Form.natom 5, Form.natom 4, sᗮ, rᗮ, qᗮ, pᗮ]"
#guard asciiSeq [𝟏, ⊥, ⊤, 𝟎, p ⅋ (q & (r ⊕ s))] == "|- 1, bot, top, 0, p | (q & (r + s))"
#guard showSeq [] == "⊢"
#guard srcForms [] == "[]"
#guard asciiSeq [] == "|-"

/-! ## Lean reads what `srcForms` writes as the same sequent

`mallrun prove` states its fact of the list that `srcForms` writes, and
its first line shows the sequent as `showSeq` writes it.  The two are the
same sequent only if Lean reads the first text as the sequent it was
written from.  Here each text is given to Lean's own parser and
elaborator, and the value compared. -/

open Lean Elab Command Term Meta in
/-- Lean's reading of a text as a term of type `List Form`. -/
unsafe def leanReads (text : String) : TermElabM (List Form) := do
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term text)
  let ty := mkApp (mkConst ``List [levelZero]) (mkConst ``Form)
  let e ← elabTermEnsuringType stx (some ty)
  synthesizeSyntheticMVarsNoPostponing
  evalExpr (List Form) ty (← instantiateMVars e)

open Lean Elab Command Term Meta in
run_cmd liftTermElabM do
  let extra : List (List Form) := [chain 9, chainBad 7, fan 9, fanBad 6, withTree 4, slack 9,
    [𝟏, ⊥, ⊤, 𝟎, p ⅋ (q & (r ⊕ s))], [(Form.natom 12) ⊗ sᗮ, (Form.atom 12) ⅋ s]]
  for Γ in entries.map (·.seq) ++ extra do
    let Δ ← unsafe leanReads (srcForms Γ)
    unless Δ == Γ do
      throwError "Lean reads {srcForms Γ} as another sequent than it was written from"

/-! ## The reader binds as Lean does

Each text, in the notation of `MALL/Form.lean` and with no parentheses but
those shown, is read by the reader and by Lean; the two sequents are
compared. -/

open Lean Elab Command Term Meta in
run_cmd liftTermElabM do
  let texts : List String := ["p ⊗ q & r", "p & q ⊗ r", "p ⅋ q ⊕ r", "p ⊕ q ⅋ r", "p & q ⅋ r",
    "p ⅋ q & r", "p ⊗ q ⊕ r", "p ⊕ q ⊗ r", "p ⊗ q ⊗ r", "p & q & r", "p ⅋ q ⅋ r", "p ⊕ q ⊕ r",
    "p ⊗ q & r ⅋ s ⊕ p", "p ⊕ q ⅋ r & s ⊗ p", "pᗮ ⊗ qᗮ", "(p ⊗ q)ᗮ ⅋ r", "(p ⊕ q)ᗮᗮ",
    "⊥ ⅋ 𝟏 ⊗ ⊤ ⊕ 𝟎", "(p ⅋ q) ⊗ r, p ⅋ (q ⊗ r)", "pᗮ ⅋ q ⊗ rᗮ & 𝟏"]
  for t in texts do
    let Δ ← unsafe leanReads ("[" ++ t ++ "]")
    match parseSeq t with
    | .ok Γ => unless Γ == Δ do throwError "the reader and Lean read {t} differently"
    | .error f => throwError "the reader refuses {t}: {f.msg}"

-- The same, said outright for the four connectives and `⊸`.
#guard reads "p * q | r" [(p ⊗ q) ⅋ r]
#guard reads "p | q * r" [p ⅋ (q ⊗ r)]
#guard reads "p & q + r" [(p & q) ⊕ r]
#guard reads "p + q & r" [p ⊕ (q & r)]
#guard reads "p * q & r | s + p" [(((p ⊗ q) & r) ⅋ s) ⊕ p]
#guard reads "p * q * r" [p ⊗ (q ⊗ r)]
#guard !reads "p * q * r" [(p ⊗ q) ⊗ r]
-- `⊸` binds least, and groups to the right; `A ⊸ B` is `A⊥ ⅋ B`.
#guard reads "p -o q -o r" [pᗮ ⅋ (qᗮ ⅋ r)]
#guard reads "(p -o q) -o r" [(p ⊗ qᗮ) ⅋ r]
#guard reads "p * q -o q + p" [(p ⊗ q)ᗮ ⅋ (q ⊕ p)]
#guard reads "p ⊸ q" [pᗮ ⅋ q]
-- A comma binds less than any connective.
#guard reads "p -o q, r" [pᗮ ⅋ q, r]

/-! ## The signs of a keyboard, and the dual -/

#guard reads "T, top, ⊤, 1, 𝟏, 0, 𝟎, bot" [⊤, ⊤, ⊤, 𝟏, 𝟏, 𝟎, 𝟎, ⊥]
#guard reads "a0, a3, a4, a12, Form.atom 12, (Form.natom 12)^"
  [p, s, .atom 4, .atom 12, .atom 12, .atom 12]
#guard reads "p par q" [p ⅋ q]
#guard reads "  p ,\n q  " [p, q]
-- The dual is a function: what is read is in negation normal form.
#guard reads "p^, pᗮ, p⊥, ~p, ¬p" [pᗮ, pᗮ, pᗮ, pᗮ, pᗮ]
#guard reads "~(p * q)" [pᗮ ⅋ qᗮ]
#guard reads "(p ⊗ q)⊥" [pᗮ ⅋ qᗮ]
#guard reads "~~p, p^^, p⊥⊥" [p, p, p]
-- `~` takes the formula that follows it, with its duals: `~p⊥` is `p`.
#guard reads "~p⊥" [p]
#guard reads "~p * q" [pᗮ ⊗ q]
#guard reads "~(p) ^" [p]

/-! ## `⊥` is two things -/

-- Where a formula is expected, the unit.
#guard reads "⊥" [⊥]
#guard reads "⊥, ⊥" [⊥, ⊥]
#guard reads "⊥ ⅋ p" [⊥ ⅋ p]
-- After a formula, the dual.
#guard reads "p⊥" [pᗮ]
#guard reads "⊥⊥" [𝟏]
#guard reads "p ⅋ ⊥⊥" [p ⅋ 𝟏]
#guard reads "(p ⊗ q)⊥⊥" [p ⊗ q]
-- The word and the caret are one thing each.
#guard reads "bot^" [𝟏]
#guard reads "~⊥" [𝟏]
#guard refusedAt "^p" 0
#guard refusedAt "p bot" 2

/-! ## The sequent: the turnstile, brackets, two sides -/

-- The empty sequent, four ways.
#guard reads "" []
#guard reads "⊢" []
#guard reads "|-" []
#guard reads "[]" []
-- One-sided, with the turnstile or without, or as Lean writes a list.
#guard reads "|- p, q" [p, q]
#guard reads "⊢ p, q" [p, q]
#guard reads "p, q" [p, q]
#guard reads "[p, q]" [p, q]
-- Two-sided: the formulas before the turnstile are negated.
#guard reads "p, q |- r" [pᗮ, qᗮ, r]
#guard reads "p * q |- q * p" [pᗮ ⅋ qᗮ, q ⊗ p]
#guard reads "p |-" [pᗮ]
#guard reads "p => q" [pᗮ, q]
#guard reads "p ⟹ q" [pᗮ, q]

/-! ## Texts that are refused, and where -/

-- A formula is missing.
#guard refusedAt "p," 2
#guard refusedAt ", p" 0
#guard refusedAt "p,, q" 2
#guard refusedAt "p *" 3
#guard refusedAt "p * | q" 4
#guard refusedAt "~" 1
#guard refusedAt "()" 1
#guard refusedAt "p ⊗ (q ⅋" 8
#guard refusedAt "p par" 5
#guard refusedAt "par p" 0
-- Two formulas with nothing between them.
#guard refusedAt "p q" 2
#guard refusedAt "top top" 4
#guard refusedAt "1 1" 2
#guard refusedAt "p ~ q" 2
-- Parentheses, brackets and turnstiles that do not fit.
#guard refusedAt "(p" 2
#guard refusedAt "p)" 1
#guard refusedAt "[p" 2
#guard refusedAt "p]" 1
#guard refusedAt "[p] q" 4
#guard refusedAt "p, [q]" 3
#guard refusedAt "p |- q |- r" 7
#guard refusedAt "[p |- q]" 3
-- Names and signs that are not of this calculus.
#guard refusedAt "x" 0
#guard refusedAt "P" 0
#guard refusedAt "p0" 0
#guard refusedAt "a" 0
#guard refusedAt "7" 0
#guard refusedAt "p # q" 2
#guard refusedAt "p - q" 2
#guard refusedAt "Form.atom" 9
#guard refusedAt "Form.atom p" 10

/-! ## The report of a fault

The places above are counted from 0, as a `Fault` has them; the report
counts from 1. -/

#guard (match parseSeq "(p" with
  | .error f => f.pos == 2 && f.msg == "the parenthesis opened at character 1 is not closed"
  | .ok _ => false)

#guard (match parseSeq "p, (q ⊗" with
  | .error f => f.report "p, (q ⊗" ==
      "not a sequent, at character 8: a formula was expected\n  p, (q ⊗\n         ^"
  | .ok _ => false)

end MALL.ParseTest
