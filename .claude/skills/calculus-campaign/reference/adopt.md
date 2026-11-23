# Part (a): adopting the calculus

Covers the Survey, the transcription half of Adopt, and Prove. The tools
are the commands of `ProofTools.Audit`: `import ProofTools.Audit`, with no
`open`.

Contents: 1 the source; 2 the kinds of result; 3 the transcription;
4 the rule table; 5 statements and their screening; 6 proving.

## 1. The source

**Which source** was fixed at the first act (`gates.md`, the first entry).
The version agreed there rules: do not replace it, or the file you were
handed, by another without asking.

**Get the source, not a rendering of it.**

- Read the agreed version, in LaTeX where that version's source can be
  had (arXiv gives it for many papers), otherwise its PDF. The LaTeX of
  another version serves for labels and for searching, and for nothing
  that is transcribed. Say in the plan which file was read, and whether
  in full.
- **Read the appendix.** Page limits push the detail that matters there.
- **Cite by label, never by number alone.** The arXiv source and the
  journal version of one paper number the same result differently. Where
  the source has labels, the label is the key and the number a
  convenience; from a PDF, cite the printed number with its version.
- **`skeleton.md`**, in the campaign folder: the source's numbered
  results, each with its label, number, page and statement. A paper's
  printed numbers are not in its LaTeX: compile it and read the `.aux`,
  whose lines `\newlabel{<label>}{{<number>}{<page>}…}` give them. Do not
  simulate LaTeX's counters. The script
  `tools/paper-skeleton/paper_skeleton.py` of
  [lax-logic-in-lean](https://github.com/fairflow/lax-logic-in-lean)
  (Python, standard library only; it needs `pdflatex` and `pdftotext`)
  writes the file: `./paper_skeleton.py --arxiv <id> -o skeleton.md`, or
  `--src main.tex`. It is not part of `proof-tools`. From a PDF alone,
  write the list by hand.

**Read the prose around the figure, not the figure alone.** Before any
rule is transcribed, write down in `plan.md` (Q1), each with its place in
the source:

- what a formula is (the connectives; whether negation is primitive or
  defined; whether formulas are in a normal form);
- what a judgment is, exactly: one-sided or two-sided; lists, multisets or
  sets; whether it is flat or has structure inside it;
- what the schematic letters of the figure range over, and what each
  piece of its notation means;
- every side condition, including those stated once in the prose for
  several rules;
- which lines of the figure are **rules** and which are **restrictions on
  proof search**. They are not interchangeable, and the figure does not
  say which is which;
- which rules are primitive and which the paper shows admissible;
- where the source is ambiguous or silent, and what you propose. These are
  the reviewer's to settle.

**The standing list** (`SKILL.md`) is answered entry by entry in Q2. The
paper that defines a calculus is often not the one that proves a given
result about it: look at the papers that cite it, and at the sources it
cites for the logic. A result proved for a neighbouring system (the
calculus with an extra rule, another calculus for the same logic) is not
a result about this one: its value is "holds of the logic, proved
elsewhere", and the line says which system the source's theorem is about.

**Look for what exists already** (Q5): a formalisation of this calculus in
any prover; a related calculus already in the project. Bound the search,
and say where you looked. "Not found" is the claim to make, not "none
exists".

**Does the paper prove a theorem twice by different routes?** Cost both;
the shorter one is equally published.

## 2. The kinds of result

Decide them in the plan, before transcribing: each kind needs a different
encoding and fails differently, and a campaign usually has several. A
result that is not in the table takes its shape from the source's
statement of it.

| kind | shape | watch for |
|---|---|---|
| soundness and completeness for a semantics | a structure of models with a forcing relation; soundness by induction on derivations; completeness by a model construction or through a second calculus | make the model construction return data (a `Type`), since it is then the search of the Run stage |
| cut elimination, admissible structural rules | two families, with and without the rule, or one with a parameter (§3); a measure carried by the statement; induction on it | decide how the measure is carried before the family is typed (§3). Say which form is the goal: that the rule is admissible, or a procedure that removes it |
| a property stated of models (the finite model property) | a construction of a model with the property | return the model as data: it is then a producer of countermodels for Run |
| a result about a term calculus (normalisation, confluence) | terms, typing, and reduction as a relation: a second transcription, with a rule table of its own | how binding is represented is a choice of encoding for the plan |
| a result read off derivations (the disjunction and existence properties) | a function on derivations, or on derivations of a special form | it may need another result first (cut-free derivations, a normal form): order the goals so. With the family into `Type` what is read off is data |
| termination, decidability | a well-founded order on judgments, and a procedure | the bound that makes the proof easy is seldom runnable: prove with it, and search without it (Run) |
| conservativity, a translation | two calculi and a map, a theorem each way | computed indices (§3) |
| completeness of a search strategy | a restricted calculus, complete for the unrestricted one | a restriction that the source states by a classification of formulas is a statement-level decision: get it signed |
| the subformula property | a closure and an invariant on derivations | it is where the side conditions of the rule table become visible: if it fails, suspect the table |

## 3. The transcription

**One indexed inductive family, one constructor for each primitive rule.**

- The indices are the judgment. Side conditions are fields. Each
  constructor's comment cites its rule in the source (label, or figure and
  name).
- Into `Type` where a derivation will be used as data: a translation, a
  proof term, a search that returns it, a procedure on derivations (the
  removal of cuts), a witness read off a derivation; and then the
  explorer's derivations map out to it as data (`reference/explore.md`
  §4). Into `Prop` otherwise. Say which in the plan.
- A rule that cannot cite a line of the source is invented. If you need
  one, it is a divergence (§4), recorded when it is made.
- **Rules the source shows admissible are theorems, not constructors.**
  They are goals of Prove.
- **Where the source has two systems** and a result relates them (with cut
  and without, say), they are two families, or one family with a Boolean
  parameter that says whether the extra rule is allowed. Choose in the
  plan; the rule table has rows for both.
- **A measure** (height, rank) that a proof will induct on: either a
  second family indexed by it (an index `n + 1` is not a computed index),
  or, when the family is into `Type`, a function on derivations. Do not
  add an index the source does not have to the family the rule table is
  checked against.

**Judgments as data.** Core Lean has lists, not multisets. Where the
source's judgments are multisets or sets, the choices are: a list, with
each rule asking for its formula by membership (`A ∈ Γ`) and adding at the
head, so that exchange, weakening and contraction are admissible and need
no rule (the form that has kept earlier developments free of casts); or a
list with an exchange rule added. Either is a divergence of
representation (§4): propose one in the plan and have it signed.

**No computed index in a conclusion.** In a constructor's return type
every index must be a variable or a constructor applied to variables,
never a function applied to something. Lean's unifier cannot invert a
function, so `cases` on a derivation fails, or leaves an equation between
types that nothing discharges. The development stays sound; what goes
wrong is that the statements bend to what can be case-analysed, and the
judgment stops being the source's. A clean build with clean axioms does
not show it. (A computed index is "green slime", after McBride: hence the
command's name.)

- Precisely: what matters is the index after Lean has unfolded
  definitions at its head. Clean: variables, constructors, literals,
  `n + 1`, a definition that unfolds to a constructor. Not clean: a
  projection `c.head`, a definition that stays stuck on a variable,
  `Γ ++ Δ`, `Γ.erase A`.
- Computation in a **premise** is harmless: only the return type matters.
- **The repair**: replace the computed index by a fresh variable and carry
  the computation as an equation field. Schematically, for a rule whose
  conclusion the source writes with `Γ ++ Δ`:

  ```lean
  | rule {Γ Γ' Δ : List Form} {A B : Form}
      (d : Fam (A :: Γ) B)
      (h : Γ' = Γ ++ Δ)          -- was: the conclusion `Fam (Γ ++ Δ) …`
      : Fam Γ' (Form.imp A B)
  ```

- Do it now. Afterwards it means redoing every proof over the family.

**A rule stated for every context.** Some sources state a rule
schematically for any surrounding structure. Written as it stands, its
conclusion is then a function applied to something: a computed index. The
repair is the one above. How a place inside a judgment is named in Lean,
and with it what the family's constructor takes, is a choice of encoding
for the plan (`reference/explore.md` §13 has the options and what each
costs), and a divergence of representation (§4).

**Run the two commands.** Give the judgments the source's notation
first, so that the output reads as the figure does. On a family of two
rules (compiled; `⊢` and `⋏` are its notations):

```lean
#rules Example.Fam
#slime Example.CleanControl Example.SlimedControl
#slime Example.Fam
```

```
Example.Fam — 2 rules
andR
    Fam (Γ ⊢ A)      Fam (Γ ⊢ B)
    ──────────────────────────────
    Fam (Γ ⊢ A ⋏ B)

andL
    Fam (A :: B :: Γ ⊢ C)
    ───────────────────────
    Fam (Γ ⊢ C)
    for  A : Form,  B : Form
    if   A ⋏ B ∈ Γ
Example.CleanControl — 1 indices, 2 constructors, 0 carrying green slime

  clean: nil, cons
warning: Example.SlimedControl — 1 indices, 2 constructors, 1 carrying green slime

  app
    index 1  ms ++ ns
              ↳ computed by  HAppend.hAppend

  clean: nil
Example.Fam — 1 indices, 2 constructors, 0 carrying green slime

  clean: andR, andL
```

- `#rules J` prints each constructor as an inference figure: premises over
  a line (side by side where they fit), the conclusion under it, side
  conditions after `if`, and after `for` the data the rule names. A
  binder whose type ends in the family is a premise; any other
  proposition is a side condition; an explicit binder that is neither is
  data. Compare the output with the source's figure line by line, and
  paste it, as printed, into the rule table.
- `#rules` prints what the constructor says. Content inside a definition
  shows as the definition's name: open it and read it too.
- `#slime J` reports, for each constructor, which indices of its
  conclusion are computed, and by what. It warns and never fails a build.
  **Run a control first**, so that you know the check neither flags
  everything nor nothing: the two small families above are in
  `templates/Instance.lean.txt`. The transcription is not done until
  `#slime` reports none on the family. Leave both commands in the file,
  after the family.

## 4. The rule table, and the divergence log

`templates/rule-table.md`. One row for each rule of the source's figure,
in the figure's order: the rule as printed, the constructor, the output of
`#rules` for it, and whether they agree. What is in the Lean and not in
the figure has a table of its own. The column for the move of the proof
system is empty when the table is signed; it is filled at step 5 of Adopt
and is read at the reviewer's test.

A **divergence** is recorded when it is made, never afterwards. Three
kinds, kept apart:

- **W**, the source is wrong or says too much: prove what is used, and
  say so;
- **U**, the source is under-specified: say how it was specified, and that
  the choice was ours;
- **R**, a choice of representation where the source is clear: a list for
  a multiset, an equation field for a computed index. Say what in the
  Lean stands for what in the source.

The reviewer signs the table before anything is built on the family. It is
also the page that lies beside the source's figure at the reviewer's
test. An error of transcription found later is repaired in the family,
entered in the table's last section with when it was found, and the table
is signed again.

## 5. Statements, and screening them

Faults of statement, not of proof, are the recurring ones, and each was
refutable by a small countermodel before any proof was attempted.

**Which statements.** The goals of the plan, the two that join `step` to
the family (S1 and S2, `reference/explore.md` §4), and any statement of
your own that a report will cite. Lemmas on the way are not entered. A
goal whose proof the literature only states is entered like the others:
it is OPEN until the kernel has a proof, whoever says it is proved.

**Each goes to the reviewer displayed, before its proof**, in
`statements.md` (`templates/statements.md`), with status OPEN.

**Where an OPEN statement lives in Lean.** As a named proposition with no
proof, in a theory file:

```lean
def Completeness : Prop := ∀ j, Valid j → Nonempty (Fam j)
```

Lean checks that it is well typed, and it carries no `sorry`, so the
file's bound on axioms still holds. Its proof, when there is one, is
`theorem completeness : Completeness`. A `sorry` in a theory file breaks
the file's bound, which is what the bound is for.

**Every quantified statement is attacked before you decide how to prove
it.** Four directions, in the order they have paid:

1. **Replay what is known.** The hard instances the project or the source
   already has, put into the new statement's terms.
2. **Boundary cases.** The degenerate end of every axis: empty contexts,
   the constants of the language, every clause of a definition that has no
   case.
3. **One step past what passed.** Size plus one, depth plus one, a second
   member that interacts. Never run again only what passed.
4. **Every branch.** Each arm of each match met by an admissible case.
   Pairs of features are not always enough.

Verdicts are three-valued: fail only on a certificate; a case that ran out
of budget is flagged and run again at a larger one, never dropped. Run
banks of cases compiled, one line of output for each, so that a run that
is stopped loses nothing.

**What to screen with.** A calculus that is new to the project has no
model checker until one is written. The check of a model of part (b)
(`reference/certify.md` §3) is the screen, so where the plan has a
semantics, write it before the proofs of this stage and not after them:
its notion of model was signed with the plan, and no gate of Run waits
for it.
With it, the simplest screen of a soundness theorem goes rule by rule: for
each rule, small instances of its premises and conclusion, and small
models, and no model may refute the conclusion while refuting no premise.
A completeness statement is screened on the known non-theorems (each
should have a small countermodel) and, once there is a search, on small
valid judgments (each should get a derivation). Until that check exists,
screen small cases by evaluation, and say in the report what each
statement was screened with.

A rule that is being designed, not transcribed, gets the same: print it
with `#rules`, screen it, and have it signed before anything rests on it.

## 6. Proving

- **A theory file ends with its bound on axioms**, as the plan's policy
  sets it: `#axioms_within_file [...]`, an upper bound, so that a proof
  may use fewer axioms than its file allows and none outside them. For
  one declaration, `#axioms_within d [...]`; for whole libraries, from a
  file that imports them, `#axiom_sweep [Lib] allowing [...]`. An
  exception is the reviewer's to grant, one declaration at a time:
  `#axioms_within_file [...] except [d]`.
- **When a bound fails**, do not guess: the axiom is as often in a tactic
  or a library lemma as in the argument. `#choice_path d` gives the
  shortest chain from `d` to `Classical.choice`, with each step's module:
  where the names stop being yours is where the axiom enters.
  `#choice_sources d` gives the direct dependencies that carry it;
  `#axiom_path ax d` does the same for any axiom, `sorryAx` included.
- **Where the policy is to avoid `Classical.choice`.** On core Lean the
  known sources are the `String` functions that R4 of `lean-certify`
  lists, and `omega` given a conjunction to prove (split the goal first).
  On Mathlib also: `tauto` and `push_neg` are classical, and `simp` can
  be, through a library lemma. Everywhere: `choose` and `Nonempty.some`
  are choice, so a construction that must return a derivation returns
  one, as data. `#cf_search "pat"` lists the constants whose name contains
  the pattern and that do not depend on `Classical.choice`.
- **Where choice is in the statement and not in the proof**, say so, and
  give the constructive form beside it; both are entered in
  `statements.md`.
- **A case that will not close** becomes a named hypothesis: a proposition
  defined as above, taken as an argument by the theorem and used at that
  branch. The theorem is then PROVED as it is stated, hypothesis included;
  the hypothesis is OPEN; both are in `statements.md`. Not a `sorry`, and
  not a silent change of strategy.
- **REFUTED** means a theorem `¬ Statement`, or a verdict of the no side
  of an engine, checked by the kernel.
- **Extending a calculus that is adopted** (a new connective, new rules)
  is a campaign of its own, started when the base's rule table is complete
  and its theorems are within their bounds. Use the base's proofs as
  templates: the same witnesses, the same recursion, the same measure, new
  cases only. A template case that fails points at one rule.
