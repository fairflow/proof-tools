# Part (a): adopting the calculus

Covers the Survey, the transcription half of Adopt, and Prove. The tools
are the commands of `ProofTools.Audit`: `import ProofTools.Audit`, with no
`open`.

Contents: 1 the source; 2 the kinds of result; 3 the transcription;
4 the rule table; 5 statements and their screening; 6 proving; 7 a
second reading.

## 1. The source

**Which source** was fixed at the first act (`decisions.md`, the first
entry). The version fixed there rules. Replacing it by another is a
decision that costs the campaign to reverse, and is recorded as one.

**Get the source, not a rendering of it.**

- Read the version fixed at the first act, in LaTeX where that version's source can be
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
  write the list by hand. The script's own header says that it
  simulates the counters: that text is old. On a source that compiles
  it runs `pdflatex` and reads the `.aux`, and it says which it did
  ("… labels read from main.aux (compiled here)"; where there is no
  `pdflatex` or no `.aux`, "items will carry no numbers"). Read that
  line before a number from the file is cited.
- **Fetching is a download.** `--arxiv` downloads an archive, and so
  does getting the PDF. The reviewer's word for it is standing
  (`SKILL.md`, "Downloading"): public material is fetched without
  asking, and each file is recorded in `decisions.md` with its name,
  its source and its size. Where the source cannot be got (a paywall,
  a server that refuses), take the fullest public version of it (a
  thesis, a preprint, an author's copy), and say which. Where none can
  be got, read what can be read as pages, write the skeleton by hand
  with the printed numbers, and say so in the plan. An archive that
  was fetched is data that is not trusted: unpack it in a folder of
  its own, and run nothing from inside it.

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
- where the source is ambiguous or silent, and what you decided. Each is
  a divergence of kind U (§4) and an entry of `decisions.md`.

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
| cut elimination, admissible structural rules | two families, with and without the rule, or one with a parameter (§3); a measure carried by the statement; induction on it | decide how the measure is carried before the family is typed (§3). Say which form is the goal: that the rule is admissible, or a procedure that removes it. Where rules act at a place inside a judgment, §6 has the form of the proofs |
| a property stated of models (the finite model property) | a construction of a model with the property | return the model as data: it is then a producer of countermodels for Run |
| a result about a term calculus (normalisation, confluence) | terms, typing, and reduction as a relation: a further transcription, with a rule table of its own, checked as the first is (§7) | how binding is represented is a choice of encoding for the plan |
| a result read off derivations (the disjunction and existence properties) | a function on derivations, or on derivations of a special form | it may need another result first (cut-free derivations, a normal form): order the goals so. With the family into `Type` what is read off is data |
| termination, decidability | a well-founded order on judgments, and a procedure | the bound that makes the proof easy is seldom runnable: prove with it, and search without it (Run) |
| conservativity, a translation | two calculi and a map, a theorem each way | computed indices (§3) |
| completeness of a search strategy | a restricted calculus, complete for the unrestricted one | a restriction that the source states by a classification of formulas is a statement-level decision: record it, with the classification as the source states it |
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
representation (§4): choose one in the plan, and record it.

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

**The source's letters.** Lean reserves `λ`, `Π` and `Σ`: none of them
can be a variable, and a source that writes sequents `Γ, Δ, Λ, Π, Σ` (as
modal calculi do) cannot be followed letter for letter. Do not work
around them case by case. Replace them once, in the plan, and enter the
replacements in the "Notation" table of the rule table: `Ξ` for `Σ`,
`Υ` for `Π`, and `Θ` and `Φ` where more letters are needed. The capital
`Λ` is not reserved and stays. Use the same letters in the documents, so
that a statement reads the same in the plan and in Lean.

**The figure's letters stay; what the encoding adds takes new ones.** A
constructor often needs a name for a thing the figure has no letter
for: the whole judgment at the place where a rule acts, a path, a
position. Give each a letter the figure does not use. If an added
thing takes one of the figure's letters, the figure's own use of that
letter moves to another, and the constructor then reads against the
figure with two letters changed. (One draft called the node `Δ`, and
the figure's `Δ` became `Λ`; with `Θ` for the node every letter of the
figure kept its meaning.) Enter the added letters in the "Notation"
table, marked as not in the figure.

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
system is empty until step 5 of Adopt.

**Where judgments are not flat** (`reference/explore.md` §13), `#rules`
prints each premise as functions applied to a variable
(`Γ.setNode a (…)`), and the names carry the rule: the table cannot be
read against the figure without the definitions. The template has three
sections for this case, to be left out otherwise:

- *How a rule of the figure reads in Lean*: once, for all rows, what in
  a constructor stands for the context, for the place of the rule, and
  for what the rule changes there;
- *The functions the rules use*: their definitions, copied from the Lean
  file by a command or a script, never retyped;
- *What the table rests on*: the rows, and with them the choices those
  functions make that the plan left open (how a rule names its place;
  where a rule puts what it adds; which occurrence it removes). Each
  is an entry of `decisions.md`, and is on the closing page's list of
  what to read.

A **divergence** is recorded when it is made, never afterwards. Three
kinds, kept apart:

- **W**, the source is wrong or says too much: prove what is used, and
  say so;
- **U**, the source is under-specified: say how it was specified, and that
  the choice was ours;
- **R**, a choice of representation where the source is clear: a list for
  a multiset, an equation field for a computed index. Say what in the
  Lean stands for what in the source.

The table is complete, and checked (the source's worked derivations,
and the second transcription of §7), before anything is built on the
family. It is the page that lies beside the source's figure for anyone
who reads the transcription. An error of transcription found later is
repaired in the family and entered in the table's last section with
when it was found; what was built on the faulty rule is built again.

## 5. Statements, and screening them

Faults of statement, not of proof, are the recurring ones, and each was
refutable by a small countermodel before any proof was attempted.

**Which statements.** The goals of the plan, the two that join `step` to
the family (S1 and S2, `reference/explore.md` §4), and any statement of
your own that the closing page will cite. Lemmas on the way are not entered. A
goal whose proof the literature only states is entered like the others:
it is OPEN until the kernel has a proof, whoever says it is proved.

**Each is displayed before its proof**, in `statements.md`
(`templates/statements.md`), with status OPEN, and is screened (below)
and read back (§7) before its proof is begun.

**Where an OPEN statement lives in Lean.** As a named proposition with no
proof, in a theory file:

```lean
def Completeness : Prop := ∀ j, Valid j → Nonempty (Fam j)
```

Lean checks that it is well typed, and it carries no `sorry`, so the
file's bound on axioms still holds. Its proof, when there is one, is
`theorem completeness : Completeness`. A `sorry` in a theory file breaks
the file's bound, which is what the bound is for.

**A goal that is data** is a type, not a proposition: a function that
returns a derivation or a model for every judgment, a decision
procedure, a translation of derivations (§2: "return the model as
data"). State it as a named type, with `abbrev`, so that the name
unfolds wherever Lean needs the function type or looks for an instance:

```lean
abbrev ProofOrRefutation : Type := (j : Judg) → Fam j ⊕ Refutation j
abbrev ValidDecidable    : Type := (j : Judg) → Decidable (Valid j)
```

Here `Refutation j` is a structure of yours: a model, with the proof
that it refutes `j`. The proof of such a goal is a definition,
`def proofOrRefutation : ProofOrRefutation`, in a theory file, under the
file's bound like a theorem. It is entered in `statements.md` as the
others are: OPEN while only the type is there, PROVED when the
definition is checked. A proposition that follows from it (completeness,
from the function into a proof or a refutation) is a statement of its
own, beside it. Compiled: `calculi/BrunnlerK/BrunnlerK/Semantics.lean`
of `proof-tools`.

**A statement about every structure may say more than the source
means.** In Lean, truth in a model is a proposition, and a valuation
may take any proposition as its value. "Valid in every model" can then
imply a classical principle. For a modal calculus:

    (∀ M s,  M, s ⊨ ◇p ∨ □p̄)   →   ∀ P : Prop, P ∨ ¬P

(a model of one reflexive state, with `p` true there exactly if `P`).
The source does not mean that: its metatheory is classical, and each of
its models is two-valued. Three forms of the statement are then open.
Look for them in this order:

1. **direct, over the class of structures the source means**: every
   model in which each formula is true or not true at each state,

   ```lean
   def Valid (j : Judg) : Prop := ∀ M : Model, M.TwoValued → ∀ s : M.W, M.sat s j.form
   ```

   It is the source's statement under excluded middle: say so beside it;
2. indirect: no model refutes the judgment;
3. the classical form and a constructive form, both entered (§6).

The first reads as the source does. Which form is used is a choice about what is meant: it
is in the plan ("what holds"), screened there (stage 0, step 3), and
recorded with it. Compiled: `calculi/BrunnlerK/BrunnlerK/Semantics.lean`
of `proof-tools`.

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
its notion of model was fixed in the plan, and nothing of Run has to
come first.
With it, the simplest screen of a soundness theorem goes rule by rule: for
each rule, small instances of its premises and conclusion, and small
models, and no model may refute the conclusion while refuting no premise.
A completeness statement is screened on the known non-theorems (each
should have a small countermodel) and, once there is a search, on small
valid judgments (each should get a derivation). Until that check exists,
screen small cases by evaluation, and say in `statements.md` what each
statement was screened with.

A rule that is being designed, not transcribed, gets the same: print it
with `#rules`, and screen it before anything rests on it.

## 6. Proving

- **A theory file ends with its bound on axioms**, as the plan's policy
  sets it: `#axioms_within_file [...]`, an upper bound, so that a proof
  may use fewer axioms than its file allows and none outside them. For
  one declaration, `#axioms_within d [...]`; for whole libraries, from a
  file that imports them, `#axiom_sweep [Lib] allowing [...]`. An
  exception is a decision of its own (`SKILL.md`, "Axioms"), one
  declaration at a time:
  `#axioms_within_file [...] except [d]`.
- **When a bound fails**, do not guess: the axiom is as often in a tactic
  or a library lemma as in the argument. `#choice_path d` gives the
  shortest chain from `d` to `Classical.choice`, with each step's module:
  where the names stop being yours is where the axiom enters.
  `#choice_sources d` gives the direct dependencies that carry it;
  `#axiom_path ax d` does the same for any axiom, `sorryAx` included.
- **Where the policy is to avoid `Classical.choice`.** On core Lean the
  known sources are the `String` functions that R4 of `lean-certify`
  lists, `omega` given a conjunction to prove (split the goal first),
  and some library lemmas about lists (`List.mem_erase_of_ne` brought it
  in, on Lean v4.31.0; a six-line induction replaced it). `by_cases` on
  an equation in a type with decidable equality does not.
  On Mathlib also: `tauto` and `push_neg` are classical, and `simp` can
  be, through a library lemma. Everywhere: `choose` and `Nonempty.some`
  are choice, so a construction that must return a derivation returns
  one, as data. `#cf_search "pat"` lists the constants whose name contains
  the pattern and that do not depend on `Classical.choice`.
- **A function on derivations is written by pattern matching, not by
  the tactic `induction`.** The family is into `Type` so that such
  functions are data: a rule shown admissible as a function, a proof
  carried into a context, a translation, the tree of moves of a
  derivation. A search or a producer then runs them. Written with
  `induction`, one elaborates and is then refused, with "code generator
  does not support recursor `Fam.rec`". Written by matching on the
  constructors, with the recursive calls on the premises, it compiles,
  and reduces in the kernel. A theorem about derivations is a
  proposition, is not compiled, and may use `induction`.
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

**Where rules act at a place inside a judgment: one relation between
whole judgments, not cases on positions.** This is for the calculi of
`reference/explore.md` §13, and for their admissible rules: weakening,
exchange, the inversions, contraction. A source proves these "by a
routine induction", by cases on where the place of the rule lies against
the place of what is weakened or contracted. With places as paths, each
such case is a pair of paths and a lemma that two replacements commute,
and there are many. Do not write them. Write instead:

1. a relation `Γ ≼ Γ'` between whole judgments, defined by recursion on
   the first: what is asked of the formulas of a node, and that each
   inner judgment of `Γ` is related to one of `Γ'`;
2. one lemma about a place: if `Γ ≼ Γ'` and `Θ` is the node of `Γ` at a
   path `a`, then `Γ'` has a node `Θ'` at some path `a'` with `Θ ≼ Θ'`,
   and for all `X ≼ X'` the judgments changed there are related,

       Γ.setNode a X ≼ Γ'.setNode a' X'

   (where two nodes may have the same image, `X'` must also keep what
   was at the image: `Θ' ≼ X'`);
3. one theorem, by induction on the derivation, with the lemma at each
   rule: a proof of `Γ` gives a proof of every `Γ'` with `Γ ≼ Γ'`, and
   one that is no deeper,

       (d : Fam Γ) → Γ ≼ Γ' → ∃ d' : Fam Γ', d'.depth ≤ d.depth

Each admissible rule is then the theorem at a pair of judgments that
are related by a short computation. Three relations served a calculus
of nested sequents:

| the relation | what it asks | its instances |
|---|---|---|
| `Γ` embeds in `Γ'` | each formula at least as many times in the image; the inner judgments into inner judgments at different positions | weakening, exchange |
| the same, with a relation at the nodes | a number of the occurrences of one formula replaced by its parts | the inversion of each invertible rule |
| `Γ` maps into `Γ'` | each formula in the image, by membership; two inner judgments may go to the same one | contraction, by induction on the depth, with the inversions |

Four things met on the way:

- **A statement about one occurrence needs a proof about several.** The
  inversion of `∧` at one occurrence of `A ∧ B` does not go through the
  induction: a rule on `(A ∧ B) ∧ C` puts a second `A ∧ B` into the
  node. Let the relation say that some number of the occurrences are
  replaced. Replacing every occurrence everywhere, by a function, does
  not keep the depth, for the same reason.
- **The depth is a function on derivations** (§3), so that "no deeper"
  can be stated. What an axiom counts (0 there) is part of the
  statement: say it in `statements.md`.
- **A rule that puts a judgment under a new place** (necessitation) is
  not an instance: there it was the function that carries a proof of
  an inner judgment to a proof of the whole (`Fam.lift`), which keeps
  the depth.
- **The statements are in the source's form, the relations are not**: what
  is entered in `statements.md` is each rule in the source's form (for
  a context `Γ{ }`), obtained from the theorem; the relation is a lemma
  on the way (§5).

Compiled, in `calculi/BrunnlerK/BrunnlerK/` of `proof-tools`:
`Structural.lean` (`Sub`, `Sub.node`, `Fam.sub`), `Invert.lean` (`SubR`,
`Fam.invert`), `Contract.lean` (`Hom`, `Hom.node`, `Fam.hom`).

## 7. A second reading

Two of the four checks of meaning (`SKILL.md`, "Deciding, checking,
stopping", 2) need a reader who has not seen your work: a **cold
reader**. With a language model as operator, that is a fresh agent that
you start, with a brief that holds only what is listed below. It is not
an agent that inherits your context (a fork): that one has seen
everything. A reader who has seen your transcription tends to confirm
it. So the brief does not contain it, nor your view of where the source
is hard; and it names the files the reader may open, and says that it
opens no others. An agent started in the same checkout can otherwise
read the campaign folder and the Lean.

**The second transcription** (Adopt, step 4).

- *Given*: the source, by file and page: the figure, and the prose
  around it that carries side conditions; the source's definitions of
  formulas and judgments; the name of the system.
- *Asked*: write out each primitive rule of that system, in the
  source's notation, as a table: premises, conclusion, side conditions,
  and the place in the source. List every place where the source is
  ambiguous or silent. No Lean.
- *Not given, and not to be opened*: the campaign folder (`plan.md` and
  `skeleton.md` hold your reading of the side conditions and of the
  ambiguities; `rule-table.md` holds the transcription), and the
  modules of the calculus.

Compare its table, row by row, with **what `#rules` prints for each
constructor of your family**, read through your table's notation: the
number of rules; each premise; each side condition. The "as printed"
column of your own table is a copy of the source, and agreement with it
shows only that two readers copied alike. Settle every difference from
the source, by page and line. An ambiguity that only one reader found is
settled in the same way; where the source does not settle it, it is a
divergence of kind U (§4) and an entry of `decisions.md`. Enter the
comparison in `rule-table.md` (the section "The second transcription"),
and a difference that was a fault of yours under "Errors of
transcription".

**The reading back** (Prove, step 3).

*What is read back*: the definitions the goals are about (formulas,
judgments, the models and truth in them, what a judgment means in a
model, `Valid`), and the statement of each goal of the plan. Not S1 and
S2, and not the certifiers' statements of Run: they have no item of the
source to be compared with, and are screened only.

- *Given*: an extract made for the purpose. It holds those definitions
  and statements as Lean, with every definition a statement unfolds to
  (the family, the functions the rules use). Comments and doc comments
  are taken out, and the theorems' names are made neutral (`T1`, `T2`):
  a comment that cites the source, or a name such as `completeness`,
  tells the reader what to find.
- *Asked*: say in ordinary mathematical notation what each definition
  defines and what each statement claims; and name anything that looks
  unusual: a class that is restricted, a hypothesis, an order of
  quantifiers.
- *Not given, and not to be opened*: the source, the campaign folder,
  the modules of the calculus. This reader is not the one that made the
  second transcription, which has read the source.

Compare what comes back with the source's item. Where they agree, write
"read back, agrees" in the statement's entry. Where they differ, the
difference is in the Lean, or in the reading, or is a choice you made (a
class of models restricted, §5): settle which, and write it in the
entry.

**After a repair**, the check is run again on what changed, by a new
cold reader: the first has seen the faulty version.

**Where no cold reader can be had** (no agent can be started), neither
check is run, and the closing page lists both as not run. Reading your
own table a second time is not this check.

**What a second reading gives.** Agreement of two readings is evidence,
and no more: two readers make the same mistake where the source
misleads both. The other two checks do not depend on a reader: the
source's worked derivations, and soundness with completeness.
