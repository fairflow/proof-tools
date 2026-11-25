# The campaign: one calculus, from its paper to use

Draft, 2026-11-19; revised 2026-11-25, when the skill was rewritten so
that the operator works without waiting for the reviewer. This page says how the parts of this repository are meant
to be used together on one proof calculus. It was drawn from work on calculi
for propositional lax logic in
[lax-logic-in-lean](https://github.com/fairflow/lax-logic-in-lean), and will
be revised as it is applied. The explorer it mentions is `ProofTools.Explore`
([explore.md](explore.md)).

**This page describes the method. It is not the procedure.** The procedure,
with its checks, its templates and the rules of every stage, is the Claude
skill in `.claude/skills/calculus-campaign/`, run by the command
`/calculus-campaign <the calculus, named in words>`. A campaign is run from
the skill, not from this page. If you were asked for that command and it is
unknown in your session, do not carry the campaign out from here: say so,
and see "If the command is unknown" in the [README](../README.md).

## Who does what

- The **operator** runs the campaign from the command to its closing page:
  a person, or a language model. It makes the choices, records each with
  what it would cost to reverse, and runs the checks below. It does not
  wait for approval.
- The **reviewer** is the person who asked for the campaign. The reviewer
  owns what leaves the project (contact with the source's authors,
  publication), may redirect the campaign at any time, and is expected to
  read one page at the end. The reviewer is not asked to read proofs, nor
  to approve steps. A reviewer who wants to pass a thing themselves says
  so, and that thing then waits for them.

What a result may be relied on for is settled by the kernel, by the checks
the operator ran, and by the closing page being short enough to read.

## Before anything: five questions

They are asked of the literature, and answered in writing, before a line of
Lean. Their answers decide what the later stages are for.

1. **What are the rules?** The source, its version, its notation, its side
   conditions, and where it is ambiguous or silent.
2. **What is proved about it?** Soundness, completeness, cut elimination,
   decidability, complexity, interpolation. Each published result becomes a
   goal of the campaign, or is set aside with a reason.
3. **What should run, and why?** Proof search, countermodel generation, or
   both; a decision procedure, or search with a budget. The reason for
   certifying is stated: who will rely on the answers.
4. **How do people use it?** By hand, in teaching, inside another proof.
   This says what an explorer should show, and which options it needs.
5. **Which calculi is it related to?** Translations in the literature, in
   either direction.

## The five stages

| | Stage | The work | The checks, run by the operator | Kept |
|---|---|---|---|---|
| 0 | **Survey** | The five questions. | The plan's choices screened in scratch, and recorded: goals, non-goals, order, what "holds" means. | `plan.md` |
| 1 | **Adopt** | The rules as an inductive family; `#rules` and `#slime` run on it; a first explorer instance. | The rules beside the source's figure; a second transcription by a reader who has not seen the first; the source's own derivations, as terms and run through the explorer. | A table matching each rule to its place in the source; a file of exercises. |
| 2 | **Prove** | The plan's theorems. Statements first, displayed before they are proved. Countermodels are looked for before a proof is attempted. | Each statement screened, and read back from the Lean by a reader who has not seen the source; soundness and completeness before the other goals. | The statements, each PROVED, REFUTED or OPEN; in each theory file, the bound on its axioms that the development's policy sets. |
| 3 | **Run** | Procedures that search for proofs or countermodels, each an untrusted producer whose output a checker certifies. | A corrupted certificate rejected by each checker; verdicts on a corpus of judgments of known status. | The procedures, the corpus, the settings. |
| 4 | **Explore** | The explorer in full: display, queries, scripts, what question 4 asked for. | Every line of the tutorial elaborated, what it shows pinned in tests. | A user's guide; the closing page, with changes to this method. |

The explorer appears twice on purpose. A first instance in Adopt is the
quickest test of a transcription: a rule that does not behave as the source
says shows itself when it is applied. The full one comes last, when the
theorems and procedures it relies on exist. The exercises file is also the
reviewer's way in, at any time they choose.

## What is trusted

Lean's kernel, and for each calculus two checkers, each with one theorem:

- a **step function**, which says whether a move applies to a judgment and
  what its premises are; its theorem says that a successful step is an
  instance of a rule;
- a **model evaluator**, which says whether a finite model refutes a
  judgment; its theorem says that a refuted judgment is not derivable.

Everything else produces candidates: a person typing, a search procedure, a
language model, a translation from another calculus. A wrong candidate is
refused by a checker; it cannot become a wrong theorem. A declaration that
is still a `sorry` is OPEN, and "machine-checked" is said only of what the
kernel has checked, within the axioms its development allows.

## Axioms: a policy of the development, not of the method

Which axioms a development may use is an option of the campaign, settled in
its plan. It depends on the calculus and on the part of the work.

- A propositional calculus with finite countermodels can often be kept free
  of `Classical.choice`, and a development may set that as its aim. A
  first-order calculus whose completeness goes through infinite models will
  in general need it, and aims at something else. The method prescribes
  neither.
- The policy is stated once, at the top of the development (for example:
  avoid `Classical.choice` wherever possible), and then written into the
  files: **each theory file states the axioms its declarations may depend
  on.** Files of code (producers, printers, tactics) carry no bound, since
  nothing they compute is trusted.
- A bound is an upper bound: a proof may use fewer axioms than its file
  allows, and must use none outside them. An exact list is not pinned, so a
  proof that gets cleaner breaks nothing. The commands:
  `#axioms_within_file [...]` at the end of a theory file, for that file;
  `#axioms_within d [...]` for one declaration; `#axiom_sweep` for whole
  libraries, from a file that imports them.
- An exception is made one declaration at a time
  (`#axioms_within_file [...] except [d]`), recorded as a decision, and
  listed on the closing page beside the theorem it touches.

## Countermodels

The tools assume nothing about how a countermodel is found. In some calculi
an unfinished derivation that can go no further is a countermodel as it
stands; in others the countermodel is assembled from several failed
attempts; in others there is no such reading. The survey says which method
the literature gives. Where it gives none, a tableau system with countermodel
extraction can be built for the logic, if that is feasible and wanted, and
it is then a calculus of its own, with its own campaign.

## The closing page

A campaign ends when its closing page can be read by the reviewer, not when
the build is clean. No report is written at the end of a stage: a status
board in the campaign folder is kept true at every commit. The closing page
asks nothing, and has these parts:

1. what was adopted, proved and runs: each goal PROVED, REFUTED or OPEN,
   with its axioms and the commit;
2. what to read: the definitions that no tool checks, with their lengths;
3. the checks, which were run and what each found;
4. the decisions, the costliest to reverse first;
5. what only the reviewer may do, and what they may try;
6. what it cost, and the changes proposed to the method.

A system that was designed, not adopted from a source, has no source to be
faithful to. In place of the table of rules against the source it has its
rules, the reading of a judgment, the termination measure and the truth
lemma, entered as statements and screened before their proofs.
