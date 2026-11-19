# The campaign: one calculus, from its paper to use

Draft, 2026-11-19. This page says how the parts of this repository are meant
to be used together on one proof calculus. It was drawn from work on calculi
for propositional lax logic in
[lax-logic-in-lean](https://github.com/fairflow/lax-logic-in-lean), and will
be revised as it is applied. The explorer it mentions is not built yet.

## Who does what

- The **operator** does the work of a stage: a person, or a language model
  working with one.
- The **reviewer** owns the statements and decides at the end of each stage
  whether to go on. The reviewer reads statements and tries things; the
  reviewer is not asked to read proofs.

No stage is automatic, and none is meant to be. What the tools do is make
each stage's result checkable without trusting the operator.

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

| | Stage | The work | In front of the reviewer | Kept |
|---|---|---|---|---|
| 0 | **Survey** | The five questions. | The plan: goals, non-goals, order. | `plan.md` |
| 1 | **Adopt** | The rules as an inductive family; `#rules` and `#slime` run on it; a first explorer instance. | The rules as inference figures beside the source, and **the test**: the source's own derivations, typed in by hand. | A table matching each rule to its place in the source; a file of exercises. |
| 2 | **Prove** | The plan's theorems. Statements first, shown before they are proved. Countermodels are looked for before a proof is attempted. | Each statement, marked PROVED, REFUTED or OPEN. | The statements; in each theory file, the bound on its axioms that the development's policy sets. |
| 3 | **Run** | Procedures that search for proofs or countermodels, each an untrusted producer whose output a checker certifies. | Verdicts on a corpus of judgments of known status. | The procedures, the corpus, the settings. |
| 4 | **Explore** | The explorer in full: display, queries, scripts, what question 4 asked for. | **The tutorial**, worked through. | A user's guide; a retrospective, with changes to this method. |

The explorer appears twice on purpose. A first instance in Adopt is the
quickest test of a transcription: a rule that does not behave as the source
says shows itself when a person applies it. The full one comes last, when
the theorems and procedures it relies on exist.

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
- A bound is an upper bound (`#axioms_within`, `#axiom_sweep`): a proof may
  use fewer axioms than its file allows, and must use none outside them.
  An exact list is not pinned, so a proof that gets cleaner breaks nothing.
- Exceptions are the reviewer's to grant, one declaration at a time.

## Countermodels

The tools assume nothing about how a countermodel is found. In some calculi
an unfinished derivation that can go no further is a countermodel as it
stands; in others the countermodel is assembled from several failed
attempts; in others there is no such reading. The survey says which method
the literature gives. Where it gives none, a tableau system with countermodel
extraction can be built for the logic, if that is feasible and wanted, and
it is then a calculus of its own, with its own campaign.

## Reports

A stage ends when its report is written and sent, not when the build is
clean. Every report has the same parts:

1. what was done, with the commit;
2. the statements, each PROVED, REFUTED or OPEN;
3. what to look at or try;
4. what differed from the plan or from the source;
5. what the reviewer must decide.

A system that was designed, not adopted from a source, has no source to be
faithful to. In place of the table of rules against the source it has its
rules, the reading of a judgment, the termination measure and the truth
lemma, reviewed as statements before their proofs.
