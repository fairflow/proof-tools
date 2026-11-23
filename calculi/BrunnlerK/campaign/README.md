# Brünnler's system K: campaign folder

System K is Brünnler's nested sequent calculus for the least normal modal
logic K: one-sided sequents of formulas in negation normal form, with
boxed sequents inside them, and rules that act at any depth. The target,
the paper, the place of the files, the reviewer and the rules of the
project: [gates.md](gates.md), the first entry, as changed by the second
(the place of the files, and where commits go).

Operator: Claude (Fable 5.2) for stages 0 and 1; see the cost log. The method:
the skill `calculus-campaign`, read at commit `e6410cd` of proof-tools
and amended on 2026-11-23 at the reviewer's word (the default folder; the
letters Lean reserves).

## Status

| stage | state | gate | where |
|---|---|---|---|
| 0. Survey | done | the target: passed, 2026-11-23; the plan: passed, 2026-11-23, at its second putting | [plan.md](plan.md), [report-0-2026-11-23.md](report-0-2026-11-23.md) |
| 1. Adopt | steps 1 to 4 done: the package, formulas and sequents, the two families, the rule table | the rule table: put 2026-11-23, not signed; the reviewer's test: not put | [rule-table.md](rule-table.md), [statements.md](statements.md), [brief-1-2.md](brief-1-2.md) |
| 2. Prove | not started | the statements: 0 of 10 seen in Lean; goals PROVED: 0 of 10 | [statements.md](statements.md) |
| 3. Run | not started | the producers: not put | |
| 4. Explore | not started | the tutorial: not put | |

## Files here

* [gates.md](gates.md): the reviewer's word at each gate; first, the
  target.
* [plan.md](plan.md): the five questions, the results, and the plan.
* [skeleton.md](skeleton.md): the source's numbered results, by label
  where the source has one, with printed number and page.
* [cost-log.md](cost-log.md): one row for each session.
* [method-notes.md](method-notes.md): where the skill was wrong, silent
  or unclear.
* [report-0-2026-11-23.md](report-0-2026-11-23.md): the Survey's report.

* [brief-1-1.md](brief-1-1.md), [brief-1-2.md](brief-1-2.md): the briefs
  for Adopt, to the rule table's gate and after it.
* [rule-table.md](rule-table.md): each rule of the source beside its
  constructor, with the output of `#rules`, and the divergences.
* [statements.md](statements.md): the ten goals, S1 and S2, each with
  its status.

## Build

In `calculi/BrunnlerK/`: `lake build`. Core Lean only, on the library's
toolchain (v4.31.0); the package requires `proof-tools` by its path.

## Files of the development

| file | what | bound on axioms |
|---|---|---|
| `BrunnlerK/Form.lean` | formulas, the negation, `⊃` | `[propext, Quot.sound]` |
| `BrunnlerK/Sequent.lean` | nested sequents; paths; the functions the rules use; set sequents | `[propext, Quot.sound]` |
| `BrunnlerK/System.lean` | the family `Fam`: system K, and K + cut | `[propext, Quot.sound]` |
| `BrunnlerK/SystemO.lean` | the family `FamO`: system K° | `[propext, Quot.sound]` |
| `BrunnlerK/Show.lean` | formulas and sequents as text | none: code |
| `BrunnlerK/Test/Sequent.lean`, `BrunnlerK/Test/System.lean` | tests | none: tests |

Not yet made: the proof system (`Move`, `step`), the tactic, the
exercises file `Play/BrunnlerK.lean`.
