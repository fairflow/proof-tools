# Brünnler's system K: campaign folder

System K is Brünnler's nested sequent calculus for the least normal modal
logic K: one-sided sequents of formulas in negation normal form, with
boxed sequents inside them, and rules that act at any depth. The target,
the paper, the place of the files, the reviewer and the rules of the
project: [gates.md](gates.md), the first entry, as changed by the second
(the place of the files, and where commits go).

Operator: Claude (Fable 5.2) for all five stages; see the cost log. The method:
the skill `calculus-campaign`, read at commit `e6410cd` of proof-tools
and amended on 2026-11-23 at the reviewer's word (the default folder; the
letters Lean reserves; a later command of the reviewer overrides a
gate; the reviewer may lift every gate).

## Status

| stage | state | gate | where |
|---|---|---|---|
| 0. Survey | done | the target: passed, 2026-11-23; the plan: passed, 2026-11-23, at its second putting | [plan.md](plan.md), [report-0-2026-11-23.md](report-0-2026-11-23.md) |
| 1. Adopt | done, but for its last gate: the package, formulas and sequents, the two families, the rule table, the proof system, the tactic `kmove`, the tests, the exercises file | the rule table: signed 2026-11-23; the reviewer's test: put 2026-11-23, deferred by the reviewer, not done | [rule-table.md](rule-table.md), [statements.md](statements.md), [report-1-2026-11-23.md](report-1-2026-11-23.md), `Play/BrunnlerK.lean` |
| 2. Prove | done, 2026-11-23, in the session of stages 0 and 1: goals 1, 2, 3, 4, 5, 8, 9 and 10 PROVED; goals 6 and 7 set aside by the reviewer. Nothing OPEN | the statements, first sending: signed as put; second sending: decided by the operator, the gates being lifted by the reviewer; the report: [report-3](report-3-2026-11-23.md) | [statements.md](statements.md), [report-2-2026-11-23.md](report-2-2026-11-23.md), [report-3-2026-11-23.md](report-3-2026-11-23.md), `Play/Search.lean` |
| 3. Run | done, 2026-11-23, in the same session: the certifiers, the compiled producer `ksearch`, level 3 proved, a corpus of 22 sequents with every fact checked, negative tests, measurements and the frontier | the producers: decided by the operator; the report: [report-4](report-4-2026-11-23.md) | `BrunnlerK/Run.lean`, `BrunnlerK/Corpus/`, [measurements-2026-11-23.md](measurements-2026-11-23.md) |
| 4. Explore | done but for its gate, 2026-11-23, in the same session: a sequent as its tree, tactics of the calculus, the search as a tactic, the tutorial, the user's guide, the closing report | the tutorial: put 2026-11-23, to be worked through by the reviewer; not done | `Play/BrunnlerKTutorial.lean`, [users-guide.md](users-guide.md), [report-5-2026-11-23.md](report-5-2026-11-23.md) |

After the campaign, by the owner session of this calculus: `ksearch prove
'<sequent>'`, a sequent typed at a shell, 2026-11-26
([report-6](report-6-2026-11-26.md); the user's guide, "From the command
line"), and the same day brought to the skill's paragraph on such a
command (the last section of report-6; method notes 76 to 80).

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
* [report-1-2026-11-23.md](report-1-2026-11-23.md): Adopt's report, with
  what should happen at each exercise of the reviewer's test.

* [report-2-2026-11-23.md](report-2-2026-11-23.md): the report of Prove
  at the reviewer's goal (completeness, cut elimination).
* [report-3-2026-11-23.md](report-3-2026-11-23.md): the report at the end
  of Prove (goals 2 to 5, the finite model property).
* [report-4-2026-11-23.md](report-4-2026-11-23.md): the report of Run.
* [measurements-2026-11-23.md](measurements-2026-11-23.md): the timings
  of Run, as `Corpus/measure.py` wrote them, and the frontier.
* [report-5-2026-11-23.md](report-5-2026-11-23.md): the closing report,
  with the retrospective.
* [report-6-2026-11-26.md](report-6-2026-11-26.md): after the campaign,
  the command `ksearch prove`: what was built and what was checked.
* [users-guide.md](users-guide.md): the user's guide.
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
| `BrunnlerK/Proof.lean` | the moves, `step`, the proof system `S`; S1 (`step_sound`) and S2 (`famToDer`) | `[propext, Quot.sound]` |
| `BrunnlerK/Tactic.lean` | `seq[…]`; moves as text; the moves to try; `within`; `Explorable S`; the tactic `kmove` | none: code |
| `BrunnlerK/Test/Sequent.lean`, `BrunnlerK/Test/System.lean`, `BrunnlerK/Test/Proof.lean` | tests | none: tests |
| `BrunnlerK/Semantics.lean` | models, truth, two-valued models, `Γ_F`, `Valid`; finite trees and their model; `Refutation`; the statements of goals 1, 8, 9, 10 | `[propext, Quot.sound]` |
| `BrunnlerK/Context.lean` | lemmas on paths; `Fam.lift` (a proof of a subtree is a proof of the whole); `Fam.diaAll` | `[propext, Quot.sound]` |
| `BrunnlerK/Weight.lean` | the weight the search goes down by | `[propext, Quot.sound]` |
| `BrunnlerK/Ctx.lean` | the comma, contexts, `fill`; the rules in the figure's shape (S3) | `[propext, Quot.sound]` |
| `BrunnlerK/Soundness.lean` | truth of a sequent on the sequent; deep inference is sound; soundness of K and of K + cut | `[propext, Quot.sound]` |
| `BrunnlerK/Search.lean` | the model of finite trees is two-valued; the search: a proof or a refutation | `[propext, Quot.sound]` |
| `BrunnlerK/Completeness.lean` | completeness, decidability, cut elimination | `[propext, Quot.sound]` |
| `BrunnlerK/Structural.lean` | the depth of a proof; embedding (`Sub`, `Fam.sub`); `nec`, `wk`, exchange | `[propext, Quot.sound]` |
| `BrunnlerK/Identity.lean` | the general axiom | `[propext, Quot.sound]` |
| `BrunnlerK/Invert.lean` | embedding with a relation at the nodes; `Fam.invert`; the inverse rules | `[propext, Quot.sound]` |
| `BrunnlerK/Contract.lean` | mapping a sequent into another (`Hom`, `Fam.hom`); `ctr` | `[propext, Quot.sound]` |
| `BrunnlerK/FiniteModel.lean` | models with finitely many states; the finite model property | `[propext, Quot.sound]` |
| `BrunnlerK/Test/Semantics.lean`, `BrunnlerK/Test/Ctx.lean`, `BrunnlerK/Test/Search.lean`, `BrunnlerK/Test/Structural.lean` | the screens of the statements; tests | none: tests |
| `BrunnlerK/Run.lean` | the certifiers; a proof as a tree of moves; the producers; the engine; level 3 (S4) | `[propext, Quot.sound]` |
| `BrunnlerK/Corpus/Basic.lean` | the corpus: 22 sequents with their status and its source; four families | none: data |
| `BrunnlerK/Corpus/Facts.lean` | the corpus's facts, each with its certificate; written by `ksearch facts` | `[propext, Quot.sound]` |
| `Main.lean`, `Corpus/measure.py` | the executable `ksearch` (`lake build ksearch`), with `ksearch prove '<sequent>'`; the script of the measurements | none: code |
| `BrunnlerK/Test/Run.lean` | negative tests of the certifiers | none: tests |
| `BrunnlerK/Parse.lean` | a nested sequent read from text; a sequent as Lean source and with the signs of a keyboard | none: code |
| `BrunnlerK/Test/Parse.lean` | the reader's tests: the corpus read back from each printer, and by Lean; binding; texts refused | none: tests |
| `Corpus/prove_corpus.py` | `ksearch prove` on every entry of the corpus, each file elaborated | none: code |
| `Corpus/prove_families.py` | `ksearch prove` on members of the families, each file elaborated and timed | none: code |
| `BrunnlerK/Explore.lean` | a sequent as its tree; tactics of the calculus (`routine`, `auto`, `found`) | none: code |
| `BrunnlerK/Test/Explore.lean` | tests | none: tests |
| `Play/BrunnlerKTutorial.lean` | the tutorial; in no library (`lake env lean Play/BrunnlerKTutorial.lean`) | none |
| `Play/Search.lean` | the search, to try; in no library (`lake env lean Play/Search.lean`) | none |
| `Play/BrunnlerK.lean` | the reviewer's exercises; in no library (`lake env lean Play/BrunnlerK.lean`) | none |

