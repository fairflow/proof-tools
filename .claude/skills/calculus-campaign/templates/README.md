# <CALCULUS>: campaign folder

*Template: the status board. It opens the campaign folder, which sits
beside the modules of the calculus. Keep it to one screen; change it in
the same commit as the thing it reports, so that it is true at every
commit. No other report is written until the closing page.*

<One paragraph: what the calculus is, for which logic.> The target, the
paper, the place of the files and the rules of the project:
[decisions.md](decisions.md), the first entry.

Operator: <who, for each stage, in the cost log>. The method: the skill
`calculus-campaign`, as it stood at <the commit of the repository that
holds it, or the date it was read>.

Waiting on the reviewer: <nothing / the stop, its date, and what goes on
meanwhile>.

## Status

| stage | state | the checks | where |
|---|---|---|---|
| 0. Survey | not started / in progress / done | the plan's choices screened and recorded: <n> | [plan.md](plan.md), [decisions.md](decisions.md) |
| 1. Adopt | | worked derivations as terms: <n of m>; the second transcription: <run, n differences settled / not run, why>; S2: <PROVED / OPEN> | [rule-table.md](rule-table.md), `<the theory file>`, `<the exercises file>` |
| 2. Prove | | statements screened and read back: <n of m>; goals PROVED: <n of m>; OPEN: <n>; REFUTED: <n> | [statements.md](statements.md) |
| 3. Run | | negative tests: <n>; the frontier: <in a line> | `measurements.md`, `<files>` |
| 4. Explore | | the tutorial: <every line elaborated and pinned / not yet>; the tutorial page: <n pins hold, by `tutorial_pins.py check` / not yet> | `<files>` |

## Files here

* [decisions.md](decisions.md): each choice of the operator, with what it
  costs to reverse, and each word of the reviewer; first, the target.
* [plan.md](plan.md): the five questions, the results, and the plan
  (on a shorter path, `record.md` stands in its place).
* `skeleton.md`: the source's numbered results, with labels.
* [rule-table.md](rule-table.md): each rule beside its place in the
  source; the second transcription; the divergence log.
* [statements.md](statements.md): every statement, PROVED, REFUTED or OPEN.
* `measurements.md`: what runs, its verdicts and its timings.
* [cost-log.md](cost-log.md): one row for each session.
* `method-notes.md`: where the skill was wrong, silent or unclear.
* `users-guide.md`: how a goal reads, the moves, the tactic's lines
  (from stage 4).
* `report.md`: the closing page, when the campaign is done.
* `brief-<stage number>-<k>.md`: a brief, where a session was handed on.

## Build

    <the command, naming its folder>

## Files of the development

<Each file, one line: what it holds, and whether it is theory (with its
bound on axioms) or code.>
