# <CALCULUS>: campaign folder

*Template: the status board. It opens the campaign folder, which sits
beside the modules of the calculus. Keep it to one screen; change it in
the same commit as the thing it reports.*

<One paragraph: what the calculus is, for which logic.> The target, the
paper, the place of the files, the reviewer and the rules of the project:
[gates.md](gates.md), the first entry.

Operator: <who, for each stage, in the cost log>. The method: the skill
`calculus-campaign`, as it stood at <the commit of the repository that
holds it, or the date it was read>.

## Status

| stage | state | gate | where |
|---|---|---|---|
| 0. Survey | not started / in progress / done | the target: <passed, date>; the plan: <not passed / passed, date> | [plan.md](plan.md) |
| 1. Adopt | | the rule table: <…>; the reviewer's test: <…> | [rule-table.md](rule-table.md), `<the theory file>`, `<the exercises file>` |
| 2. Prove | | the statements: <n of m seen>; goals PROVED: <n of m> | [statements.md](statements.md) |
| 3. Run | | the producers: <…> | `<files>` |
| 4. Explore | | the tutorial: <…> | `<files>` |

## Files here

* [gates.md](gates.md): the reviewer's word at each gate; first, the
  target.
* [plan.md](plan.md): the five questions, the results, and the plan.
* `skeleton.md`: the source's numbered results, with labels.
* [rule-table.md](rule-table.md): each rule beside its place in the
  source; the divergence log.
* [statements.md](statements.md): every statement, PROVED, REFUTED or OPEN.
* [cost-log.md](cost-log.md): one row for each session.
* `method-notes.md`: where the skill was wrong, silent or unclear.
* `brief-<stage number>-<k>.md`: the brief a session started from.
* `report-<stage number>-<date>.md`: the reports.

## Build

    <the command, naming its folder>

## Files of the development

<Each file, one line: what it holds, and whether it is theory (with its
bound on axioms) or code.>
