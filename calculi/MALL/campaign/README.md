# MALL: campaign folder

Propositional multiplicative-additive linear logic, in the one-sided
sequent calculus of J.-Y. Girard, *Linear logic* (TCS 50, 1987),
Definition 1.15, without the exponentials: connectives ⊗, ⅋, **1**, ⊥,
&, ⊕, ⊤, **0**, negation a defined function, no weakening and no
contraction. The target, the paper, the place of the files and the rules
of the project: [decisions.md](decisions.md), the first entry.

Operator: Claude Fable 5.2, one session for all stages
([cost-log.md](cost-log.md)). The method: the skill `calculus-campaign`,
as it stood at commit `906e2fa` of `proof-tools`.

Waiting on the reviewer: nothing.

## Status

| stage | state | the checks | where |
|---|---|---|---|
| 0. Survey | done, 2026-11-26 10:04 | the plan's choices screened and recorded: 6 entries; the encoding and "valid" screened in scratch | [plan.md](plan.md), [decisions.md](decisions.md), `skeleton.md`, [survey-report.md](survey-report.md) |
| 1. Adopt | not started | | |
| 2. Prove | not started | | |
| 3. Run | not started | | |
| 4. Explore | not started | | |

## Files here

* [decisions.md](decisions.md): each choice of the operator, with what it
  costs to reverse, and each word of the reviewer; first, the target.
* [plan.md](plan.md): the five questions, the results, and the plan.
* `skeleton.md`: the source's numbered results.
* [survey-report.md](survey-report.md): the report of the agent that
  fetched the other sources and surveyed the mechanisations.
* [cost-log.md](cost-log.md): one row for each session.
* `method-notes.md`: where the skill was wrong, silent or unclear.

## Build

    (cd ~/Lean/Sources/proof-tools/calculi/MALL && lake build)

## Files of the development

None yet.
