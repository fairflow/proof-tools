# <CALCULUS>: the cost log

*Template. Started on the first day of the Survey, one row for each
session. Times come from the clock (`date`), never from an estimate. A
figure the environment does not give is written "not known": do not guess
it. The purpose is to measure the method, so a bad row is as useful as a
good one.*

## Sessions

The four columns from "requests" to "cost" are about an operator that is
a language model; a person writes hours under "cost" and leaves the
others. **An operator that is a model does not, as a rule, know them**:
its environment shows it neither its requests nor its tokens nor what
they cost. It writes "not known" in each, and does not work a figure out
from the length of the session. They are the reviewer's to fill, from
the tool's usage report, if the method is to be costed; the line below
the table says who filled them and from what. What the operator can
measure, it measures: the clock, the builds, the lines.

| # | stage | operator (person, or model and settings) | fresh session from a brief? | began | ended | waiting on builds (the sum of the build commands' times) | requests | output tokens | input read again (cached) | cost | Lean lines added / removed (`git diff --stat`) | document lines |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | Survey | | yes / no / no, at the reviewer's word | | | | | | | | | |

Where the tokens and the cost come from: <the tool's usage report, read
by the reviewer on <date>; the transcript; "not known to the operator,
and not filled">.

## Exchanges with the reviewer

Every message from the reviewer during the campaign, classed:

* **decision**: one the method asks for: a gate, a choice in the plan, an
  answer to a question the operator put;
* **correction**: the operator was wrong or unclear and was put right;
* **rescue**: the operator was stuck and could not have gone on alone.

| # | date | stage | class | the reviewer's words, in brief | what it changed |
|---|---|---|---|---|---|

## By stage

| stage | sessions | elapsed | of which waiting on builds | requests ("not known", where the rows say so) | cost (the same) | reached its gate? | decisions / corrections / rescues |
|---|---|---|---|---|---|---|---|
| 0 Survey | | | | | | | |
| 1 Adopt | | | | | | | |
| 2 Prove | | | | | | | |
| 3 Run | | | | | | | |
| 4 Explore | | | | | | | |

## Errors of transcription

The list is in `rule-table.md`. Here, the count: found at the rule table
<n>; at the reviewer's test <n>; later <n>.

## What the operator did unaided, and what it did not

<A few lines for each stage. Include what the operator knew that the skill
did not tell it.>
