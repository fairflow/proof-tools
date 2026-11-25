# <CALCULUS>: the closing page

*Template, kept as `report.md`. The one document the reviewer is expected
to read. It asks nothing. Keep it to a few screens: point at files, and
do not repeat them. Write what is so; where something was not checked,
say "not checked". No report is written at the end of a stage: the
status board (`README.md`) carries that.*

Written <date and time, from the clock>. Commit `<…>` on `<branch>`.
To build: `<the command, naming its folder>`.

## 1. What was adopted, proved, and runs

<Two or three lines: the calculus, the logic, the source, the system.>

**The goals**, those from the standing list first. Each PROVED statement
is checked by the kernel, with no `sorry`, within the axioms named:

    <statement>                                   (<name>, <file>)
    PROVED, within <axioms>

**OPEN**: <each goal not reached: what was tried and where it stopped, or
"not on the route taken, not attempted". A statement that only tests
support is OPEN.>

**REFUTED**: <each, with its countermodel and what replaced it; or
"nothing">.

**Runs**: <the procedures and the level; the frontier, in a line;
`measurements.md`>.

## 2. What to read

No tool checks that these say what the source means. They are what a
reader trusts beyond the kernel.

| definition | file, lines | length | the source's item |
|---|---|---|---|
| formulas | | | |
| judgments | | | |
| the family of rules (with `rule-table.md` beside the figure) | | | |
| the functions the rules use, where judgments are not flat | | | |
| the models, truth in a model, `Valid` | | | |
| `step` (S1 and S2 tie it to the family) | | | |

Total: <n> lines.

## 3. The checks of meaning

| check | run? | what it found |
|---|---|---|
| `#rules` and `#slime`, beside the figure | | |
| the source's worked derivations (<n>), as terms and by script | | |
| the second transcription, by a cold reader | | <the differences, and how each was settled from the source> |
| the reading back of the definitions and the statements | | |
| soundness and completeness, before the other goals | | |
| S2: `step` refuses no instance of a rule | PROVED / OPEN | |

Errors of transcription found: <n, and by which check>. What these
checks do not show: <in a line or two: no second reading could be had;
completeness is OPEN, so the rules are not fixed against the semantics;
results about this system rest on the comparison rule by rule>.

## 4. The decisions

The costliest to reverse first, each by its entry in `decisions.md`.

| decided | not taken | cost to reverse | doubt |
|---|---|---|---|

Divergences from the source (`rule-table.md`): W <n>, U <n>, R <n>. Those
that change what a statement says: <each, in a line; or "none">.

Exceptions to the axiom policy: <none / each declaration, the theorem
it touches, and the path that `#choice_path` shows>.

## 5. The reviewer's

Stated, and not asked for.

* **Only the reviewer may**: <contact the source's authors about …;
  publish; push to …; or "nothing arose">.
* **To try, at any time**: the exercises (`Play/<Calculus>.lean`) and the
  tutorial (`Play/<Calculus>Tutorial.lean`). Every exercise was run by
  script in the tests; no person has typed them.
* **To fill, if the method is to be costed**: the columns of
  `cost-log.md` that the operator cannot know (requests, tokens, cost).
* **Words of the reviewer during the campaign**: <n, and the stops among
  them; `decisions.md`>.

## 6. Cost, and the method

<From `cost-log.md`: the clock time from the command to this page; of
it, the time waiting at a stop; the sessions; the Lean lines.>

Findings about the library (none was changed): <each; or "none">.

Changes proposed to the skill, from `method-notes.md`, each with its
place in the text: <each; or "none">.
