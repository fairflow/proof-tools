# MALL: the cost log

Times come from the clock (`date`). A figure the environment does not
give is written "not known".

## Sessions

One session did every stage: Claude Fable 5.2, in Claude Code (desktop),
started by another session of the reviewer's with a written task; cold.
Its context was summarised by the environment once, at 11:01, between
the last build and the closing documents; the documents were read again
after it (rule 5).

| # | stage | began | ended (its last commit) | waiting at a stop | Lean lines at that commit | document lines at that commit |
|---|---|---|---|---|---|---|
| 1 | Survey | 2026-11-26 09:46 | 10:04 (`87b6208`) | none | 0 | 1 311 |
| 1 | Adopt | 10:04 | 10:18 (`e605abf`) | none | 1 734 | 1 834 |
| 1 | Prove | 10:18 | 10:32 (`ea0d357`) | none | 4 173 | 1 834 (`statements.md` was first committed at 10:56, in `1604735`; the statements themselves, as Lean, at 10:22, in `c81bc59`) |
| 1 | Run, Explore | 10:32 | 11:00 (the last build; `1604735` at 10:56) | none | 6 051 | 2 373 |
| 1 | the closing documents, the push, the page | 11:00 | 11:06 (pushed and published) | none | the same | see `report.md` |

Waiting on builds: not measured stage by stage. The library built in
3 s from a cloned `.lake`; a full build of the campaign from nothing is
about a minute; the measuring runs (about six minutes in all, by their
deadlines) ran beside other work.

Requests, output tokens, input read again, cost: not known to the
operator, for the session.

Agents started by the operator (each a fresh agent with a written
brief; the figures are what the environment said when each ended):

| # | for | reported, by the clock | tokens | its own time |
|---|---|---|---|---|
| a1 | fetch Lafont, LMSS and three more; read Lafont and LMSS; survey the mechanisations | 10:00 (began 09:49) | 215 326 (53 tool uses) | 575 s |
| a2 | the second transcription, cold, from four page images | before 10:18 | about 85 000 | 67 s |
| a3 | cut elimination as a function, the inversions, their tests (`MALL/Cut.lean`, `MALL/CutTest.lean`) | before 10:32 (began 10:21) | about 152 000 | 516 s |
| a4 | the search, proved complete, and its tests (`MALL/Decide.lean`, `MALL/DecideTest.lean`) | before 10:29 (began 10:21) | about 112 000 | 243 s |
| a5 | the reading back, cold, from an extract of 230 lines | 10:27 | about 88 000 | 152 s |

Where "before" is written, the time the agent reported was not taken
from the clock; the bound is the commit that has its result.

After the closing page, at the reviewer's word (the saturated sets and
the tutorial): 11:39 to 14:11 by the clock. Of that, by the session's
record: about 45 minutes (11:43 to 12:35) in five tool calls that each
waited ten minutes on a hook that did not answer; 80 minutes (12:38 to
13:58) with the session's process not running; the rest, about half an
hour, work. One more agent,
a6, wrote the tutorial: 376 105 tokens, 600 s of its own time after it
was restarted.

Interpolation, a command relayed at 15:04: began 15:06.

Interpolation ended 15:22 (pushed). Four agents: a7, Craig
interpolation in Lean (164 029 tokens, 478 s); a8, the four sources
(320 787 tokens, 683 s); a9, the reading back (88 477 tokens, 182 s);
the tutorial's section and its exercises were written by the operator.
Errors found by the build on the way: a `simp` and an `omega` that used
`Classical.choice` (found by the file's bound, located by `#axiom_path`).

## What went wrong, and what it cost

| what | found by | cost |
|---|---|---|
| a document written through a shell heredoc whose delimiter was not quoted: the shell ran the words between backticks as commands, and one of them (`top`) did not end | the command not returning | about three minutes; no file was harmed (checked) |
| a value pinned from expectation, three times (the screen's countermodel for `⊢ 1, 1`; the structure `refuteBy` returns for `chainBad 16`; the number of the screen's structures) | the build, each time | a build each |
| a first evaluator of the semantics over cyclic groups, by closures, that did not end in 120 s | a deadline | rewritten with lists of Booleans: 1.2 s |
| an agent's function named `step` in the namespace of the proof system's `step` | the first build that imported both | a rename |
| a plain `lake build` while an agent's test file was half written | the build | built by target after that |
| `native_decide` drafted in a test | the operator, before the build | replaced by `#guard` and `decide +kernel` |

Errors of transcription: none found.

## Words of the reviewer

None after the task that started the session. No stop.

| # | date | stage | class | the reviewer's words, in brief | what it changed |
|---|---|---|---|---|---|
