# DILL: the cost log

Times come from the clock (`date`). A figure the environment does not
give is written "not known".

## Sessions

One session runs the stages; the rows are the stages. The stages overlap
(the proofs were handed out while the explorer was written), so the
times are of the commits that begin and end each.

| # | stage | operator | started cold, or handed on, or went on | began | ended | waiting on builds | waiting at a stop | requests | output tokens | input read again | cost | Lean lines added / removed | document lines |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | Survey | Claude Fable 5.2 | started from a brief written by another session; cold as to the calculus | 2026-11-26 14:47 GMT | 14:59 (the plan committed) | a few seconds (two scratch files) | none (see "Time lost") | not known | not known | not known | not known | 0 | SURVEY-DOC |
| 2 | Adopt | the same | went on in the session | 15:13 | ADOPT-END | ADOPT-BUILD | none | not known | not known | not known | not known | ADOPT-LEAN | ADOPT-DOC |
| 3 | Prove | the same, with agents A to E | went on in the session | 15:20 (the brief) | PROVE-END | PROVE-BUILD | none | not known | not known | not known | not known | PROVE-LEAN | PROVE-DOC |
| 4 | Run | the same, with agents G and H | went on in the session | 15:29 (the brief) | RUN-END | | none | not known | not known | not known | not known | RUN-LEAN | RUN-DOC |
| 5 | Explore | the same, with an agent | went on in the session | EXPLORE-BEGIN | EXPLORE-END | | none | not known | not known | not known | not known | EXPLORE-LEAN | EXPLORE-DOC |

Where the tokens and the cost come from: not known to the operator, and
not filled. The agents' figures are as the environment reported them.

## Agents

"Began" is the clock at the launch (read by `date` in the call before or
after it); "ended" is that time plus the duration the environment
reported, so it is computed, not read.

| # | stage | task, in a few words | brief | began | ended | duration, as reported | tokens, as reported | result: what was kept, what was redone |
|---|---|---|---|---|---|---|---|---|
| 1 | Survey | the literature: a phase semantics, the finite model property, undecidability, formalisations, places for the further results | in the session; its report is `survey-report.md` | 14:49 | 15:09 | 19.5 min | 327 794 | kept whole; the operator read the semantics again from the page |
| 2 | Adopt | the second transcription, from four page images | in the session (the text is in the rule table's account) | 15:15 | 15:19 | 3.3 min | 106 261 | kept: no difference from the family |
| 3 | Prove | E: the translation to and from one-zone ILL | `brief-2-1.md`, E | 15:20 | 15:24 | 3.3 min | 119 603 | kept whole |
| 4 | Prove | D: the decision without `!` | `brief-2-1.md`, D | 15:20 | 15:25 | 4.7 min | 134 707 | kept whole |
| 5 | Prove | C: the structural results, identity expansion, subformulas | `brief-2-1.md`, C | 15:20 | 15:27 | 6.0 min | 147 994 | kept whole; it found that `Fam.exch` and `Fam.mono` were compiled by well-founded recursion |
| 6 | Prove | the reading back, from an extract of 491 lines | in the session | 15:21 | 15:28 | 6.3 min | 120 026 | kept: its eight instances are the refutations |
| 7 | Prove | B: soundness and completeness | `brief-2-1.md`, B | 15:20 | 15:28 | 7.7 min | 165 340 | kept whole |
AGENT-ROWS

## Time lost

From 15:00:36 to about 15:12 GMT, about twelve minutes. The operator's
first write of `DILL/Form.lean` came back as declined by the user, with
the instruction to stop and wait; the operator stopped and asked. The
session that started this one read the application's log and this
session's record afterwards and reports (15:33, a message between
sessions): the reviewer had interrupted that session at 15:00:33 and
15:00:35 about something else; at 15:00:36 the application stopped the
family of sessions and interrupted this one; the write had been waiting
39.9 s for its permission and was recorded as "user rejected" at the
same millisecond as the interrupt. The reviewer declined nothing and
resumed this session at about 15:12. The survey agent went on working
through it.

From 15:51 to 16:03 GMT, twelve minutes, and the three agents' work in
flight. The machine restarted at 15:51 (the session that started this
one reports it, with the cause: several Lean builds at once, three of
them this campaign's agents G, H and the tutorial's, beside an
evaluation of another repository's that had no cap on its memory). This
session's last command before it was the push of 15:42; its first after
it was at 16:03. The agents had their files on disk: G's and H's Lean
built as it stood; H's measurements were written but for one
placeholder; G's measurements and the tutorial's last files were not.
The scratchpad was cleared: the fetched papers, the page images, the
cold readers' two reports and the scratch screens are gone (what they
showed is in the plan, the rule table and the statements). From 16:03
one agent builds at a time (the reviewer's word of that hour, relayed).

## Words of the reviewer

| # | date | stage | class | the reviewer's words, in brief | what it changed |
|---|---|---|---|---|---|
| 1 | 2026-11-26 | before the Survey | command | "Yes, start DILL" (relayed in the brief of the session that started this one) | the campaign |
| 2 | 2026-11-26 15:13 | Adopt | correction | "I declined no such thing." | the operator went on; nothing built was affected |

## Errors of transcription

The list is in `rule-table.md`: none. By what could have found one:
`#rules` or `#slime` 0; a worked derivation 0; the second transcription
0; soundness or completeness 0; a person 0; later use 0.
