# Brünnler's system K: the cost log

Times come from the clock (`date`, and the session's transcript for its
start). A figure the environment does not give is written "not known".

## Sessions

| # | stage | operator (person, or model and settings) | fresh session from a brief? | began | ended | waiting on builds | requests | output tokens | input read again (cached) | cost | Lean lines added / removed | document lines |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | Survey | Claude Fable 5.2 (`claude-fable-5-2`); effort setting not known | no: the command's session, and not cold (see `gates.md`) | 2026-11-23 07:23 GMT | first at its gate note, 2026-11-23 07:57 GMT; taken up again on the reviewer's answer (the clock read 09:06 at the first command) and at the gate again at 2026-11-23 09:12 GMT | none: no build; scratch runs of `lean` on seven files, a few seconds each; one run of `pdflatex` on the source | not known | not known | not known | not known | 0 / 0 | 815 added before the answer; after it, see the commits of 2026-11-23 |
| 2 | Adopt, to the rule table's gate | Claude Fable 5.2 (`claude-fable-5-2`); effort setting not known | no: the session of row 1, at the reviewer's word (`gates.md`, the fourth entry); worked from `brief-1-1.md` | 2026-11-23 14:07 GMT | at the gate note, 2026-11-23 14:19 GMT by the clock | under a minute in all: the first build of the library's audit modules 6 s; each later build 1 to 3 s | not known | not known | not known | not known | 631 / 0 (of which tests 196) | 597 in `rule-table.md` and `statements.md`; additions to four other files |
| 3 | Adopt, after the rule table's gate | Claude Fable 5.2 (`claude-fable-5-2`); effort setting not known | no: the session of rows 1 and 2, after a summary of its earlier part; worked from `brief-1-2.md` | 2026-11-23 15:45 GMT, at the reviewer's signature | at the report, 2026-11-23 15:55 GMT by the clock | under a minute in all: each module about 1 s; the tests file 1.5 s | not known | not known | not known | not known | 976 / 0 (`Proof.lean` 203, `Tactic.lean` 133, tests 439, the exercises file 201) | the report (184); additions to the rule table, the statements, the notes, this log |
| 4 | Prove, to the reviewer's goal (completeness, cut elimination) | Claude Fable 5.2 (`claude-fable-5-2`); effort setting not known | no: the session of rows 1 to 3, after two summaries of its earlier parts; no brief (the reviewer's goal was the instruction) | 2026-11-23 17:30 GMT | at the report, 2026-11-23 18:00 GMT by the clock; of this, 17:36 to 17:53 GMT was at the statements' gate, with the contexts written meanwhile | under a minute in all: each module 1 to 3 s; the screens 2.4 s | not known | not known | not known | not known | 1 919 / 0 (theory 1 533: `Semantics` 169, `Context` 205, `Weight` 129, `Ctx` 268, `Soundness` 365, `Search` 345, `Completeness` 52; tests 343; `Play/Search.lean` 43) | the report; additions to the gates, the statements, the notes, this log; the skill's rule 6 |

Where the tokens and the cost come from: not known to the operator. The
reviewer's application shows them.

What this row does not separate: the session's first part, done without
the skill (reading the source, a first plan), and its second, under the
skill. The clock was read at 07:31 (the first scratch screen, in the
first part) and at 07:47 (the searches of the first act, in the second);
the reading of the source was all in the first part.

## Exchanges with the reviewer

| # | date | stage | class | the reviewer's words, in brief | what it changed |
|---|---|---|---|---|---|
| 1 | 2026-11-23 | 0 | decision | the command: "Brünnler's K" | began the session |
| 2 | 2026-11-23 | 0 | correction | "we should be working from an installation of calculus-campaign the entire purpose of this session was to test that campaign. Please install it" | the skill was merged in from `proof-tools-home`; the first plan lost its standing |
| 3 | 2026-11-23 | 0 | a question (none of the three classes) | on the excluded-middle screen: "somehow the object model theory forces EM in our META-theory? is this a shallow or a deep embedding then, it looks deep!" | two more screens (omniscience; the form with no countermodel); the plan's section on what "valid" means |
| 4 | 2026-11-23 | 0 | decision | "Continue here" (over a fresh session) | the first act was done in this session |
| 5 | 2026-11-23 | 0 | decision | the target gate: "Yes, as proposed" | the campaign folder; the Survey |
| 6 | 2026-11-23 | 0 | decisions (three), corrections (two), questions (two) | the plan's gate, answered in part; the words are in `gates.md`, the second entry | decisions: the source may be fetched; cyclic leaves left out; the letters. Corrections: the place (`examples/` to `calculi/`, in the skill too); commits go to `main`. Questions: exchange (the plan's table says why); a less absolute "valid" (found: two-valued models) |
| 7 | 2026-11-23 | 0 | decision | the plan's gate, put again: "Pass as proposed" | the plan is passed; all ten goals are goals; the brief for Adopt |
| 8 | 2026-11-23 | 1 | decision | "Continue here with Adopt I have pulled in, you continue in your worktree. I think a single session may be sensible" | Adopt was run in the session of stage 0, not a fresh one |
| 9 | 2026-11-23 | 1 | a question (none of the three classes) | at the rule table's gate: "So the paper puts no constructors in the rule conclusion?" | nothing in the Lean; the answer is in `gates.md`; an offer made (the rules in the figure's shape, as derived rules), carried to the report |
| 10 | 2026-11-23 | 1 | decision | the rule table's gate: "As put thanks" | the table is signed; steps 5 to 9 of Adopt were done |
| 11 | 2026-11-23 | 2 | decision | "I will test later since proving the next set of results may change what you already implemented so: /goal prove completeness and cut elimination" | the reviewer's test deferred; Prove begun in this session, for two goals |
| 12 | 2026-11-23 | 2 | a question (none of the three classes) | "We're still in the skill process right? Or off track?" | nothing in the Lean; the operator said where in the process it was |
| 13 | 2026-11-23 | 1, 2 | decision | "PS yes add contexts and lemmas of course" (decision 2 of Adopt's report) | `BrunnlerK/Ctx.lean`: contexts, `fill`, the six rules in the figure's shape |
| 14 | 2026-11-23 | 2 | decision, and a correction of the method | "Signed and if I set a goal that's a very deliberate thing to do so please modify the instructions of the skill to allow a later command of mine to override an earlier gate. As you call it. So yes "signed as put"." | the statements signed; the skill's rule 6; the proofs |

## By stage

| stage | sessions | elapsed | of which waiting on builds | requests | cost | reached its gate? | decisions / corrections / rescues |
|---|---|---|---|---|---|---|---|
| 0 Survey | 1 | 34 min by the clock to the first gate note; the second part from 09:06 to 09:12 GMT | none | not known | not known | yes: the plan passed at its second putting; ended 09:36 GMT with the brief for Adopt | 7 / 3 / 0, and three questions |
| 1 Adopt | 1 (the session of stage 0, continued) | 12 min by the clock to the rule table's gate note; 10 min from the signature to the report | under two minutes | not known | not known | the rule table: passed as put; the reviewer's test: put, not done | 2 / 0 / 0, and one question |
| 2 Prove (to the reviewer's goal; not ended) | 1 (the session of stages 0 and 1, continued) | from 17:30 GMT to the report, 2026-11-23 18:00 GMT; 17 min of it at the statements' gate | under a minute | not known | not known | the statements, first sending: signed as put; the report: put | 3 / 1 / 0, and one question |
| 3 Run | | | | | | | |
| 4 Explore | | | | | | | |

## Errors of transcription

None found. The two families were signed by the reviewer on 2026-11-23,
as put. After the signature: Example 2.3 built by the tactic maps out to
the term written with the constructors before the signature (equal by
`rfl`), and S2 found no instance of a rule that `step` refuses.

## What the operator did unaided, and what it did not

**Survey.** Unaided: found and read the source; found that the journal
and conference versions could not be got; read the bibliography and found
the source's slip about [13]; screened the soundness statement and found
that the source's reading needs excluded middle; found a type of
sequents for which every `deriving` line works. Not unaided: it did not
find the skill, which was on another branch, until told that one existed;
it then needed the reviewer's word to go on in the same session.

**Adopt, to the rule table.** Unaided: the functions on sequents and the
two families; found that the proviso of K° is about the whole sequent and
not the node; renamed the node so that the figure's letters keep their
meaning. One false start, caught by the file's bound on axioms: `Path`
was declared inside a namespace and the family's binders did not resolve
it. One function written that nothing asked for (a modal depth), taken
out again.

What the operator knew that the skill did not tell it: that soundness of
a classical calculus for truth defined in the host logic is as strong as
the host's excluded middle, and that the form "no countermodel" avoids
it. An older skill of the project (`calculus-adoption`,
`reference/choice-free.md`, "When choice is genuinely in the statement")
says to give the constructive form beside the classical one; this skill's
`templates/statements.md` says to enter both, and nothing sends the
Survey to look for the case.

**Adopt, after the rule table.** Unaided: the proof system and both
theorems that tie it to the family; the tactic, the syntax for
sequents, the tests and the exercises. One false start: the case of
`◇k_c` in S1 did not typecheck as a nested `match`, and was made a
function of its own. Four pinned messages were wrong at the first run of
the tests (a combining character; the order of two offered moves; a
count; a name printed in full) and were corrected from Lean's output.
Three statements in the first draft of the report were wrong and were
corrected before it was committed: a build time that had not been
measured, and two counts of what the exercises do.

**Prove, to the reviewer's goal.** Unaided: the definitions of the
semantics and the statements; the screens; the route (a search at the
root, `Fam.lift`, a weight), which is not the source's; all the proofs.
False starts, each caught by Lean at once: `Fam.lift` written with
`induction` did not compile to code; a characterisation given to `simp`
looped; a library lemma brought in `Classical.choice`; an anonymous
constructor of the wrong shape. Not unaided: the operator stopped twice
at the statements' gate after the reviewer had set a goal, and needed
the reviewer's word to go on; one time written in a document was
estimated and not read from the clock, and was corrected from the
commit's time before anything else was built.
