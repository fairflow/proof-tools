# The method notes of five campaigns, collated

Written 2026-11-27 00:00 GMT by the directing session of the calculus campaigns.

**What this is.** Each campaign kept `method-notes.md`: the places where the skill `calculus-campaign` was wrong, silent or unclear. This page puts them together, says what the campaigns show when read side by side, decides each proposal that had not been applied, and lists what should move into the libraries. It is the second of two pages. The first, `docs/campaigns/skill-against-design-2026-11-26.md`, is the factual sweep: every note of the first four campaigns in one table, by theme and state, with the evidence. This page does not repeat that table.

**The campaigns.** Brünnler's nested sequents for K (2026-11-23, 80 notes); GLS for provability logic (2026-11-25, 27 notes); MALL (29 notes); DILL (22 notes); and a fifth, in a private repository, on a set-based sequent calculus whose source is a Lean family and whose certificate against a derivation has cycles (22 notes, written so that they can be quoted here). Counts are as of this page; the sweep counted 150 at commit `0e83910`, and 30 more were written on the evening of 26 November.

**What is decided here and what is not.** Changes to the skill's text are the directing session's to make, and each is decided below. Three things are the reviewer's: additions to the standing list of results, which calculi come next, and whether the work on the libraries is started. They are set out in the last section as proposals.

## What the campaigns show, read together

**The checks of a transcription have never been seen to fail.** Four campaigns from a paper, and no error of transcription was found by any check at any stage: not by `#rules` beside the figure, not by the worked derivations, not by the second transcription, not by soundness or completeness. Either the transcriptions were right or the checks are blind, and the record cannot tell which. The checks did find faults of the sources (three misprints in one, a wrong connective in a figure of another) and tempting simplifications that never reached the family. A test with planted faults would settle it: copies of one adopted family, each with one fault, and a table of which check catches which.

**Waiting for approval cost time and found nothing; one choice at the start mattered.** The first campaign ran under seven gates. One changed the work (the form of "valid", at the plan); none found an error; about two hours of work lay in a span of eleven and a half. The four campaigns since ran on "decide, record, go on" and none ended with a goal open. What the one useful gate did can be kept without a gate: state, as information, the form chosen for what holds and the form rejected.

**The side that says "no" took a different form in each calculus, with one proof in common.** A finite tree as a countermodel (K, GLS); a cyclic phase structure, or a saturated set of sequents (MALL); a saturated set (DILL); generators of a closed set, up to weakening (the fifth). In every case where the certificate is a set of sequents, its soundness is an induction on a derivation (the last rule of a member has a premise in the set) and needs no model. The model is wanted only where the countermodel itself is. Two refinements came from the calculus with cycles: membership up to weakening, without which the set is exponential for a trivial reason (65 536 members against 1), and a search by rounds, because a memo of failures is unsound once a failure can be provisional.

**A compiled check slower than the kernel's is a fault of the checker.** *Corrected 2026-11-27 08:40 GMT, at the reviewer's challenge; the first wording said "which side is slow is not fixed", as if it were a property of the route.* In GLS the compiled check of a certificate did not finish where the kernel took under a second. Reproduced and measured: both compiled checks end, and both cost `2ⁿ`. The countermodel's evaluation recomputes (`2ⁿ` calls for `n²` different questions on a chain of `n` worlds: 18.6 s at 30), and the kernel, which keeps the terms it has reduced, does not (0.9 s at 64). The replay of a tree of moves builds the calculus's own sequents, which double at each nested modal step (2.2 GB at 24), and the kernel never builds them. Neither is a wrong answer and neither is a failure to end; both are definitions that a person would not have run, passed because the kernel was fast. The other direction is a different thing: in MALL a set of 238 sequents is printed in 0.06 s and Lean does not check it within 8 GB, for a cause not yet looked for. So each campaign measures both sides on a family that grows, and a difference in either direction is investigated before it is recorded as a limit.

**A verdict must not read the same for a checked and an unchecked answer.** Every runner can print a certificate larger than Lean has been seen to check. Since 26 November the first line says so above a measured size. The size is not sharp, depends on the form of the printed file, and may need two measures (length and depth).

**Mistakes of the record repeat, and only a mechanical rule stops them.** A time written ahead of the clock occurred five times in DILL, twice in the fifth campaign and once in the directing session, each by the same cause: a document composed in the same call as the `date` it quotes. The same holds of a sum typed and not computed, a certificate typed from expectation, and a commit cited before the push that rebased it.

**Goals that do not rest on one another can go out together.** DILL handed five agents its goals at once from one brief; all came back proved in 3 to 12 minutes with no file touched twice. What made it work: the statements as named types in one file committed first, a list of names taken, and builds by target. The cheap proof of a proposition (cut elimination by soundness and completeness) unblocked everything that needs only the proposition while the costly one (the function on derivations) was still running.

**The loop from a campaign's notes to the skill converges fast when the task is small.** The command `prove` was specified in one bullet; K's owner built from it and listed twelve gaps; the paragraph was rewritten; MALL listed eight, GLS seven, DILL four, the fifth six; four revisions in one evening, each owner building from the text as the last had left it. The later lists are about the calculus at hand more than about the text.

**The same code is written in every calculus.** A reader of judgments, a runner with the same commands, a corpus script, a test that Lean reads back what a printer writes, permutation lemmas free of `Classical.choice`: five, five, five, five and three copies. The rule "do not change the libraries; a need is a finding" was kept by every campaign, and no finding was ever acted on. The rule needs its other half: someone reads the findings.

**The organisation changed twice and the skill has caught up with neither.** A fresh session for each stage (the draft's rule) was never tried. Since 26 November there is one directing session and one owner session for each calculus: the owner builds and writes notes, the director checks, applies notes to the skill and sends the next task. The skill says "sessions are yours to arrange" and nothing of this.

## The proposals not yet applied, decided

"Yes" means the text is changed as the note proposes, at the place it names. The changes are made in the commit that follows this page.

| note | proposal, in brief | decision |
|---|---|---|
| DILL 1 | where the system is a fragment of the paper's, say for each theorem why it holds of the fragment | yes |
| DILL 2 | a document whose author asks that it not be cited is read, not made the source of record | yes |
| DILL 3, 15; fifth 15 | no document is written in the same call as the `date` it quotes | yes: pitfall 11 and the two templates |
| DILL 17 | a sum is computed, read and pasted, like a time | yes: one clause in pitfall 11 |
| DILL 4 | screen a notation in a file with a tactic block and a `do` block; `;` and `!` cannot be signs of a judgment as they stand | yes |
| DILL 5 | a call refused at the moment of an interrupt is a stop from outside, not the reviewer declining | yes |
| DILL 6 | state a function on the family over a variable judgment; check for `brecOn`, and test by `decide` | yes |
| DILL 7 | in a two-sided calculus a right rule's move names its formula | yes |
| DILL 8 | goals that do not rest on one another go out together; the joining file is the operator's | yes |
| DILL 9 | the semantic proof of cut elimination is the cheap way to unblock what needs only the proposition | yes |
| DILL 10 | say what a goal stated as a type asserts beyond its proposition, and test that the kernel runs it | yes |
| DILL 11, 20 | cite or link a commit only once it is on the shared branch; write the tutorial's links after the push | yes |
| DILL 12 | set a budget for the measurements before they start; a lower bound serves | yes |
| DILL 13; fifth 4, 5 | for a set of sequents, soundness by induction on a derivation is the first proof to try; membership up to weakening where rules keep their principal formula; the worlds of its model are the maximal members | yes: one passage in `reference/certify.md` §3 |
| DILL 14 | builds side by side | no change: the rule already reads so |
| DILL 16 | fetched sources go in a durable folder | yes, reworded: a folder outside the repository and outside any scratch folder, named in the first entry of `decisions.md`; the cold readers' reports are copied into the campaign folder as they come |
| DILL 18 | the tutorial page may be begun when Prove is settled, its section on Run last | yes |
| DILL 19 | the order "soundness and completeness before the other goals" is a matter of what is risked | yes |
| MALL 26 | a goal with a decision procedure at hand is screened against it before the proof and before the literature | yes |
| MALL 27 | `simp at h` on lengths and `omega` at an undecidable goal bring in `Classical.choice` | yes: the list in `reference/adopt.md` §6 |
| fifth 1 | where the source is a family: the checks of meaning are the two-way theorems between the family, `step` and any relation the certificate is defined by; the family against its paper is named as unchecked | yes: "Two shorter paths" |
| fifth 2, 3 | a third layout, inside a host project; where the host already has lean-certify the library cannot be required and is copied at a pinned commit | yes for the text; the cause goes to the libraries (below) |
| fifth 6 | a memo of failures is sound only where premises are smaller; on a graph with cycles, search by rounds | yes: `reference/certify.md` §4 |
| fifth 7 | a repair of a search changes certificates: write the fact files again and record sizes before and after | yes |
| fifth 8 | a certificate in a test comes from the producer | yes: pitfall 11 |
| fifth 9 | `Repr` is for the editor and may be derived in the code file | yes: the template |
| fifth 10 | in a host with a large library, expect any short word to be taken | yes |
| fifth 11 | four limits of the pins script | to the libraries (below); one sentence in `reference/explore.md` §11 meanwhile |
| fifth 12 | where the family is into `Prop` with a height, and moves normalise contexts, S2 is proved with weakening in the induction | yes: `reference/explore.md` §4 |
| fifth 13 | a cross-check with another tool: a deadline, read its output only if it ended, a timeout is no verdict, and no tool is the reference | yes: `reference/certify.md` §5 |
| fifth 14, 18 | where atoms are words: a list of words that are not letters, the written-out form in the printed file, and the misreading to test is a constant's name read as a letter | yes: the paragraph on `prove` |
| fifth 16 | a statement whose form the template fixes (S1, S2) needs no separate entry before its proof | yes: rule 2 says so |
| fifth 17 | a session whose brief settled the first act records "decided by the brief" and sends no message | yes |
| fifth 19 | lines of the paragraph with no object for one search and one kind of certificate | no change |
| fifth 20 | a fact's import is paid by every answer | yes |
| fifth 21 | sizes beyond the kernel are measured on the file as finally printed, and again when its form changes; say on how many families | yes |
| fifth 22 | for a certificate with cycles: the alteration that cannot pass; the family whose generators grow; the order of hypotheses; "it has answered everything tried"; a member that asks for itself; the model as a theorem and not a printed fact | yes, in six short lines |

Also from this page's own findings: the skill gains a short section on a round of campaigns (one directing session, one owner for each calculus, who changes which files, how a note becomes a line of the skill), and the first act gains the statement of the form of what holds, chosen and rejected, as information.

## What the campaigns asked of the libraries

None of these has been done. Each has a decision; the work itself is proposed in the last section.

| need | written how often | decision |
|---|---|---|
| permutation lemmas free of `Classical.choice` (`perm_count`, those on `erase`), and the enumerations of picks and divisions of a list | three times; twice | into `ProofTools`; the three calculi then import them |
| a reader of judgments: a lexer with positions, connectives by binding strength, a refusal with the text and a mark | five times | into `ProofTools`, as functions a calculus instantiates with its signs |
| the test that Lean reads back a judgment printed as Lean source (`leanReads`) | five times | into `ProofTools` |
| the corpus script: run the command on every entry and on members of the families, in a process group ended at the deadline, compare exit codes, elaborate each file under a memory cap | five times | one script in `scripts/`, with the runner's name as its argument |
| the runner (`status`, `facts`, `corpus`, `families`, `prove`, the exit codes, the deadline) | five times | a template in the skill, not a library function: the certifiers differ; `Certify.Cli` is not usable without a registry and the template says so |
| `ProofTools` and `LeanCertify` in one package | met once | separate packages, or `ProofTools` requiring `lean-certify`: without it a project that already has lean-certify must copy the library |
| `scripts/tutorial_pins.py`: a status REFUTED and the negated statement; a definition not given PROVED; a structure's fields; pages for a repository whose links do not open | three campaigns | into the script |
| `Cert` without `DecidableEq`; the word `size` made a keyword for every importing file; the offered line placed after comment lines or taking a trailing comment | once each | `DecidableEq` and `size`: yes. The placing of the offered line: when it is met again |
| a tactic of the calculus applied to the goal in front; a goal drawn as a tree in the infoview; a mark in the explorer where the rules that lose nothing end | once each | not now |

## For the reviewer

**Additions to the standing list.** The list has seven results. A survey of the literature made for this round found no general theory that covers these calculi together; it found that the judgmental method of Pfenning and Davies gives, for any sequent calculus, a fixed set of statements beside cut elimination. Proposed for the list: identity expansion (every formula from atomic initial sequents), the partner of cut; one cut principle for each kind of hypothesis; the admissible structural rules of each zone; the classification of the rules by invertibility. DILL proved all four unprompted; the others proved some.

**The planted-fault test.** One adopted calculus, copies of its family with one fault each (a side condition dropped, a premise weakened, a connective swapped, a rule missing from `step` only), every check of the skill run on each copy. It answers the first finding above, and it is the one experiment that could show the method's central checks to be worth less than they cost.

**The work on the libraries.** The table above, as one piece of work by one session that owns `ProofTools/`, `LeanCertify/` and `scripts/`, after which each owner replaces its copy.

**Which calculi next.** The survey's advice, with the reasons it gave: adjoint logic with the order of modes as a parameter (cut and identity proved once for the two-zone linear calculus, S4 necessity and a monadic modality; it would test a parametrised calculus, and it subsumes the logic of mixed linear and non-linear contexts that was a candidate for the next phase of the linear round); and a labelled calculus for K with its translation to nested sequents (the one result found that relates two kinds of calculus, against a campaign already done).

## Not done

- The operator's own tokens are in no cost log; the application can report usage by session and that has not been tried.
- No person has typed the exercises of any tutorial.
- The validity form of what holds, the named hypothesis for a case that will not close, and a campaign that ends with a goal open: none has occurred.
- The readers of the four public calculi do not take the same letters.
- This page was not read by a second reader.
