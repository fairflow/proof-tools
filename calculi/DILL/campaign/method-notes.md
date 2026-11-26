# DILL: notes on the method

Each place where the skill `calculus-campaign` (as amended in `94df876`,
and not run before as it now stands) was wrong, silent or unclear, and
what was done there. Kept to what would change that text.

## The first act

1. **A source that is a fragment of the paper's system, with no name of
   its own in the paper.** The first act's default for "the system" is
   "the one the command's words name, under the paper's own name for
   it", and "where they fit several, the base system: without the
   extensions". Here the paper's system (JILL) is the extension, and the
   command's system is the part of its figure without three rules and
   with the right-hand side specialised. The paper proves its theorems
   for the whole. *Done*: the fragment was taken; the first entry says
   which lines of the figure are left out, and the plan says why each of
   the paper's theorems holds of the fragment (a cut-free derivation of
   a sequent of the fragment has only rules of the fragment). *Proposed*:
   a line in the first act: where the system named is a fragment of the
   paper's, say for each theorem aimed at why it holds of the fragment,
   or that it is "holds of the logic, proved elsewhere".
2. **A source marked "do not cite".** Lecture notes that state the same
   calculus and more of its results carry "Please do not cite or
   distribute this document" on the title page. The skill's default
   ("the most complete version you can get") would take them. *Done*:
   not the source of record; read for prose and for results the report
   lacks, and each such result's entry says so. *Proposed*: a line under
   "Decide the target": a document whose author asks that it not be
   cited is read, not made the source of record.

## Stage 0

3. **Pitfall 11 again: a time typed before the clock was read.** The
   plan and four entries of the decisions were written with times
   three and six minutes ahead of `date` (15:02 and 15:05 for 14:59),
   typed while the text was composed and the clock read afterwards. Put
   right in the next commit. The pitfall's order of work ("evaluate,
   read, paste") was known and not kept: a document is written in one
   call and its time must exist before the call. *Proposed*: in
   `templates/decisions.md` and `templates/plan.md`, say "run `date`
   first, in a call of its own, and paste".
4. **A notation screened in a file with no tactic.** The plan's screen
   of `Γ ; Δ ⟹ C` passed: the scratch file had definitions and terms
   only. The first file with a tactic block failed, since the term
   before a `;` between two tactics was then read as the start of a
   sequent. *Done*: `⨾`. *Proposed*: in stage 0, step 3, "a notation is
   screened in a file that has a tactic block and a `do` block"; and in
   `reference/adopt.md` §3, beside `⊕ × ∘ →`: `;` cannot be a sign of
   the judgment, and `!` is Boolean negation and takes all that follows
   it (`!A ⊗ B` is refused; `(!A) ⊗ B`).

## Stage 1

5. **A refusal that came with an interrupt.** The environment returned
   the operator's write as declined by the user and told it to stop and
   wait. The skill's list of stops does not have this one, and the
   operator took the environment's word: twelve minutes. The reviewer
   had declined nothing; the application had interrupted the family of
   sessions for another reason at the same millisecond (the cost log has
   the record). *Proposed* (from the session that read the log): under
   "The stops", a line: a call that is refused at the moment of an
   interrupt is a stop from outside; report "stopped", say what was in
   hand, and do not report that the reviewer declined the act.
6. **A function on the family is compiled by well-founded recursion,
   silently, when the family's index in its argument is not a
   variable.** `Fam.exch : Ξ ~ Ξ' → Fam c (Γ ⨾ Ξ ⟹ C) → Fam c (Γ ⨾ Ξ' ⟹ C)`
   by pattern matching compiled, ran under `#eval`, and did not reduce
   in the kernel: `#print` shows `._unary` and `@[irreducible]`. Two
   agents found it independently, from a `decide` that failed. The same
   function over `{j : Seq} → Fam c j → …`, with `j.lin` and the like in
   its type, is structural. This is new with a judgment that is a
   structure: MALL's index was a list, a variable in every conclusion.
   *Done*: the functions restated through auxiliaries over `j`, names
   and types kept. *Proposed*: in `reference/adopt.md` §6, beside "a
   function on derivations is written by pattern matching": "state it
   over a variable judgment; check with `#print` that it has a
   `brecOn` and no `._unary`; a test by `decide` on a small derivation
   is the sign".
7. **A move of a right rule that names nothing.** `reference/explore.md`
   §2 says "nothing a move could compute from the judgment need be in
   it". A move `tensorR Δ` that reads `A ⊗ B` off the conclusion makes
   S1 a match on the shape of the conclusion with a case of refusal for
   each other shape, or a cast. *Done*: the moves of the right rules
   name their formula (`tensorR A B Δ`), and `step` compares. *Proposed*:
   a line there: for a two-sided calculus, let a right rule's move name
   the formula; the pattern with holes fills it for the user.

## Stage 2

8. **Five agents at once, from one brief.** The goals of Prove rest on
   one another only through the cuts, so they were handed out together,
   each agent with its own files and namespace, the operator's design,
   and "another design is welcome". All five came back with every goal
   proved, in 3.3 to 12.0 minutes of their own time, with no file
   touched twice and no name clash; each improved the design it was
   given in one place (a statement with three zones in place of
   weakening; generators in place of closed sets; a search that returns
   the derivation, so that soundness is its type). What made it work,
   beyond rule 5: the statements as named types in one file committed
   first; a list of names taken; "build by target". *Proposed*: say in
   stage 2 that goals that do not rest on one another go out together,
   and that the joining file (here `Goals.lean`: the statements about
   the calculus with cut, from a result without cut and cut elimination
   as a proposition) is the operator's.
9. **Cut elimination as a proposition arrived before cut elimination as
   a function** (soundness and completeness took 7.7 minutes, the
   syntactic proof 12.0), and the goals that only need the proposition
   (consistency, the disjunction property, decidability, the eight
   refutations) were joined from it at once. The skill's kinds table
   warns that the semantic cut "ignores the two given derivations"; it
   might also say that it is the cheap way to unblock everything that
   needs only the proposition.
10. **A type of functions says no more than its `Nonempty`, classically.**
    The cold reader's remark on every goal stated as a type, and on
    `Decidable`: "inhabited with no proof search at all". The skill asks
    for goals that are data to be stated as types (`reference/adopt.md`
    §5). *Proposed*: say there what such a statement asserts beyond its
    proposition: that the definition is within a bound that excludes
    `Classical.choice`, and that it computes; and ask for a test that
    the kernel runs it (`decide` on a small instance), which is also
    what catches note 6.
11. **A commit cited before a rebase.** `statements.md` cited the commit
    of the named statements by its hash; the push rebased onto another
    session's commits and the hash changed. *Proposed*: in "The campaign
    folder": cite a commit by hash only after it is on the shared
    branch.

## Stage 3

12. **Measurements with no budget.** Stage 3, step 3, says "give every
    run a deadline of its own"; nothing says how far a growing family
    is to be taken. The agent took a chain to 96 formulas, one capped
    case at a time, with the rest of the campaign queued behind it; the
    reviewer asked what was being waited for, and why. *Done*: stopped,
    and written up with the largest size settled as a lower bound.
    *Proposed*: in stage 3, step 3, and `reference/certify.md` §5: set a
    budget for the measurements before they start (so many sizes of
    each family, or so many minutes in all); the closing page needs the
    order of the frontier, and a lower bound serves; nothing waits on a
    measurement.
13. **A saturated set's soundness needs no model.** `reference/certify.md`
    §3 gives the record of a failed search its soundness through the
    syntactical model of the completeness proof. Here it is an
    induction on a derivation without cut (a member's last rule has a
    premise in the set), with cut elimination to reach the calculus
    with cut: 250 lines, no semantics. With it came, proved, what the
    certificate cannot reach (no member with a formula in the
    unrestricted zone or `!A` in the linear one). *Proposed*: say in §3
    that the syntactic proof is the first to try, and that the model is
    wanted only where the countermodel itself is.
14. **Builds side by side.** The skill gained, during this run, first
    "one agent builds at a time" (after the machine restarted under
    three of this campaign's agents and another session's uncapped
    evaluation) and then its correction, in the reviewer's words:
    "predictably the rules are now too restrictive, assuming a single
    build at a time. That's NOT needed." Under the first form the
    operator serialised everything for nineteen minutes. What the run
    shows of the rule as it now stands: the look before a build is
    cheap and was always clear after the restart (about 90% of memory
    free with two builds running); the danger was an evaluation of
    unknown size, and the cap (`lean -M 8000`) is the part that binds.

## Every record

15. **A time typed ahead of the clock, five times in one campaign**
    (note 3, and four more: "delivered 16:35" at 16:34 on the closing page itself, an entry "16:06" at 16:05, "built 16:24"
    at 16:23, a set of agents' end times computed from durations and
    first written as if read). Each was put right in the next call.
    The cause is the same each time: a document is composed in one
    call, and the time inside it must exist before the call. *Proposed*:
    pitfall 11 might say it mechanically: no document is written in the
    same call as the `date` it quotes.
16. **Fetched sources in a scratch folder do not survive a restart.**
    The first act says to put what is fetched in "a folder of its own";
    the session's scratchpad was used, as MALL's campaign did, and the
    machine's restart cleared it: the papers, the page images, the two
    cold readers' reports. Nothing proved was lost, and the records
    hold what the reports found, but a later check against the page
    means fetching again. *Proposed*: the folder is a durable one
    outside the repository (the round's shared notes folder served for
    hand-over notes and would serve for this), and the cold readers'
    reports are copied into the campaign folder when they come in.
17. **A sum typed, not computed.** The closing page first said that
    3 578 lines of the Lean are tests; `wc` says 3 439. It was caught
    because the same command that filled the page printed the count.
    The pitfall's order of work holds for sums too: compute, read,
    paste.

## Stage 4, and the whole

18. **The tutorial page before Run was finished.** The agent for the
    page was started while Run's files were being written, told to do
    its section on what runs last; the restart cut it off with seven
    sections done, and it was resumed for the eighth. Nothing was lost,
    and the page was not the last thing on the path. *Proposed*: say in
    stage 4, step 3, that the page may be begun when Prove is settled,
    its section on Run last.
19. **What this run shows of the skill as amended from MALL's notes.**
    The third form of judgment (`reference/adopt.md` §3, "where the
    logic has no weakening") carried over to two zones as written, one
    form for each zone. The line "where derivability is not decidable,
    level 3 is not a goal" (`reference/certify.md` §3) was right and
    saved designing for it; what it does not say is that level 3 can
    still be stated, and proved, of the decidable fragment
    (`decidedBangFree`). "Build by target while agents write" (rule 5)
    was needed from the first minute. The tutorial page as part of
    stage 4 took one agent about half an hour of its own time. The
    order "soundness, then completeness, before every other goal"
    (stage 2, step 4) was not kept: all goals went out at once, and
    nothing was lost by it, since no proof rested on a rule that the
    two theorems could have faulted before the others were done; had
    they faulted one, five agents' work would have been built again.
    *Proposed*: let step 4 say that the order is a matter of what is
    risked, and that with agents the two theorems may run beside the
    rest at that risk.
20. **The tutorial's links, and a rebase.** `reference/explore.md` §11
    says: "commit the Lean first, then run `write`, then commit the
    page". `write` links at `HEAD`; the push then rebased onto another
    session's commits, and the commit the 112 links named was no longer
    on the branch. *Done*: `write` run again after the push, at a commit
    that is on `main`. *Proposed*: "commit the Lean and push it, then
    run `write`, then commit the page": where several sessions push to
    one branch, a link may name only a commit that is already there.
21. **A sequent typed at a shell** (2026-11-26 21:18 GMT, after the
    campaign closed; by the session that started it, on the reviewer's
    remark that a prover at the command line would be useful). The four
    runners (`ksearch`, `glsrun`, `mallrun`, `dillrun`) answered only
    for their own corpus and families: none read a judgment from text.
    *Done*: `dillrun prove '<sequent>'` (`DILL/Parse.lean`, `Main.lean`;
    the user's guide, "From the command line"). It prints `derivable`
    with the tree, `not derivable` with a saturated set, or `flag`, as a
    Lean file that the kernel checks, and exits 0, 1 or 3 (2 for a text
    not read). The reader is tested by reading back all 56 entries of
    the corpus from both printers (`DILL/ParseTest.lean`); the command,
    run on the 56, gives 39 derivable, 13 not derivable with a set and 4
    flags, none against the status; three printed files were elaborated,
    and one with a move altered was refused. *Done in the skill*:
    `reference/certify.md` §5 names the command as the third way to
    splice. Not done: the same command for K, GLS and MALL.
22. **`dillrun prove` brought to the skill's paragraph** (2026-11-26,
    22:16 GMT on; by the owner session, on the directing session's
    task). The paragraph is "A judgment typed at a shell",
    `reference/certify.md` §5, as of commit `0e83910`. *Done*: the
    printed file has named declarations in `DILL.Answer` and ends with
    the bound on axioms; both options for a large answer, with the
    threshold measured; a text not read is reported with the text and a
    mark; Lean reads the Lean source of all 56 entries (and six more) as
    the sequent it was written from (`DILL/ParseTest.lean`, `leanReads`);
    `dillrun corpus` and `Corpus/prove_corpus.py`; the figures in
    `measurements.md`, "The command on the corpus". What the paragraph
    does not say, for this calculus:
    1. *A flag agrees with either status.* "A script that compares each
       exit code with the recorded status" supposes a search that always
       answers (K's). Here 4 of the 56 answers are flags. The script
       fails only on an answer against the status, and names the flags;
       a search that came to flag more would pass it. *Proposed*: say
       that where the command can flag, the script names the flagged
       entries and the measurements record the list; or let the corpus
       record the verdict expected of the command, not only the status.
    2. *Two searches, and only one had a bound.* "The budget where the
       search has one, a deadline where it has none" reads as a choice.
       DILL has both kinds in one command: the search for a derivation
       has the budget and a cap on calls, the search for a saturated set
       has neither, and on 24 equal atoms against 25 the command as note
       21 left it did not end in 100 s. Found only because the sizing of
       "a large answer" tried a family outside the corpus. *Done*:
       `--deadline=<seconds>` (10) over the whole answer. *Proposed*:
       "a deadline in every case; the budget as well where a search has
       one", and "try a family that grows before saying the command ends
       by itself".
    3. *"A large answer" has no measure.* K's thresholds are K's. Here
       the limit met first is the depth of recursion, between a tree
       nested 101 deep and one nested 131 deep; no limit on heartbeats
       was met. *Proposed*: "find where a printed file without the
       options is refused, set the threshold well below, and record
       both".
    4. *Several facts, one kernel check.* "State each from the one
       certificate" was first done with one `verdict` for each fact, and
       the kernel then checked the set once for each: 41 s for a set of
       200 sequents. *Done*: the check is a theorem of its own, passed
       to each certifier's `verdict`: 20 s. It has to be stated through
       the certifier (`noCFBySet.check sequent saturated = true := by
       decide +kernel`). Stated of the checker's function
       (`refutedBy saturated sequent = true`), which is the same Boolean
       by definition, the kernel passed 8 GB on the same set and the
       file was refused. The cause was not looked for. *Proposed*: say
       "one kernel check, stated as `K.check s c = true`", and that a
       second statement of the same check is to be measured, not
       assumed equal.
    5. *Which texts the reader reads back.* "The reader reads back what
       each printer writes": K's script gives the command the Lean
       source as a third text; DILL's reader did not read Lean source
       (zones in brackets, `Form.atom 12`). *Done*: it does, and the
       script gives all three. *Proposed*: name the three texts.
    6. *Two printers of Lean source.* `seqSrc` and `Refute.srcSeq` differ
       in the parentheses around the conclusion. The facts are stated of
       `sequent`, printed by the first; the second prints the members of
       a set, which is a certificate: a member misprinted can make the
       check fail and cannot make a fact false. Both are tested all the
       same. *Proposed*: one line saying that the test of meaning is of
       the printer that writes the statement.
    7. *A certificate past the kernel's reach.* For a set of 499
       sequents the command answers `not derivable` in milliseconds and
       prints a file whose kernel check did not end in 120 s
       (`measurements-sat.md`). The paragraph is silent. *Done*: from 201
       sequents the head of the file says so. Whether that answer should
       be a flag is not decided here.
    8. *Who alters the certificate.* "One with its certificate altered
       refused" names no place for it. *Done*: the script does it, for
       one tree and one set, and fails if Lean accepts either.
    Also corrected on the way: `Refute.outcome` printed "1 sequents"
    (a loose end of the closing page); a `--budget` that is not a
    number, and an option that does not exist, are refused with exit
    code 2 where the first panicked and the second was dropped.
