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
