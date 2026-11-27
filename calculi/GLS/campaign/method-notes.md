# GLS: notes on the method

Each place where the skill `calculus-campaign` was wrong, silent or
unclear, and what was done there. The text read is that of commit
`818483e` of proof-tools: the rewrite of 2026-11-25, of which this
campaign is the first run. Kept to what would change that text.

## The first act

1. **The default version and the download permission do not meet.** Step
   3 says to read "the most complete version you can get (a journal
   version or a thesis before a conference paper)". The command named
   the conference paper and allowed the download of "the paper". The
   default then picks a file (the thesis) that the reviewer's words do
   not cover, and the operator's environment asks the reviewer's word
   file by file. What was done: the question was asked for the thesis,
   as the step's own clause on downloads says. *Proposed*: the first act
   should say that a permission to download "the paper" is to be read as
   covering every version of it that the first act may choose, or the
   command's hint should invite "you may download its sources".
   (Settled while this campaign ran: commit `28e3aa8` of proof-tools,
   13:16, makes the download of public material the reviewer's
   standing word. Notes 2 and 3 are answered by the same change.)
2. **A paper that is named and cannot be got.** Step 2 says "a source
   you cannot get is not the target: take the best one you can get". The
   paper here was behind a paywall and its open copy unreachable; the
   best that could be got was a thesis by one author, and the authors'
   Coq formalisation. The text does not say whether a formal development
   published with the paper counts as a version of the source. What was
   done: the Coq files were read as evidence for the Survey (what the
   systems and the theorems are called, what is proved), and nothing was
   to be transcribed from them into the rule table without a source in
   prose beside it (rule 1).
3. **"Ask it in the message of step 4" supposes that the operator talks
   to the reviewer.** This session was started by another session; a
   question goes to that session, and the harness says to end the turn
   after it. The skill says to go on meanwhile. What was done: the
   question was sent at once, before the folder was written, so that the
   answer could come while the work went on; the turn was not ended.
4. **The first entry's times.** The template asks for a time "from the
   clock" at the entry's head and at "told to the reviewer"; the entry is
   written before the message is sent. What was done: the times were
   corrected after the message, from `date`.

## Stage 0, Survey

5. **The source the paper is about may be a formal development.** The
   Survey's Q1 ("the figure, the prose around it, the appendix") and the
   second transcription ("the figure, and the prose around it") suppose
   a paper. Here the paper's object is a Coq development, which was
   readable when the paper was not. A Coq file states its rules without
   ambiguity, and the cold reader given it found the same five and six
   rules, with the place of every side condition. *Proposed*: say in
   `reference/adopt.md` §1 that where a source has a published formal
   development, its definitions are read beside the figure, and which
   rules where they differ (here: the definitions, since the theorems
   are about them).
6. **A campaign may want a semantics the source does not have.** "Of
   the source's own theorems, soundness is a goal" supposes the source
   has one. This source is proof theory only. The fourth check of
   meaning and the no side of Run both want a semantics. What was done:
   the usual semantics of the logic was stated by the operator, entered
   among the costliest decisions, and listed on the closing page among
   the definitions to read. *Proposed*: say in "What a campaign proves"
   what to do when the source has no semantics: that the operator may
   state the logic's usual one, as a decision that costs the campaign,
   and that soundness and completeness for it are then goals of the
   kind "holds of the logic, proved elsewhere".
7. **Two routes to a goal by rule, of which one makes the other's lemmas
   unnecessary.** Stage 2, step 4, foresees it ("the proofs may take
   another"). Here the shorter route (soundness and completeness, then
   cut in ten lines) also *ignores the two given derivations*, which is
   what the paper is against. The type of the goal cannot tell the two
   apart. What was done: both, the second recorded as a second proof of
   the same statement. *Proposed*: a line in `reference/adopt.md` §2,
   "cut elimination": where the goal is a function on derivations, say
   in the statement's entry which function was defined, since the type
   does not.

## Stage 1, Adopt

8. **The template's tests put a description above a pinned message.** A
   doc comment before `/-- error: … -/ #guard_msgs in` is a parse error
   (two doc comments). The template does not do this, and does not warn
   of it; the operator did it four times. A `--` comment serves.
9. **`explore.md` §6, "No comment after a pattern", is wider than it
   says.** Comment lines *below* a pattern line are also swallowed: the
   line the tactic offers back is written after them. Seen in the
   tutorial (`glsmove impR` followed by three comment lines).

## Stage 2, Prove

10. **The order "displayed in `statements.md`, screened, read back, then
    proved" was not kept to the letter.** The statements were in Lean
    as named propositions, the screens had run and the reading back had
    been started before the first proof; the reading back (a cold
    reader takes minutes) came in while goals 1 and 2 were being
    proved, and the entries of `statements.md` were written after. It
    found no difference. *Proposed*: let the text say that the proofs
    may begin while the reading back runs, and that what rests on a
    statement it faults is built again; and that the Lean file of named
    statements is where they are "displayed" first.
11. **Screens as a module of the build.** `reference/adopt.md` §5 says
    "run banks of cases compiled". A file of `#guard`s that imports the
    untrusted search and the tree model, built with the package
    (`GLS/Screen.lean`, 9 s), kept the screens repeatable and failed
    the build when one failed. A control (`#guard !(…)` on a claim that
    must fail) is the cheap answer to pitfall 6.
12. **Pitfall 11 happened three times** (a pinned message and two
    expected values written from expectation). Each was caught by the
    build, since `#guard_msgs` compares. One wrong *comment* in the
    corpus ("a leaf where p is false", where two worlds are needed) was
    caught only because the search's tree was printed beside it.

## Stage 3, Run

13. **`reference/certify.md` §5 says raising `maxRecDepth` "was not
    tried".** Tried: `set_option maxRecDepth 100000 in` before a fact
    let a tree of 195 moves nested about 130 deep be elaborated, where
    without it Lean stopped with "maximum recursion depth has been
    reached". The driver now writes the option into every fact.
14. **A script printed by `Repr` over several lines is not always Lean
    source**: an argument on a new line at the column of its field's
    name is a parse error ("unexpected token '('; expected '}'"). What
    was done: scripts are printed on one line (width 10⁹).
15. **macOS has no `timeout` command** (`certify.md` §5: "the operating
    system's `timeout`"). The measuring script's own deadline
    (`subprocess.run(timeout=…)`) serves.
16. **The kernel is lazy and the compiled producer is not.** A tree of
    moves whose sequents double at every step was checked by the kernel
    in under a second where the compiled search needed 2 s and then
    more than 20 s to build the derivation. So measure the check of the
    certificate even where the producer is slow, and do not conclude
    from the producer's time what the kernel's will be.
17. **A frontier whose cause is the calculus.** Stage 3, step 4, speaks
    of "a fault of a search". Here the time went into the size of the
    object the search returns. The cure was a second certifier for a
    weaker property (that a derivation exists), with a producer that is
    not proved and a decision that checks it and falls back on the
    proved one. *Proposed*: add this pattern to `certify.md` §4 beside
    "the direct decision": a fast search that is not proved, wrapped as
    `if check then … else the proved decision`, is a decision procedure
    the kernel runs, and needs no proof about the fast search.

## Stage 2, Prove, continued: the delegated goals

18. **Handing three goals on by brief worked.** A fresh agent, with
    `brief-2-1.md` and the statements already in Lean as named types,
    returned the seven structural functions, the equivalence with PSGLS
    and the source's cut, all within the axiom policy, in 15 minutes
    (225 816 tokens by its own report). What it changed in the route
    the brief gave: recursion on a derivation needs the sequent as a
    variable index, so each function is stated for `Fam s` with the
    lists recovered by equations; every permutation is proved by one
    tactic that counts occurrences; `omega` on a goal with a
    disjunction brought `Classical.choice` in and was replaced by
    `Nat` lemmas. *Proposed*: say in `prove.md` that a brief which
    gives the statements as named Lean types and the tests the result
    must pass (`CutTest.lean` was written by the operator from the
    brief's list) is enough, and that the operator builds and runs the
    result before recording PROVED.
19. **A commit taken while an agent was writing included the agent's
    half-made file** (`Structural.lean`, first version, in `c9880e8`).
    It built, so the board was not false, but the commit's message
    names it. *Proposed*: rule 7 or the delegation section should say:
    an agent of the campaign works in the same tree, so name its files
    in the brief and leave them out of commits until it reports.

## The session, and the stop

20. **The session ended with a command running, and was resumed three
    hours later** (about 09:57 to 13:14). The scratchpad had been
    emptied; nothing of the campaign was in it except the downloaded
    Coq files, which were not needed again. Every file of the campaign
    was in the worktree. *Proposed*: none; the rule that the folder
    carries the state held.
21. **The answer to the first act's stop came after Explore was
    through.** The skill's text assumes the comparison with the prose
    precedes the proofs. What was done on the answer: the thesis read,
    the figure compared rule by rule by the operator and by a second
    cold reader on the pages (no difference), the skeleton given its
    numbers and pages, the sources of four statements filled in, and
    one new goal (cut elimination from GLS + (cut), the thesis's
    Theorem 12.7.2) entered and proved. Nothing proved before had to
    be built again. *Proposed*: `survey.md` should say what is owed
    when the source arrives late: the comparison, the skeleton's
    numbers, a pass over the standing list against the source's
    results, and nothing else unless the comparison finds a difference.
22. **A repository's "download" link returned an error page.** The
    thesis's `/bitstreams/<id>/download` gave HTTP 500; the same
    repository's `/server/api/core/bitstreams/<id>/content` gave the
    PDF. Worth a line in the Survey's notes on fetching (DSpace 7).
23. **`pdftotext` drops the box.** In the text taken from the thesis,
    `□` and `⊠` are missing, so GLR reads as a rule with no modality.
    The figure was read from a rendered image of the page. *Proposed*:
    `adopt.md` §1 should say to read every figure of rules from the
    page's image, never from extracted text.
24. **A definition of the operator's turned out to be in the source.**
    The models, GL frames and truth were stated at the Survey as "the
    usual semantics, none in the source's Coq files"; the thesis has
    them (Definitions 12.2.2 and 12.2.3) and they agree. The table of
    definitions in `statements.md` has a column for the source's item,
    which made the correction one cell.
25. **Reading back after the proof.** S24 was entered, proved and read
    back in that order, in ten minutes, since its proof is seven lines
    over S10. The skill's order would have cost nothing more. Recorded
    as a departure.
26. **A fault of the operator's own code that looked like a frontier.**
    `dedup` called itself twice on each element in compiled code; three
    families were cut off at sizes the first search handled. Found by
    comparing the two searches' times on the same input, not by any
    check of the skill. *Proposed*: `certify.md` §5: when a second
    search is slower than the first on a small member, suspect the
    code before the calculus.

## After the campaign: the notes made changes to the skill (2026-11-25 14:37 GMT)

Written by the session that started this campaign, not by its operator.
The reviewer's word, to the question whether to apply the changes this
file proposes: "Yes, apply them". Made in commit `b20b7aa` of proof-tools,
which changes the skill's files and nothing else.

| note | what the skill now says | where |
|---|---|---|
| 1, 2 | downloading public material is the reviewer's standing word (commit `28e3aa8`, before this one) | `SKILL.md`, "Downloading" |
| 3 | where another session started this one, the lines for the reviewer go in the session's own output, and the turn is not ended | `SKILL.md`, the first act, step 4 |
| 4 | the time of "told to the reviewer" is filled after the message is sent | `templates/decisions.md` |
| 5 | a formalisation published with the paper is part of the source: read beside the figure, not in place of the prose | `SKILL.md`, rule 1; `reference/adopt.md` §1 and §7 |
| 6 | where the source has no semantics, the operator states the logic's usual one, as a decision that costs the campaign | `SKILL.md`, "What a campaign proves" |
| 7 | where a goal is a function on derivations, the entry says which function; a cut from soundness and completeness is a second proof | `reference/adopt.md` §2 |
| 8 | a description above a pinned message is a `--` comment | `reference/explore.md` §10 |
| 9 | comment lines directly below a pattern line are taken with it | `reference/explore.md` §6 |
| 10, 25 | the Lean file of named statements is where a statement is displayed first; the proofs may begin while the reading back runs | `SKILL.md`, stage 2, steps 2 and 3 |
| 11 | screens as a file of `#guard`s in the build, with a control | `reference/adopt.md` §5 |
| 13 | `maxRecDepth` was tried, and works | `reference/certify.md` §5 |
| 14 | a script is printed on one line | `reference/certify.md` §5 |
| 15 | macOS has no `timeout` | `reference/certify.md` §5 |
| 16 | measure the kernel's check even where the producer is slow | `reference/certify.md` §5 |
| 17, 26 | a fast search that is not proved, beside the proved one; suspect the code before the calculus | `reference/certify.md` §4 |
| 18, 19 | what a brief gives when goals are handed on; the agent's files stay out of commits; the operator builds before PROVED | `SKILL.md`, rule 5; `templates/brief.md` |
| 21 | what is owed when the prose arrives late | `reference/adopt.md` §1 |
| 22 | look at what a download link gave back | `reference/adopt.md` §1 |
| 23 | a figure of rules is read from the page's image | `reference/adopt.md` §1 and §7 |

Not made changes: 12 and 24 report that the text held; 20 proposes
none. Notes 18 and 21 name files the skill does not have (`prove.md`,
`survey.md`): their changes went into rule 5 and `reference/adopt.md`
§1.

Added from the run's record, and in no note: the closing page is
written when the goals are settled, and a commit is made before a
measuring run (the session ended under a running command at 09:57 and
stood idle until 13:14, with no closing page); the skill's "Status",
which now says what this run does not show; this campaign as a third
worked instance.

## 2026-11-26: `glsrun prove`, a sequent typed at a shell

Written by the owner of `calculi/GLS`, at the directing session's
request. The text built from: `reference/certify.md` §5, "A judgment
typed at a shell", as it stood at commit `0e83910`; the instance read
beside it: Brünnler's K (`BrunnlerK/Parse.lean`, the `prove` part of its
`Main.lean`, `Corpus/prove_corpus.py`).

27. **What the paragraph still does not say, and what GLS needed that
    neither instance gave a model for.**

    *The paragraph does not say:*

    a. **That the program's own check of a certificate may be the slow
       one.** (2026-11-27: both cases below were faults of the checks'
       definitions and are repaired; note 28.) The paragraph, and K's `answer`, suppose that what the
       search returns is checked by the compiled certifier before it is
       printed, and that this is cheap. In GLS it is not, twice, and
       both times the kernel is the fast side (note 16 said so of the
       producer; it holds of the check too):
       - a tree of moves replayed on multisets builds sequents that
         double at each nested GLR. Compiled, `treeCert.check` on
         `□p → □³³p` does not end; the kernel checks that tree in under
         a second;
       - `Seq.refutedAt`, the check of `noValid` and `noDerivable`,
         evaluates `□A` at a world by evaluating `A` at every world
         below, keeping nothing. Compiled, `□³³⊥ → □³²⊥` on its chain of
         33 worlds was not checked in 10 s: **the first run on the
         families returned a flag for `consis 32`**, a sequent the
         search over sets settles in a millisecond. The kernel checks
         the same tree in 0.3 s.
       What was done: the program prints only what it has checked, by
       other means than the certifier's check where that is slow. For a
       derivation, a replay under a cap (no side of a sequent longer
       than 4 096 formulas), and beyond the cap the weaker fact alone
       (b). For a tree of worlds, a second evaluation by a table
       (`GLS/FastCheck.lean`), compared with `Seq.refutedAt` in the
       tests on 1 024 sequents at 200 worlds. The kernel still checks
       the printed certificate by the certifier.
    b. **That one verdict may have more than one kind of answer.** "State
       each [fact] from the one certificate" supposes each can be
       stated. Here "derivable" is two kinds: with the derivation as
       data (`treeCert`), and, beyond the cap of (a), the proposition
       only (`setCert`, which checks the same tree of moves over sets).
       So "one printed file of each kind of answer" is three files for
       two verdicts, and the first line does not tell the two apart: a
       comment in the file does.
    c. **Which search answers, where the campaign has two.** GLS has a
       proved search that is cut off at 28 nested boxes and a search
       over sets that is not proved. The command runs the second,
       checks its answer, and falls back on the first where the check
       fails (not seen). The paragraph's "what a flag is" has no case
       for this: with the fallback, a flag is still only the deadline,
       or a refused certificate of the proved search.
       A branch that is never taken is never run: the option `--proved`
       asks the proved search for the answer, so that its branch could
       be run on the corpus (23 of 25 agree; 2 flags at the deadline,
       where that search is known to be cut off).
    d. **That the corpus may not reach every kind of answer.** "Run on
       every entry" found two kinds and no fault. The third kind and
       the flag of (a) appeared only at members of the families
       (`boxChain 32`, `consis 32`). `glsrun families` lists nine
       members beside `glsrun corpus`, and the script takes both.
    e. **Whether a judgment may be abbreviated.** A person types a
       formula, not a sequent. Here a text with no arrow is one formula
       `A`, read as `⇒ A`, and the first line shows the arrow; two
       formulas with no arrow are refused.
    f. **The deadline of the script that runs the command.** §5's
       paragraph on measuring says a deadline ends the whole process
       group. K's `prove_corpus.py`, which the paragraph points to, uses
       `subprocess.run(timeout=…)`: that ends `lake` and leaves `lean`.
       GLS's script starts each command in a session of its own and
       ends the group (`os.killpg`).
    g. **Which alteration.** "One with its certificate altered refused":
       a tree of moves altered at random may still be a derivation. The
       alterations here cannot pass: the last IdP made a move on a
       variable the sequent does not have; a variable of the antecedent
       side made true at the root of the countermodel. One for each
       kind of answer. (A large certificate is printed with a move
       broken over two lines, `GLS.Move.idP` and then `0`: a script that
       alters text matches across white space. The first run reported
       "not checked" for that file, and said so.)

    *GLS needed, with no model in either instance:*

    h. **Two sides, each a list.** K's sequent has one side; DILL's has
       zones and one formula. Lean source writes a GLS sequent as
       `[A, B] ⇒ [C]`, so `[]` is `□` before a formula and a side with
       nothing in it before the arrow or the end, and a bracket that is
       not `[]` opens a list, only at the start of a side. Guarded:
       `[]p ⇒ q`, `[] ⇒ []p`, `[[]p] ⇒ [q]`, `[] ⇒ []`, and `[]`,
       `[], p ⇒ q`, `[[], p] ⇒ q` refused.
    i. **Connectives the library defines and the calculus does not
       have.** `GLS/Connectives.lean` (added after the campaign) defines
       `¬`, `⊤`, `◇`, `∧`, `∨` from `→` and `⊥`, with Lean notations for
       the last two. The reader uses those definitions, and the tests
       of binding have Lean terms on the right, so the reader's binding
       is compared with that of Lean's notations. The printers write
       `→`, `⊥`, `□` only: nothing folds a formula back into `∧`, and
       the guide shows an example of what the first line then looks
       like.
    j. **A fact weaker than the one wanted**, (b), and **a check of the
       program's own**, (a): a second evaluation that is not the
       certifier's needs its own test against the certifier's.

    *Asked of the directing session* (files that are not this owner's):
    in the paragraph, (a) and (b) under "What is printed" and "What a
    flag is"; (d) under "Run on the corpus"; (g) there too; (e) under
    "The reader". (f): K's script, or a line in the paragraph.

## 2026-11-27: the two checks repaired

Written by the owner of `calculi/GLS`, at the directing session's
request. The text built from: `reference/certify.md` §5, "The program's
own check", as it stood at commit `525f9cd`.

28. **What the repair found that the paragraph does not say.**

    a. **The kernel hid the second fault on one family only.** The
       paragraph says of the list replay that "the kernel reduces only
       as far as each step's test looks (no measurable time at 48)".
       That is `boxChain`, where the `p` that IdP asks for is first in
       the antecedent. On `lastChain n` (`⇒ □p → □ⁿq → □ⁿp`, the same
       derivation with `□ⁿq` put before `□p`) the kernel on the list
       replay took 10.4 s at `n = 16` and overflowed its stack at 24,
       32, 48 and 64. So "fast in the kernel" was a property of the
       family, and the advice "measure both sides on a family that
       grows" wants a second clause: on a family made against whatever
       is thought to make the kernel fast (here: the formula asked for
       put last).
    b. **Of the repairs the paragraph names, `@[csimp]` did not fit,
       for two reasons the paragraph could give.** With `@[csimp]` the
       kernel goes on running the definition, which is right only if
       the kernel's run of it has been measured good on such a family
       (a). And `@[csimp]` replaces a constant: the library's
       `Cert.check` is one function for every proof system, so a
       campaign has no constant of its own to replace. What GLS did:
       the certifier's `check` is the new function, its `sound` is the
       old soundness after the equality, and two theorems keep the old
       statements (`treeCert.check s c = Cert.check s c`). One function
       on both sides, and no attribute.
    c. **A check proved equal to the definition can be a poor
       algorithm too, and the proof does not say.** The first replay by
       counts looked each formula up in the whole side. Compiled it was
       fast at every size asked for (2.5 ms at `boxChain 64`); in the
       kernel it took 3.7 s there, and at 128 passed the cap of 8 GB,
       where the list replay took 0.03 s. It was seen only because the
       table was carried to 128 and 256, beyond the sizes asked for. A
       second form (the entries in order of size, the premise of GLR by
       one merge) was right on `boxChain` and over four times slower than
       the list replay on `kChain`, where a side has many formulas of
       one size; the third puts in the formula a move adds with no
       search. So the paragraph's advice wants: the repaired check is
       measured as the faulty one was, in the kernel as well as
       compiled, on every family and one size beyond; and "the
       algorithm one would run" is to be read for the kernel too, where
       a step costs some thousand times what it costs compiled. After
       the repair the kernel is still slower than it was where its
       laziness served the definition (1.4 s against 0.9 s at `kChain
       128`): that is not a fault.
    d. **The same sequents are written out by a search and by a
       script, and the paragraph speaks of checks only.** The search
       over multisets returns a derivation of GLS as a term, which
       holds every sequent; a script is replayed with its goals written
       out, since the explorer shows them. Neither is a check that can
       be proved equal to a better one: the size is in what is
       returned. For those, a deadline is not a cap on memory: at
       2 GB a second, 20 s is 40 GB. GLS now has a cap on the program's
       own memory (it asks the system five times a second and leaves
       with a flag above 8 GB) and the same in its measuring scripts.
       The skill could ask it of every compiled program of a campaign
       whose judgments can grow.
    e. **A timing of compiled code is to be checked against the time of
       the whole process.** The first timing command gave 80 µs for the
       list replay at `boxChain 20`, where the process took 0.1 s and
       137 MB: the work was not inside the clock. The check had been
       passed to the timer as `fun _ => check s c`; as a function of
       its own, not unfolded where it is used, with the unit as its
       last argument, the figure was 82 ms. Why the first form did the
       work early was not looked into.
    f. **"Statements first, screened before any proof" was kept for one
       statement of three.** For S25 and S26 the proof was written with
       the definitions and passed at once; the screen was run after and
       is kept as a guard. For S27 the screen came first and the proof
       took four rounds. The rule has no clause for a proof that takes
       less time than the screen; the statements page says which order
       each had.
    g. **A third kind of answer that no input gives any more** needs an
       option to ask for it, or the test "one printed file of each
       kind" has nothing to elaborate: `--sets`, as `--proved` for the
       fallback (note 27 c).

    *Asked of the directing session*: (a), (b), (c) in "The program's
    own check"; (d) there or in §5's advice on measuring; (e) with the
    advice on measuring.
