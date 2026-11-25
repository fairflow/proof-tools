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
