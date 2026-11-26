# Brünnler's system K: notes on the method

Every place where the skill `calculus-campaign` was wrong, silent or
unclear, and what was done there. Read at commit `e6410cd` of proof-tools.

## Stage 0

1. **The command does not exist where sessions start.** The skill is on
   the branch `proof-tools-home` (open pull request 6) and not on `main`.
   A session whose worktree is cut from `main` answers that no such
   command is available and treats the words as a plain request. What was
   done: the operator found `docs/campaign.md` on `main` and followed
   that. It is an older text and differs (no first act, no standing list,
   another place for the files), and nothing told the operator so.
2. **A skill added to the worktree during a session is not picked up by
   that session.** After the merge the files were present and the command
   was still unknown. What was done: `SKILL.md` was read as a file, which
   its third case allows for.
3. **The first act has no word for a session that has already read the
   source.** It forbids reading past abstracts and writing to disk before
   the answer. Here both had happened. What was done: the proposal was
   put all the same, and the history is written under the first entry of
   `gates.md`.
4. **The first act does not ask leave to download the source.** Its list
   of things asked covers the checkout, pushing and what is not to be
   touched. `reference/adopt.md` §1 then says to read the LaTeX and to
   run `paper_skeleton.py --arxiv`, which downloads an archive. This
   operator may not download a file without the user's word. What was
   done: the PDF that the web tool had already saved was read, the
   skeleton written by hand with printed numbers, and the question put in
   the Survey's report.
5. **Scratch Lean before the plan's gate is allowed only to see whether
   an encoding is feasible** (stage 0, step 3). Screening a statement of
   the plan needed a fragment of the semantics: formulas, a model, and
   forcing. What was done: two scratch files for it, outside the repository,
   said in the plan. The result changed what the plan proposes for "what
   valid means", so the screen earned its place; the skill should say
   whether it is allowed.
6. **`reference/explore.md` §13 lists three ways to hold a judgment that
   is not flat. A fourth was found**: a plain inductive type with direct
   recursion only (no list of itself), for which every `deriving` line
   works. Tried in scratch; in the plan.
7. **The rule "a standing result that holds of this system and has a
   source is a goal by rule" does not say which form.**
   `reference/adopt.md` §2 asks the plan to say whether the goal is that
   the rule is admissible or a procedure that removes it. The source
   states the first and proves it twice (a corollary of completeness, and
   a procedure). What was done: the statement is entered as the goal by
   rule and the route left to the reviewer.
8. **The reviewer's hook refuses to send a file from a worktree**, and
   the gate fixed that nothing is pushed. The skill's rule 6 offers
   "pushed, sent in full, or published". What was done: the plan and the
   report are published as one private page, rendered by
   `scripts/md-artifact.py` of lax-logic-private. That script prints the
   name of its own repository in the page's stamp; the stamp was
   corrected by hand.
9. **The cost log asks for requests, tokens and cost.** The environment
   gave none of them to the operator. Written "not known".
10. **The cost log's three classes of exchange (decision, correction,
    rescue) have no place for a question from the reviewer** about the
    mathematics. One came, and it led to two more screens and a section
    of the plan. What was done: entered as "a question".

## Stage 0, after the reviewer's answer at the plan's gate

Notes 1 and 2 are answered in the library by commit `07a5b2e` (the
README's "If the command is unknown"; the first act says whether the
checkout is behind `main`), which was written while this stage ran.

11. **Note 4, again.** The reviewer: "yes you may download the source,
    surprised you need permission". The limit is this operator's own
    (its environment asks for the user's word before any download), not
    the method's. A line in the first act, "asked: may the agreed source
    be fetched and compiled?", would have settled it in the first
    exchange. Not added to the skill: the reviewer did not ask for it.
12. **The default place, `examples/<Calculus>/`, is rejected by the
    reviewer**: "I think examples is a poor choice of target directory so
    please amend skill accordingly". The reviewer named no other. What
    was done: `calculi/<Calculus>/`, in every place the skill and the
    README named the folder; the layout of `reference/explore.md` §1 was
    built under the old name and does not depend on it.
13. **The skill was silent on the letters Lean reserves.** The source
    writes sequents `Γ, Δ, Λ, Π, Σ`. The reviewer: use `Θ`, `Φ`, `Ξ` (for
    `Σ`) and an upsilon. What was done: `Υ` for `Π`, `Ξ` for `Σ`; a
    paragraph in `reference/adopt.md` §3.
14. **`templates/statements.md` says to enter the classical form and the
    constructive form of a statement. A third way was wanted here**: keep
    the statement direct and restrict what it quantifies over (validity
    in every two-valued model). The operator had proposed the indirect
    form ("no model refutes the sequent") and the reviewer asked for a
    less absolute direct one. Where a statement about all structures
    implies a classical principle, the skill could say to look first for
    the class of structures the source means.
15. **A gate answered in part has no entry.** `templates/gates.md` has
    passed, passed with changes, and not passed. The reviewer's answer
    settled three decisions, changed two things the first gate had
    fixed (the place, the pushing), asked two questions and said nothing
    of the rest. What was done: "not passed", with each thing done on
    the answer, and the gate put again.
16. **Rule 7 and a reviewer who asks for a change to the skill.** The
    rule forbids a campaign to change a tracked file outside its folder.
    The reviewer asked for one. What was done: the change, in a commit of
    its own, said in the report.
17. **The skill's "Judgments as data" (`reference/adopt.md` §3) already
    says why no exchange rule is needed**, and the plan's table did not
    carry the reason, so the reviewer had to ask. The fault is the
    operator's. `templates/plan.md` could ask for the reason in the row,
    not the choice alone.
18. **`paper_skeleton.py` says of itself that it simulates the
    counters**, which the skill forbids. Run with `--src` on a source
    that compiles, it reads the `.aux` and says so in its output. The
    skill's sentence about it is right; the script's help text is old.

## Stage 1 (Adopt), to the rule table's gate

19. **Rule 5 against the reviewer's word.** The skill starts a stage in
    a fresh session. The reviewer: "Continue here with Adopt … I think a
    single session may be sensible, we'll see how much context is
    needed." What was done: the stage was run in the session of stage 0,
    from `brief-1-1.md` as written, read as a fresh session would read
    it. One line of the brief was false in that case (the scratch copy
    of the source was still there, and was used). The summary the
    session carried was enough with the brief; the parts of the skill
    were read again in full.
20. **The figure's letters and the encoding's.** A rule stated for a
    context needs, in the constructor, a name for the whole sequent at
    the node. The first draft called it `Δ`, and the figure's own `Δ`
    (the box of `◇k_c`) became `Λ`: the constructor then read against
    the figure with two letters moved. What was done: a letter the
    figure does not use, `Θ`, for the node, so that every letter of the
    figure keeps its meaning. `reference/adopt.md` §3 could say it:
    letters of the figure stay; what the encoding adds takes new ones.
21. **`#rules` prints names, and for a judgment that is not flat the
    names carry the rule.** Each premise is `Γ.setNode a (…)`: the table
    is unreadable without the definitions. What was done: three sections
    the template does not have, "How a rule of the figure reads in
    Lean", "The functions the rules use" (the definitions, extracted
    from the file by a script, not retyped) and "What the reviewer is
    asked to sign". `templates/rule-table.md` could carry them for §13's
    case.
22. **A side condition that looks local and is not.** The proviso of K°
    compares the set sequents of whole sequents. It looked equivalent to
    "the formula added is not already in the node". A test of three
    sibling boxes showed it is not. The skill's rule (side conditions
    are fields, transcribed as stated) was enough; the note is that the
    simplification was tempting and a four-line test refuted it.
23. **Tests of the family before its gate.** Step 4 says to write
    nothing that names the family while the gate waits. It does not say
    whether the family may be tested before the gate is put. What was
    done: the source's one worked proof was written with the
    constructors, as a check of the transcription, and is cited in the
    rule table. No `Move`, no `step`.
24. **A printer that writes a combining character.** `p̄` is the letter
    and U+0304. A `#guard` whose expected text was typed with the
    precomposed `ā` failed; the expected texts now spell `\u0304`. The
    messages pinned by `#guard_msgs` at step 7 will meet the same thing.
    `reference/explore.md` §10 could warn of it.
25. **`statements.md` at step 4.** The template's S1 and S2 name the
    proof system, which may not be written before the rule table is
    signed. What was done: both entered as "not written", OPEN.

## Stage 1 (Adopt), after the rule table's gate

26. **The gate answered in the session.** The skill: "After a gate
    inside a stage, go on in the same session if the answer comes while
    it is open." It came; `brief-1-2.md` had been written in case, and
    was read as the list of what to do. Nothing to change.
27. **S1 for a rule that looks its node up.** The template's S1 is
    `match m, j, hok, e' with`, each case a constructor: it relies on
    `m.rule j` reducing once the move and the shape of the judgment are
    known. Here every rule begins with `Γ.node? a`, which does not
    reduce for a variable `Γ`. What was done: the rule is split in two,
    `Move.ruleAt Γ Θ` (the rule, given the node) and `Move.rule` (look
    the node up, then `ruleAt`), with a lemma `rule_some`; S1 matches on
    `Γ.node? m.path` first and then is the template's match on `ruleAt`.
    `◇k_c` looks up a second thing (the box), and the same split was
    needed once more (`diaRule`, `diaSound`); a `match` on the second
    lookup inside the first did not generalise the hypotheses.
    `reference/explore.md` §13 could give the pattern.
28. **S2 in Adopt.** With the split of note 27 it was forty lines, and
    it found nothing wrong. Each case states `S.step m Γ = .ok [the
    premises written out]` and proves it by `simp` with the side
    conditions, since `(m.rule Γ).prems` does not reduce to the
    constructor's premises. Worth doing in Adopt for a calculus of this
    kind: it is the one check that `step` refuses nothing, and the
    reviewer's test cannot show that.
29. **`decide +kernel` on a step.** `reference/explore.md` §13 says to
    try `by decide +kernel` on one `S.step m j = .ok ps`. Core Lean has
    no `DecidableEq (Except String (List _))`. What was done: the kernel
    checks are on `(S.step m j).toOption = some ps`. The reference could
    say so.
30. **The combining character, as note 24 expected.** The messages
    pinned by `#guard_msgs` contain `a` and U+0304; text typed with the
    precomposed letter failed. The tests file now says so at its head.
    Also: the tool that writes files turned an escape `\u0304` typed in
    Lean source into the character itself.
31. **The tactic's name is a keyword.** `declare_move_tactic k for S`
    would make `k` a token in every file that imports it. The name is
    `kmove`. `reference/explore.md` §5 could warn that the name must not
    be a likely identifier.
32. **An exercise whose first query is an error.** The template writes
    the first query of every exercise. For a sequent no move applies to,
    that query is an error, and the file would not elaborate clean. What
    was done: for the two such exercises the query is left for the
    reviewer to type, and the text says what should happen.
33. **What `within` should be.** The reference leaves it to the
    instance. For this calculus the source has the notion already
    (Definition 2.13, the set sequent): a premise adds nothing exactly
    if it has the conclusion's set sequent. Where the source ends its
    search by a proviso, that proviso is the first candidate.
34. **Typing a judgment that is not flat.** The skill asks only that a
    judgment be a closed term. A term syntax was written (`seq[…]`,
    where an item in list brackets is a box): twelve lines of macro, no
    syntax category. Without it every statement is `NSeq.cons` and
    `NSeq.leaf`.

## Stage 2 (Prove), to the reviewer's goal

35. **A goal set by the reviewer, and a gate.** The reviewer set a goal
    for the session ("prove completeness and cut elimination") with the
    reviewer's test of Adopt not done and the statements of Prove not
    put. The skill said: stop at each gate; a stage starts in a fresh
    session. The operator stopped twice at the statements' gate. The
    reviewer's word: a goal is deliberate, and a later command overrides
    an earlier gate. The skill is amended: rule 6 of "How a gate is
    run", and a fourth result, "overridden by the reviewer", in
    `templates/gates.md`. What the skill should also say, and does not
    yet: what the operator may do while a gate is open. Here it went on
    with what rests on signed things only (the lemmas on paths,
    `Fam.lift`, the weight, the contexts), and said so.
36. **"Statements first" and a function into a sum.** `reference/adopt.md`
    §5 gives the form `def Completeness : Prop := …`. Goal 8 is data: a
    function, for every sequent, into a proof or a refutation. What was
    done: `abbrev ProofOrRefutation : Type := (Γ : NSeq) → K Γ ⊕
    Refutation Γ`, and the proof is `def proofOrRefutation :
    ProofOrRefutation`. The same for decidability. The reference could
    give this form beside the other.
37. **The route may differ from the source's, and then goals fall off
    it.** The plan's goals 2 to 7 are the source's lemmas on the way to
    its completeness theorem. With `Fam.lift` (a proof of a subtree is a
    proof of the whole, from deep inference alone) and a search that
    works at the root, none of them is used. The skill's rule for the
    order of goals ("a goal after those it rests on") assumes the
    source's order. Said at the gate; the goals stay OPEN and are put
    for decision in the report.
38. **A function on derivations is written by matching, not by
    `induction`.** `Fam.lift` by the tactic `induction` elaborated and
    then failed: "code generator does not support recursor
    `BrunnlerK.Fam.rec`". Written by pattern matching it compiles, and
    the search can be run. `reference/adopt.md` §6 could say so, since
    the family is into `Type` so that such functions are data.
39. **`Classical.choice` from a library lemma about lists.**
    `List.mem_erase_of_ne` brought it in; the file's bound caught it at
    once. Replaced by a six-line induction. `by_cases` on an equation of
    formulas did not bring it in (the type has decidable equality).
40. **A characterisation used as a `simp` lemma loops.** `NSeq.sat_iff`
    states truth of a sequent by truth of its boxes; given to `simp` it
    rewrites inside its own right-hand side. `rw` with the sequent named
    does what was meant.
41. **The screen before the proofs was cheap and was the check of the
    countermodels afterwards.** `Form.holds`, written for the screens of
    step 3, is the function `holds_iff` proves equal to truth in the
    model of finite trees, and the tests of the search use it to check
    each tree returned. As `reference/adopt.md` §5 says it would be.
42. **Deciding in the kernel.** The search is structural on a bound and
    the proofs it carries are propositions, so `decide +kernel` proves
    `Valid Γ` and `¬ Valid Γ` for the sequents tried. Plain `decide`
    stopped on one (it does not unfold the search). Not measured beyond
    the eleven sequents: Run is where the frontier is found.

## Stage 2 (Prove), after the gates were lifted

43. **"Act independently."** The reviewer, after two closing messages
    that each ended with a thing to sign and a choice to make: "Stop
    telling me to read and approve everything. Act independently." The
    skill made every stage end in a question to the reviewer, and the
    operator followed it. The skill now says the reviewer may lift every
    gate at once, and that a gate is then a record with the result
    "decided by the operator". What it still does not say: how a report
    should read when nothing is asked. Here the report's last part is
    "what was decided", with one line each.
44. **One relation in place of a case analysis on positions.** The
    source proves the admissible rules "by a routine induction", and
    contraction by cases on where the contracted sequent lies in the
    conclusion of the rule. With paths, each such case is a pair of
    paths and a lemma that two replacements commute. None was written.
    Instead: a relation between whole sequents, defined by recursion on
    the first (`Sub`: embeds; `SubR`: embeds, with a relation at the
    nodes; `Hom`: maps into), one lemma that a node and its image may be
    replaced together, and one theorem "a proof of `Γ` gives a proof, no
    deeper, of any `Γ'` it is related to". Weakening and exchange,
    the four inversions, and contraction are instances. Worth a section
    of `reference/adopt.md`, for any calculus whose rules act at a place
    inside a judgment.
45. **A statement about one occurrence needs a proof about several.**
    Invertibility of `∧` at one occurrence does not go through the
    induction: a rule on `(A ∧ B) ∧ C` puts a second `A ∧ B` into the
    node. The relation counts: some number of the occurrences replaced.
    The first attempt, replacing every occurrence everywhere by a
    function, is not depth-preserving, for the same reason.
46. **What Lean does not derive.** `DecidableEq` for a type that
    contains a list of itself (`Tree`). The finite model was first to be
    on the subtrees of the refuting tree, which needs that test for
    two-valuedness; it is on levels and trees instead, cut at the modal
    depth, and needs no recursion on trees at all. A type signed with a
    gate may turn out awkward later: the plan's probe of `deriving`
    (stage 0) was run on the type of sequents only.
47. **An estimate written as a fact, twice.** A time in `gates.md`, and
    the expected depth in one test, were written from expectation and
    not from the clock or from Lean. Both were caught in minutes (the
    commit's time; the elaborator). The rule holds for tests too: run
    it, then pin it.

## Stage 3 (Run)

48. **A producer that is proved, and reduces.** `lean-certify` is built
    for a producer that is not trusted. Here Prove left a search that is
    proved to end and to be right, and is structural, so the kernel can
    run it: `by decide +kernel` proves `Valid Γ` or its negation. The
    skill's Run stage does not consider this case. What was done: both
    routes, measured against each other. At the sizes tried the kernel
    running the search was the cheaper, and it has no certificate to
    write out. `reference/certify.md` could say: where the plan reaches
    level 3 by a structural function, try the direct decision first, and
    keep the certifier for the proof as an object and for a producer
    that is not proved.
49. **A certificate as a term has limits of its own.** A tree of 2 335
    moves, or one nested 256 deep, was not elaborated: Lean's limit on
    recursion depth while reading the term, before the kernel is
    reached. R6 and R8 of `lean-certify` speak of kernel time; this is
    earlier. Chunking (`certify_chunks`) is for a long `List.all`, not
    for a deep tree.
50. **Measuring found a fault of the search at once.** The family
    `late` was written to see where time goes, and showed proofs of
    `2ⁿ⁺¹ − 1` steps for an instance of the axiom. `reference/certify.md`
    §5 says the difference from a proof by hand "says what the search
    should learn"; here it could be taught in ten lines, with no proof
    changed. Worth saying in the skill that a fix found in Run may be
    made in a module of Prove, and is recorded with Run's gate.
51. **A word of the library is a keyword.** `size` cannot be the name of
    a function in a file that imports `LeanCertify` (the syntax of
    `certify_chunks … size n`). As note 31, for the tactic's name.
52. **What the measurement measures.** The first table called a term
    that was not elaborated "rejected", and its column "kernel". A
    rejected certificate is a defect; a term too large to read is a
    flag. The script's words were corrected before the table was kept.

## Stage 4 (Explore)

53. **The stage's first input may be empty.** The skill takes what the
    reviewer asked for at the reviewer's test as the first input of
    Explore. The reviewer deferred the test, and then lifted the gates.
    The stage was done from the plan's Q4 alone. The skill could say
    what Explore is when Adopt's gate is still open.
54. **Two gates need the reviewer's hands.** The reviewer's test and
    the tutorial are not statements to sign: they are things to do at a
    keyboard. "Decided by the operator" has no meaning for them. They
    are recorded as put and not done, and the campaign ends with both
    open. The skill's rule 6 could name them as the two gates that
    lifting does not pass.
55. **The suggestion of a pattern line takes the comment with it.** A
    line `kmove or   -- a comment` is offered back as `kmove or` with
    its arguments written after the comment. In the tutorial the
    comments are on lines of their own.
56. **A whole campaign in one session.** Five stages, from the command
    to the closing report, with summaries of the earlier parts made by
    the environment on the way. What was lost by it, if anything, the
    operator cannot tell from inside: the documents were the memory, as
    the skill intends, and each stage was begun by reading them and the
    Lean files again.

## After the closing report: the sixteen changes, made

The reviewer: "make the 16 remaining changes to the skill". Made in
commit `3186d6d`. The report's table is left as it was sent; this is its
last column, brought up to date.

| change (the report's words) | note | where it is now |
|---|---|---|
| say what the operator may do while a gate is open | 35 | `SKILL.md`, "How a gate is run", 1 |
| name the two gates that lifting does not pass | 54 | `SKILL.md`, "How a gate is run", 6, last paragraph; `templates/gates.md`, the result "put, and not done" |
| what Explore is when the reviewer's test has not been made | 53 | `SKILL.md`, stage 4, step 1 |
| the first act: ask leave to download, or say none is needed | 4, 11 | `SKILL.md`, the first act, 3; `reference/adopt.md` §1 |
| a gate answered in part: a form for its entry | 15 | `SKILL.md`, "How a gate is run", 4; `templates/gates.md`, the result "answered in part" |
| a stage in the session of the one before, at the reviewer's word | 19, 56 | `SKILL.md`, rule 5 and "How a gate is run", 5; `templates/cost-log.md`, the column's third value |
| a relation on whole judgments in place of a case analysis on positions | 44, 45 | `reference/adopt.md` §6, the last part; a pointer in §2 |
| the form of a goal that is data | 36 | `reference/adopt.md` §5 |
| a function on derivations by matching, not by `induction` | 38 | `reference/adopt.md` §6 |
| S1 for a rule that looks its node up; `decide +kernel` on a step through `.toOption` | 27, 29 | `reference/explore.md` §13 |
| a tactic's name, and a library's words, are keywords | 31, 51 | `reference/explore.md` §5; a line in `reference/certify.md` §1 |
| where the search is proved and structural, try the direct decision first | 48 | `reference/certify.md` §4 |
| a certificate as a term has limits before the kernel | 49, 52 | `reference/certify.md` §5 |
| a fix found in Run may be made in a module of Prove | 50 | `SKILL.md`, stage 3, step 4; `reference/certify.md` §5 |
| requests, tokens and cost are not known to an operator that is a model | 9 | `templates/cost-log.md` |
| the plan's probe of `deriving`: on every type the plan names | 46 | `SKILL.md`, stage 0, step 3; `templates/plan.md`; `reference/explore.md` §13 |

57. **Changed with them, since the new text made it false**:
    `reference/explore.md` §13 said that no public instance has
    judgments that are not flat. It now names this one.
58. **Seen, and not changed, since the reviewer's word did not cover
    it.** `SKILL.md`, "Status", still says that the whole has not been
    run by an operator starting cold; it has now been run once, in one
    session, with the gates lifted from the middle of Prove and the two
    keyboard gates not done. "The worked instance" still names the
    subframe tableau as the only instance outside the library's tests.
    The last paragraph still says the text was checked against
    `proof-tools` at `3fa25c0`. Notes of this file that the report did
    not turn into changes are not in the skill either: 5, 6, 10, 14,
    17, 18, 20, 21, 23, 24 and 30, 28, 32, 33, 34, 37, 43, 55.
59. **Not tried.** The new text is prose and four schematic fragments
    of Lean, each copied in shape from a file of this campaign that
    compiles; the fragments themselves are not compiled, and no
    operator has yet run a campaign from the amended skill.
60. **"Status" and "the worked instances", brought up to date** at the
    reviewer's word ("Yes, update them"), in commit `d5c7f14`. The
    instances outside the library's tests are now two: the subframe
    tableau, and this one. "Status" says that the whole has been run
    once, and lists what that run does not test. Note 58 was loose on
    one point, put right here: the old sentence said that no operator
    *starting cold* had run the whole, and that is still so. This
    operator had read the source and written a first plan before it had
    the skill (`gates.md`, the first entry; note 1). The new text keeps
    that sentence, in its last paragraph, with the other three things
    a full run needs and this one lacked: a fresh session at each
    stage, every gate put to the reviewer, the two keyboard gates done.
    Still not changed, since the word did not cover it: the last
    paragraph of `SKILL.md`, "checked against `proof-tools` at commit
    `3fa25c0`". Nothing of the amended text was checked against a later
    commit of the library, so that line is still what is true.

## After the closing report: the eighteen other notes, made changes

The reviewer: "turn the eighteen method notes into skill changes too".
Made in commit `5337dd4`. They are the notes that note 58 lists.

| note | what the skill now says | where |
|---|---|---|
| 5 | a statement the plan proposes may be screened in scratch before the plan's gate, and the plan says what the screen showed | `SKILL.md`, stage 0, step 3 |
| 6 | a fourth way to hold a judgment that is not flat: a type that holds itself directly and never in a list; every `deriving` line works | `reference/explore.md` §13, the table's second row |
| 10 | a fourth class of exchange, "question"; a message of two classes is entered once with both | `templates/cost-log.md` |
| 14 | a statement about every structure may imply a classical principle: first the direct statement over the class of structures the source means, then the indirect form, then the two forms | `reference/adopt.md` §5; a pointer in `templates/statements.md` |
| 17 | the plan's table of choices gives, with each choice, what it does to the rules: a rule of the source that needs no constructor, a rule added | `templates/plan.md` |
| 18 | the skeleton script's header is old; on a source that compiles it reads the `.aux` and says so; read that line before citing a number | `reference/adopt.md` §1 |
| 20 | the figure's letters stay; what the encoding adds takes letters the figure does not use | `reference/adopt.md` §3 |
| 21 | where judgments are not flat, the rule table has three further sections: how a rule of the figure reads in Lean, the functions the rules use, what the reviewer is asked to sign | `templates/rule-table.md`; `reference/adopt.md` §4; pointers in `SKILL.md`, stage 1, step 4, and `reference/explore.md` §13 |
| 23 | the source's worked derivations, as terms of the family, are a screen of the family: written before the rule table is sent, or while its gate waits | `SKILL.md`, stage 1, step 4, and "How a gate is run", 1 |
| 24, 30 | a printer that writes a combining character: escapes in expected strings, pasted text in pinned messages, a line at the head of the tests file, and reading back what a tool wrote | `reference/explore.md` §10 |
| 28 | S2 is proved in Adopt for a calculus whose judgments are not flat | `reference/explore.md` §13 |
| 32 | an exercise at a judgment no move applies to has no query written; the text says what the reviewer types and sees | `reference/explore.md` §10; a comment in `templates/Play.lean.txt` |
| 33 | `within`: where the source ends its search by a proviso, that proviso is the first candidate | `reference/explore.md` §5 |
| 34 | a term syntax for judgments that are not flat, pinned by `rfl` in the tests | `reference/explore.md` §13 |
| 37 | the plan's order is the source's route; goals that fall off another route stay goals, stay OPEN, and are put to the reviewer | `SKILL.md`, stage 2, step 4; a line in `templates/plan.md` |
| 43 | the form of a report's last part where the gates are lifted: "What was decided", and "The reviewer's, and not done" | `templates/report.md`; `SKILL.md`, "Reports, the folder, the log" |
| 55 | no comment after a pattern: comments on lines of their own in the exercises and the tutorial | `reference/explore.md` §6, §10 and §11 |

61. **Decided on the way.** Note 23 asked a question and gave no
    answer. The answer written is what this campaign did: the source's
    worked proof as a term of the family is a screen of the family, so
    it is allowed before the gate and while it waits; `Move` and `step`
    still wait. Note 10 named one class; the entry for a message of two
    classes was added with it, since rows 14 and 16 of this campaign's
    log needed it. Note 43 said what one report did; the template's
    form is that report's.
62. **Not tried.** One new fragment of Lean (`def Valid`, in
    `reference/adopt.md` §5) is schematic, in the shape of
    `BrunnlerK/Semantics.lean`, and is not compiled. The exercises
    template got a comment only. The skeleton script's messages were
    read in its source (lax-logic-in-lean, the working copy on this
    machine), not by running it again. No campaign has been run from
    the skill as it now stands.
63. **The list of eighteen was short.** Note 58 listed the notes "that
    the report did not turn into changes", and left out eight that ask
    for one, or for a line: 3, 7, 8, 16, 22, 25, 39 and 47 were in
    neither list. The operator's miscount. They are made in a commit of
    their own after this one, so that it can be taken back alone; the
    next section says where each is.

## The eight notes the list of eighteen left out

Made in commit `9cbfec1`, on the same word of the reviewer, read as
"the notes that are not yet in the skill". The reviewer said eighteen;
these are beyond that count, and are in a commit of their own.

| note | what the skill now says | where |
|---|---|---|
| 3 | a session that has read the source or written files before the first act puts the proposal all the same, and says what was read and written | `SKILL.md`, the first act, after step 4 |
| 7 | where a standing result has more than one form or route, the goal by rule is the statement the source states; form and route are the reviewer's | `SKILL.md`, "What a campaign proves" |
| 8 | the first act asks how a report reaches the reviewer while nothing is pushed | `SKILL.md`, the first act, 3 |
| 16 | the reviewer may ask for a change to the skill during a campaign: a commit of its own, the words in `gates.md`, said in the report | `SKILL.md`, rule 7 |
| 22 | a side condition that looks local and is not: transcribed as stated, a simpler form tested first | `reference/pitfalls.md`, 8 |
| 25 | S1 and S2 at step 4 of Adopt: entered as displayed, "not yet in Lean", OPEN | `templates/statements.md` |
| 39 | `List.mem_erase_of_ne` brings in `Classical.choice`; `by_cases` on a decidable equation does not | `reference/adopt.md` §6 |
| 47 | an estimate written as a fact: a time from `date`, a pinned value from Lean's output | `reference/pitfalls.md`, 11 |

64. **Notes that are still not in the skill, and why.** 1 and 2 are
    answered in the library (commit `07a5b2e`). 26 says there is
    nothing to change. 41 says the reference was right. 42 is the
    direct decision of `reference/certify.md` §4, already there from
    note 48. 40 (a characterisation given to `simp` rewrites inside its
    own right-hand side) is about Lean in general and not about a
    calculus. 57 to 63 are about these changes themselves.
65. **Renumbered**: the entries of `reference/pitfalls.md` after 7. No
    file of the skill cites one by number (searched).
66. **Still not changed**: the last paragraph of `SKILL.md`, "checked
    against `proof-tools` at commit `3fa25c0`" (note 60).

## After the campaign: the skill rewritten for an operator that works independently (2026-11-25)

67. **What the rewrite changed.** The reviewer's word: `gates.md`, the
    last entry. In the skill at commit `1611566`:

    | before | now | where |
    |---|---|---|
    | the first act puts a proposal and stops | the operator decides the target by stated defaults, tells the reviewer, goes on | `SKILL.md`, the first act |
    | seven gates, each a stop | each choice an entry of `decisions.md` with its cost to reverse (little, a stage, the campaign) | "Deciding, checking, stopping", 1; `templates/decisions.md` |
    | the reviewer signs the rule table | a second transcription by a cold reader, compared row by row | `reference/adopt.md` §7; `templates/rule-table.md` |
    | the reviewer sees each statement before its proof | each is screened, and read back from the Lean by a cold reader | `reference/adopt.md` §7; `templates/statements.md` |
    | the reviewer's test, typed by a person | every exercise run by script in the tests; the file is a way in, at any time | `reference/explore.md` §10 |
    | the tutorial worked through by the reviewer | every line elaborated, what it shows pinned | stage 4, step 3 |
    | soundness before completeness | both before every other goal, as a check of the rule table | stage 2, step 4 |
    | a report of five parts at each stage | a status board, and one closing page of six parts that asks nothing | `templates/report.md`, `templates/README.md` |
    | a fresh session at each stage, begun by the reviewer | sessions are the operator's to arrange | rule 5 |
    | a need of the library: stop and report | record it, work round it or leave the goal OPEN, go on | rule 7 |
    | only the reviewer sets a goal aside, at the plan | the operator never sets one aside: a goal not reached is OPEN | "What a campaign proves" |
    | gates lifted by a word of the reviewer | a gate only where the reviewer asks to pass a thing themselves | "Deciding, checking, stopping", 5 |

    What still stops a campaign: what only the reviewer may do or allow;
    an act that cannot be undone outside the folder; no source.
68. **Not tested.** No campaign has been run from this text. The second
    transcription and the reading back have not been tried at all: this
    campaign had neither. Whether a cold reader's table can be compared
    row by row with the operator's, for a calculus whose judgments are
    not flat, is not known.
69. **What the rewrite gives up.** At the plan's gate the reviewer chose
    the direct form of `Valid` over two-valued models, where the
    operator had proposed the indirect one (note 14). Nothing in the new
    text makes that choice better: `reference/adopt.md` §5 now gives
    the order of the forms, and the closing page puts such a decision
    first, to be reversed afterwards.
70. **The rewrite was read cold before it was committed.** A second
    agent, given the files and the intent and not the operator's view
    of them, reported thirty findings; all were applied. The serious
    ones were in the new checks: the second transcription was to be
    compared with "yours", which could have meant the column copied
    from the source (it is now what `#rules` prints); the reading back
    gave the reader Lean whose comments and names say what to find (now
    an extract, with comments out and neutral names); and nothing kept
    a subagent in the same checkout from opening the campaign folder
    (the brief now names what may be opened). One finding is applied in
    the text only: the worked derivations go in a test module that
    imports the theory file alone, and the compiled template has no
    such module.

## After the campaign: a sequent typed at a shell (2026-11-26)

By the owner session of this calculus, which did not run the campaign.
The task: `ksearch prove '<sequent>'`, built first from the one bullet of
the skill that asks for it (`reference/certify.md` §5, the third way of
delivering a fact: "For one judgment typed at a shell: …") and only then
compared with the one instance there was, DILL's (`calculi/DILL/DILL/
Parse.lean`, `prove` in its `Main.lean`, `DILL/ParseTest.lean`, the
section "From the command line" of its user's guide, all at commit
`3f435db`).

71. **What was built from the bullet alone, and what was changed after
    the comparison.** From the bullet: the reader (`BrunnlerK/Parse.lean`),
    the command, the tests (`BrunnlerK/Test/Parse.lean`), `ksearch corpus`
    and `ksearch show`, the script `Corpus/prove_corpus.py`. The bullet
    was enough to build a command that works; it did not settle the
    twelve things of note 72. After the comparison four things were
    changed to DILL's, so that the calculi are used alike: the option
    for the first line is `--short` (it was `--verdict`); `--ascii` and
    a printer with the signs of a keyboard were added (`NSeq.ascii`:
    the bar over a proposition is a combining character, which a
    terminal may draw over the wrong letter); the text is the arguments
    joined by spaces (it was one argument, anything else an error);
    the report of a fault counts characters from 1 (it counted from 0).
    Where the two instances still differ, and K's way is kept: note 74.

72. **What was needed and the bullet does not say.**

    a. *What the fact is, where a calculus has several.* "The fact with
       its certificate": K has `K Γ` (a proof, data), `Derivable Γ`,
       `¬ Valid Γ` and `¬ Derivable Γ`. Printed here: on the yes side
       `def proof : K sequent` and `theorem derivable`; on the no side
       both theorems, from one tree.
    b. *That the file must pin its axioms.* "The kernel checks" is said
       in this project only with the axioms bound. The file ends with
       `#axioms_within_file [propext, Quot.sound]`, which needs
       declarations with names: an `example` cannot be audited.
    c. *That the judgment has to be written as Lean source, and that
       this is a second printer to test.* The first line shows the
       sequent as the calculus prints it; the fact is stated of
       `seq[…]` as a printer of Lean source writes it. They are the
       same sequent only if Lean reads that text as the sequent it was
       written from. K had no such printer for a whole sequent
       (`NSeq.src` is new) and the file has to declare the names the
       printer uses for propositions. Tested: Lean's own parser and
       elaborator are given the text of every entry, and the value is
       compared (`Test/Parse.lean`, `leanReads`). The bullet's test,
       reading back what the printer writes, is the other direction and
       does not cover this.
    d. *Which printer.* "What the printer writes": K has three (the
       source's notation, Lean source, the signs of a keyboard). All
       three are read back for every entry.
    e. *What a flag is where the search always answers.* Exit code 3 is
       named; K's search is total and one side always has a certificate
       (`decided`). The flags here: the search cut off at a deadline,
       and a certificate that did not pass the compiled check (a
       defect, never seen).
    f. *That the command must end by itself.* A person at a shell has
       no deadline imposed from outside. `--deadline=N`, 10 s where not
       given: the search runs as a task and the command leaves with 3.
       The bullet's source for exit codes, `Certify.Cli`, has such an
       option; the bullet does not carry it over.
    g. *Where `Cli` is.* "The exit codes of `lean-certify`'s `Cli`":
       there is no file of that name; it is the namespace `Certify.Cli`
       at the end of `LeanCertify/Decider.lean`, and its `main` cannot
       be used without a registry of tools, which no campaign has. Only
       the four numbers are taken.
    h. *What "not read" reports.* "2 a text not read": here the place,
       what was expected, the text and a mark under the place, on the
       error stream, with nothing on the standard output. From which
       number characters are counted is not said: this reader counted
       from 0 and DILL's from 1. DILL prints no mark.
    i. *What "as it was read" is where the reader computes.* K's
       negation and `⊃` are functions, so `[](a -> b)` is read as
       `□(ā ∨ b)` and printed so. The guide has to say it, or the first
       line looks like a misreading.
    j. *The limits of a term apply to this file, and the file must lift
       them itself.* §5 has the paragraph (further down, for the
       driver); for a file made at a shell nobody adds the option
       afterwards. And one option was not enough: with
       `maxRecDepth` raised, the two members the campaign recorded as
       not elaborated (`boxAnd 64`, 2 335 moves; `nest 256`) stopped at
       Lean's limit on heartbeats instead; with `maxHeartbeats 0` as
       well they were elaborated, in 17 s and 13 s. So the frontier of
       `measurements-2026-11-23.md` for "a fact with its certificate"
       is a frontier of the default options, not of the route. The
       sequent itself, as a term, met the limit before the certificate
       did (`nest 256`).
    k. *How the command is run on the corpus.* The bullet tests the
       reader on the corpus, inside the library. To run the command
       itself on every entry the corpus is needed as texts at a shell:
       `ksearch corpus`, and a script that compares exit codes with the
       recorded status and elaborates each file.
    l. *The option for the first line, and its name.* Not in the
       bullet; DILL has `--short`.

73. **What K needed and DILL's instance gave no model for.**

    a. *A judgment that nests.* DILL's sequent is flat: two zones and a
       formula. A nested sequent is read by a reader that calls itself
       at each bracket; a bracket not closed is reported with the place
       where it was opened; formulas and boxes may be mixed and are
       kept as `seq[…]` keeps them (formulas in their order, boxes in
       theirs), which is not the order typed.
    b. *A sign of the keyboard that is also a bracket of the
       structure.* `[]` is `□` on every keyboard and is the empty box
       of this calculus. Settled by looking one sign further: before a
       formula it is `□`, before a comma, a closing bracket or the end
       it is the empty box. Guards: `[]a`, `[[]a]`, `[], a`,
       `[[], a]`, `[][a]` (refused: an empty box and a box with no
       comma).
    c. *Connectives that are functions, and a sign that follows its
       formula.* Negation is computed while reading; the printer's
       negated proposition is the letter followed by U+0304, a sign
       read after the name. `∅` for the empty sequent has no sign of a
       keyboard: the printer of keyboard signs writes `seq[]`.
    d. *The no side.* The campaign built a certificate of
       non-derivability and it is used: a finite tree, a countermodel
       (`BrunnlerK.Tree`), checked by `noValid` against validity and by
       `noDerivable` against derivability (soundness carries one to
       the other). DILL's is a saturated set of sequents, which says
       only that there is no derivation; K's says more, and the file
       states both.
    e. *No budget.* DILL's search has a number of copies, and `flag`
       is a real third answer of its procedures. K has none: the search
       is proved to end, and the only bound is time.
    f. *A proof that is data.* `K Γ` is a type; the file gives the
       proof as a `def` and the proposition as a theorem. DILL prints
       one `example`.
    g. *One side only.* No turnstile: `a |- b` is refused, at the `-`.

74. **Where the two instances differ and K's was kept.** K's file has
    named declarations and ends with the bound on axioms; DILL's prints
    an `example` and no bound (note 72 b). K writes the options that
    lift Lean's limits only for a large answer, and both of them; DILL
    writes `maxRecDepth 100000` for every answer and not `maxHeartbeats`
    (note 72 j). K prints nothing but the file after the first line;
    DILL prints two more lines of comment (the size of the derivation,
    the budget). K marks the place of a fault under the text; DILL
    names the character only. None of these was settled by the bullet,
    and a person who uses both will meet each.

75. **Asked of the directing session** (files that are not this
    owner's). In `reference/certify.md` §5, the bullet: say that the
    file names its declarations and ends with the bound on axioms; say
    that the judgment is written as Lean source by a printer that is
    tested through Lean itself; name the options `--short` and
    `--ascii`, and a deadline where the search has no budget; say what
    a flag is for a search that always answers; fix from which number
    characters are counted; say that the file lifts Lean's limits
    itself, with both options; say where `Certify.Cli` is. In the same
    section, the paragraph on the limits of a term: `maxRecDepth` alone
    moved the limit to the heartbeats here; both are needed. For DILL's
    owner: its printed file has no bound on axioms. Not asked: a
    library function for the read-back test through Lean
    (`leanReads`, fifteen lines of `Test/Parse.lean`) would serve every
    calculus that prints its judgments as Lean source.
