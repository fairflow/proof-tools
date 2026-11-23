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
