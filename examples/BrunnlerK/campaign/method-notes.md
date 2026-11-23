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
