# Brief: Brünnler's system K, stage 1 (Adopt), after the rule table

Written 2026-11-23 14:19 GMT, at the gate note for the rule table, in
case the answer does not come while the session is open.

The target and the rules of the project are in
`calculi/BrunnlerK/campaign/gates.md`, the first entry, as changed by the
second: the files are in `calculi/BrunnlerK/`, and commits go to `main`
of `fairflow/proof-tools` (`git push origin HEAD:refs/heads/main`; never
the session's own branch).

## The task

Stage 1, Adopt, steps 5 to 9 of the skill's stage: the proof system, the
editor's part, the tests, the exercises file, the report. "Done" is the
report of the stage where the reviewer can read it, with the exercises
file handed over: the gate is **the reviewer's test**.

**None of it before the rule table is signed.** If `gates.md` has no
entry that passes the rule table, the first act is to record the
reviewer's answer if there is one, and otherwise to stop and ask.

5. `Move`, `step` through one function `Move.rule`, the proof system
   `S`, and S1 (`step_sound : S.SoundT K`); fill the last column of
   `rule-table.md`. State S2.
6. `Explorable S`, the tactic (an alias of `apply_move`), a way to write
   a sequent in Lean without `NSeq.cons` and `NSeq.leaf`.
7. The tests, every message pinned.
8. `Play/BrunnlerK.lean`: Example 2.3, the four further exercises of the
   plan's Q4, the non-theorems of the plan's table.
9. `report-1-<date>.md`.

## Read, in this order

1. The skill `calculus-campaign`: `SKILL.md` from "The method" on;
   `reference/explore.md` §2 to §10, §12, §13; the two Lean templates;
   Adopt's pitfalls.
2. `calculi/BrunnlerK/campaign/gates.md`: **record there, before
   anything else, any answer of the reviewer that came after this brief
   was written.**
3. `calculi/BrunnlerK/campaign/rule-table.md`: the transcription, the
   functions, the divergences D1 to D14. Whatever the reviewer changed
   at its gate comes first.
4. `calculi/BrunnlerK/campaign/plan.md`: Q3 (`within`), Q4 (the
   exercises, what the explorer should show), the known non-theorems.
5. `calculi/BrunnlerK/campaign/method-notes.md`, notes 19 to 25: add to
   it.
6. The Lean: `BrunnlerK/Sequent.lean` (the functions `step` must use),
   `BrunnlerK/System.lean` (the family), `BrunnlerK/Show.lean` (the
   printers), `BrunnlerK/Test/System.lean` (Example 2.3 as a term).

## What is settled

* Everything in `brief-1-1.md` under "What is settled".
* The modules, their names and the bound on each: the status board,
  `campaign/README.md`.
* The printer writes the source's notation (`∨`, `∧`, a bar over a
  negated proposition, formulas before boxes); the propositions print as
  `p q r s a b c d`, then `p8`, ….

## What is not settled

* **The rule table is put and not signed.** Its section "What the
  reviewer is asked to sign" lists five things.
* What a move carries. Proposed: what its constructor carries (`ax a p`,
  `and a A B`, `or a A B`, `box a A`, `dia a i A`), so that S1 is one
  constructor for each move; patterns and `candidates` fill them in.
  Whether the explorer has a move for `cut`: proposed no (the proof
  system is for K; `S.SoundT K`).
* `within` for `◇k_c`: the premise adds nothing where `A` is already in
  the box (the plan's Q3).
* How a sequent is typed in Lean: a term syntax. Go on with a proposal
  and show it in the report.

## Stop and report if

* The stage passes two sessions in all (the plan's budget; one is used).
* `step` does not reduce in the kernel on a small sequent
  (`decide +kernel` on one `S.step m j = .ok ps`).
* `apply_move`, or anything else of `proof-tools`, would need a change:
  the libraries are not changed.
* The reviewer's answer at the rule table changes a constructor: repair
  the family first, enter it in the table, and have the table signed
  again before step 5.

## Done looks like

* `BrunnlerK/Proof.lean` (or the name chosen) with `Move`, `step`, `S`,
  `step_sound`, within `[propext, Quot.sound]`; `BrunnlerK/Tactic.lean`;
  `BrunnlerK/Test/…`; `Play/BrunnlerK.lean`, which elaborates with
  `lake env lean Play/BrunnlerK.lean`.
* `rule-table.md` with its last column filled; `statements.md` with S1
  PROVED or OPEN and S2 stated.
* `report-1-<date>.md`, saying for each exercise what should happen;
  committed, pushed to `main`, and readable by the reviewer.
* A row in `cost-log.md`; the status board; `brief-2-1.md` after the
  gate.
