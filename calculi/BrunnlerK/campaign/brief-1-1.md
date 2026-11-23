# Brief: Brünnler's system K, stage 1 (Adopt)

Written 2026-11-23 09:36 GMT.

The target and the rules of the project are in
`calculi/BrunnlerK/campaign/gates.md`, the first entry. **The second entry
changes two things the first fixed**: the files are in
`calculi/BrunnlerK/` (not `examples/BrunnlerK/`), and commits go to
`main` of `fairflow/proof-tools` (`git push origin HEAD:refs/heads/main`;
never the session's own branch). The third entry passes the plan.

## The task

Stage 1, Adopt, as far as its first gate: the Lake package, formulas and
nested sequents as data, the calculus as an inductive family, and the
rule table put to the reviewer. "Done" for this session is the gate note
for **the rule table**, where the reviewer can read it. If the answer
comes while the session is open, go on with steps 5 to 9 of the skill's
stage; otherwise write `brief-1-2.md` and end.

1. Set the project up in `calculi/BrunnlerK/` (`reference/explore.md`
   §1) and build it empty.
2. Formulas (negation normal form, with the dual `Ā` as a function) and
   nested sequents as data, with their printers.
3. The family for system K: the axiom and `∧`, `∨`, `□`, `◇k_c` of
   Figure 2.3 (label `fig:kx`), and `cut` of Figure 2.4
   (`fig:admissible`) under a Boolean parameter. Then `K°` (the source's
   pp. 14–15, prose, no figure) as a family of its own. `#rules` and
   `#slime` on each.
4. `rule-table.md`, with the notation table (it carries the letters:
   `Υ` for the source's `Π`, `Ξ` for its `Σ`) and every divergence;
   start `statements.md` with the ten goals. **Gate: the rule table.**

## Read, in this order

1. The skill `calculus-campaign`: `SKILL.md` from "The method" on;
   `reference/adopt.md` §3 and §4; `reference/explore.md` §1 to §10, §12
   and §13; the two Lean templates; Adopt's pitfalls.
2. `calculi/BrunnlerK/campaign/gates.md`: **record there, before
   anything else, any answer of the reviewer that came after this brief
   was written.**
3. `calculi/BrunnlerK/campaign/plan.md`: Q1 (the figure, and the eight
   places where the source is ambiguous or silent), the table of
   encodings, the goals.
4. `calculi/BrunnlerK/campaign/skeleton.md`, for labels.
5. `calculi/BrunnlerK/campaign/method-notes.md`: add to it.
6. The source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 **v1**,
   pp. 6–15. The reviewer has allowed fetching it (`gates.md`, the
   second entry): the PDF, and the TeX source `arxiv.org/src/1004.1845v1`
   (69 kB) to a folder outside the repository. The copies of stage 0
   were in a temporary folder and are gone. Transcribe from the source,
   not from the plan's transcription of it.

There is no Lean of the calculus yet, and no file of the development to
read.

## What is settled

All by `gates.md`, the third entry (the plan, passed 2026-11-23), unless
another entry is named.

* The system: K alone, at `X = ∅` (the first entry).
* The ten goals of the plan are all goals.
* Sequents: `leaf (fs : List Form)` or `cons (inner) (rest)`; a new box
  goes after the existing ones. Stage 0 tried this type in scratch:
  `DecidableEq`, `Repr` and `ToExpr` derive, and the functions on it
  were structural. The scratch files are gone; nothing is to be copied.
* A rule names a path of box positions to the node and, in the node,
  its main formula (for `◇k_c` also the position of the box). The
  conclusion of every constructor is the variable `Γ`.
* Lists, no exchange rule: every rule finds its formula at any position.
  Exchange is goal 4.
* The family is into `Type`; one family with a Boolean parameter for
  `cut`; `K°` a second family; depth and cut rank are functions on
  derivations, not indices.
* What holds: the family itself.
* The letters: `Υ` for `Π`, `Ξ` for `Σ`, then `Θ` and `Φ` (the second
  entry).
* The axiom policy: every theory file within `[propext, Quot.sound]`.
* "Valid" (`Valid`, over two-valued models) and the search without
  cyclic leaves are settled too, but belong to Prove and Run: nothing of
  them is written in this stage beyond the statements in
  `statements.md`.

## What is not settled

Go on with the recommendation and show each in the rule table, where the
reviewer signs it:

* How a constructor says "the node at path `a` has `A ∧ B` at this
  position, and the premise has it replaced": by functions that `step`
  will also use, so that `#slime` reports nothing. The plan fixes the
  idea, not the functions.
* Where `◇k_c` puts `A` in the box, and where `∨` puts `A, B`: at the
  place of the main formula, or at the head. Choose what makes goal 4
  (exchange) plainly true, and say which.
* Whether the axiom `Γ{p, p̄}` asks for `p` and `p̄` by position or by
  membership.
* `K°`: its two provisos (`□°` only where no child contains `A`; each
  premise's set sequent differs from the conclusion's) as side
  conditions. If the second cannot be a side condition without a
  computed index, stop and ask.
* The eight ambiguous or silent places of the plan's Q1: each has a
  proposal there; each is a row or a divergence in the rule table.

## Stop and report if

* The stage passes two sessions (the plan's budget).
* A function on sequents used in a side condition does not reduce in the
  kernel on a small sequent (`decide +kernel`).
* `apply_move`, or anything else of `proof-tools`, would need a change
  to name a place inside a sequent: the libraries are not changed.
* A rule of the figure cannot be written without a computed index in
  its conclusion.
* A transcription differs from the source in a way that changes a goal.

## Done looks like

* `calculi/BrunnlerK/`: `lakefile.toml`, `lean-toolchain`,
  `lake-manifest.json`, the root module, the modules for formulas,
  sequents and the two families; `lake build` clean; `#rules` and
  `#slime` left in the files, `#slime` reporting none after its control.
* `campaign/rule-table.md` and `campaign/statements.md`.
* The gate note for the rule table: committed, pushed to `main`, and
  readable by the reviewer (a GitHub link at the commit; the reviewer
  cannot open files of a session's worktree).
* A row in `cost-log.md` for the session, the exchanges classed; the
  status board in `campaign/README.md` brought up to date.
* If the gate is not answered in the session: `brief-1-2.md`.
