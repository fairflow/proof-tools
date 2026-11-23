# Proof tools

Tools, and a method, for taking a proof calculus from its paper to a form
that Lean's kernel checks and that people can use: transcribed, proved
correct, run by certified procedures, and explored by hand. Lean 4, core
Lean only (no Mathlib).

**Status, 2026-11-19.** This repository continues lean-certify under a wider
name. `LeanCertify` is unchanged. `ProofTools.Audit`, `ProofTools.Zipper`
and `ProofTools.Explore` are new here; the explorer has its tests' example
calculus as its only instance so far. No release of `proof-tools` is tagged
yet; lean-certify's tags (v0.1.0 to v0.3.0) are in this history.

## The parts

| Part | What it is | Status |
|---|---|---|
| `LeanCertify` | Certified computation: an untrusted fast producer computes a certificate, and a checker proved sound certifies it in the kernel. | Released as lean-certify v0.3.0. `docs/lean-certify.md`; the procedure as a Claude skill, `SKILL.md`. |
| `ProofTools.Audit` | Commands that audit a development: what axioms a declaration may depend on and where one enters, the same for a whole file or for whole libraries, an inductive family printed as inference figures, and a check for computed indices. | Carried in from lax-logic-in-lean, 2026-11-19. `ProofTools/Audit.lean`. |
| `ProofTools.Zipper` | The zipper of an indexed family of trees: paths, moves and their laws, stated once. Beside it, Huet's zipper for rose trees with labelled edges, and those trees as an instance of the family. | New, 2026-11-19; the rose trees added 2026-11-22. `ProofTools/Zipper.lean`, `ProofTools/Zipper/`; "The zipper" below. |
| `ProofTools.Explore` | A proof explorer for any calculus given as a type of judgments, a type of moves, and a step function proved sound: derivations and unfinished derivations as data, scripts and their `run`, trees of moves as certificates (rose trees of `ProofTools.Zipper`), the checkers of both as certifiers, one tactic (`apply_move`, with the query `apply_move where` that draws the attempt so far), a command to look at an attempt that is built (`#walk`, by typing motions or by clicking the ones it offers) and a tactic block for the same (`Walk d`), functions that change one at a position (`Cursor.replace`, and by it `rule`, `prune`, `graft`, `script`) and run a session of motions and changes (`Cursor.walk`), and tactics of the calculus built from tactics. | New, 2026-11-19. `docs/explore.md`. |
| The method | How the parts are used on one calculus, in five stages. | Draft: `docs/campaign.md`; the procedure as a Claude skill, `.claude/skills/calculus-campaign/`. |

Related, and kept elsewhere:

- **calculus-adoption**, a Claude skill in
  [lax-logic-in-lean](https://github.com/fairflow/lax-logic-in-lean)
  (`.claude/skills/calculus-adoption/`): the procedure for transcribing a
  published calculus and proving its theorems. It is the origin of the
  Adopt and Prove stages below, and of the audit commands.
- **prover-toolkit**, a folder of the same repository: a Python harness that
  drives a hosted prover on Lean `sorry`s, with a search over a project's
  declarations and an axiom check. It is independent of this repository,
  and has had little use so far.

## The zipper

Five files, all in the namespace `ProofTools.Zip`. The first is the zipper
of any indexed family, with the address of the focus in its type; the other
four are about one kind of tree, rose trees with labels on nodes and on
edges, and give it Huet's zipper (1997) as well.

| Module | Types | Moves, edits and the rest |
|---|---|---|
| `ProofTools.Zipper` | `Deriv I W D` (the crumbs of a family `W : I → Type`, and `plug`), `Deriv.Unplug` (a layer opened at a direction), `Deriv.Sibling` (the hole of an open layer moved one place), `Deriv.Path`, `Deriv.Zipper`, `Deriv.Pos` | Moves `up` (total), `down`, `descend`, `sibling` (up, then down), `left` and `right` (to the next sibling, in one step); edits `replace`, `modify`; `ofRoot`, `toRoot`, `addr`, `crumb` (the nearest crumb). |
| `ProofTools.Zipper.Rose` | `RTree κ α`, `Crumb κ α`, `Zipper κ α` | Moves `up`, `downAt i` (by position), `down k` (the first child along the edge `k`), `left`, `right`, `top`, `descend`, `goto`; edits at the focus `modify`, `replace`, `addChild`, `insertLeft`, `insertRight`, `delete`; `ofTree`, `toTree`, `addr`; lookups `find?`, `splitKey`, `RTree.get?`. |
| `ProofTools.Zipper.RoseIndexed` | `rtreeDeriv κ α`, `IPath κ α ra`, `IZipper κ α ra` | Rose trees as an instance of `ProofTools.Zipper`. `ofTree`, `up`, `down`, `descend`, `goto`, `toTree`, `left`, `right`, `replace` are the generic ones; `modify` (of the label); `forget` to a `Zipper κ α`, and `Zipper.index` back. |
| `ProofTools.Zipper.RoseUpdate` | | `RTree.updateAt g a` changes the subtree at an address; `RTree.at?`, `updFirst`. |
| `ProofTools.Zipper.RoseRender` | | `RTree.drawWith`, `Zipper.drawWith` (the focus marked), `RTree.map`; `BEq` on trees, and `Repr`. |

PROVED, by name; the statements are in the header of each file, and some
are shown here.

    z.down k = some z'  →  z'.up = some z                              (Zipper.up_down)
    goto t a = some z   →  z.addr = a ∧ z.toTree = t                   (Zipper.goto_addr)
    (goto t a).map focus = t.get? a                                    (Zipper.goto_focus)
    (IZipper.goto t a).map forget = Zipper.goto t a                    (IZipper.forget_goto)
    IZipper.goto t a = some z → z'.path.Canon → z'.toTree = t  →  z' = z
                                                                       (IZipper.goto_unique)
    ¬ a <+: b  →  (t.updateAt g a).at? b = t.at? b                     (RTree.at_updateAt_of_not_prefix)

- `ProofTools.Zipper`, in `Deriv.Zipper`: `toRoot_up`, `toRoot_replace`,
  `down_eq_some`, `up_down`, `toRoot_down`, `down_up`, `toRoot_descend`,
  `canon_down`, `canon_descend`, `eq_of_toRoot`, `descend_cons_of_down`,
  `descend_snoc`, `exists_descend_plug`, `descend_addr`; in `Deriv.Path`:
  `plug_inj`, and for `simp` `plug_top`, `plug_cons`. The nearest crumb:
  `path_eq_cons`. The one step to a sibling keeps the parent
  and the whole tree, its two directions undo each other, and it is
  `sibling` at the direction it reaches: `up_left`, `up_right`,
  `toRoot_left`, `toRoot_right`, `right_left`, `left_right`,
  `sibling_of_left`, `sibling_of_right`.
- `Rose`, in `Zipper`. A move keeps the whole tree: `toTree_up`,
  `toTree_downAt`, `toTree_down`, `toTree_left`, `toTree_right`,
  `toTree_descend`, `toTree_top`. The moves undo each other: `up_down`,
  `up_downAt`, `downAt_up`, `right_left`, `left_right`. The address of the
  focus: `addr_up`, `addr_down`, `addr_left`, `addr_right`, `addr_descend`,
  `goto_addr`. The focus is the subtree at the address: `focus_down`,
  `focus_descend`, `goto_focus`. Lists of children: `splitKey_spec`,
  `splitKey_find?`. For `simp`: `toTree_ofTree`, `toTree_cons`, `addr_cons`.
- `RoseIndexed`, in `IZipper`: `toTree_eq_plug`, `toTree_up`, `up_down`,
  `down_up`, `toTree_down`, `eq_of_toTree`, `canon_down`, `canon_descend`,
  `canon_goto`, `goto_unique`; from the generic laws of the one step and of
  `replace`: `toTree_left`, `toTree_right`, `right_left`, `left_right`,
  `toTree_replace`. Agreement with the plain zipper:
  `addr_forget`, `toTree_eq_forget`, `forget_up`, `forget_down`,
  `forget_descend`, `forget_goto`, `Zipper.forget_index`. Paths:
  `IPath.map_edge_toList`, `IPath.toList_ofList`, `IPath.plug_eq_foldl`,
  `IPath.plug_inj`. Lists of children: `splitKey_append`, `splitKey_plug`,
  `splitKey_left`. The three laws of `Deriv.Unplug` are the instance
  `rtreeUnplug`, the four of `Deriv.Sibling` the instance `rtreeSibling`.
- `RoseUpdate`: `RTree.get?_append`, `RTree.get?_updateAt_append`,
  `RTree.at_updateAt_of_not_prefix`, `find?_updFirst_self`,
  `find?_updFirst_ne`, `find?_append_new`.
- `RoseRender`: `RTree.beq_iff_eq`, `RTree.beqL_iff_eq`, and with them the
  instance of `LawfulBEq`.

Not stated: any law for the edits at the focus of `Rose`, and the agreement
of `RTree.updateAt` with `goto`, `replace` and `toTree` (the tests check it
on one tree). The explorer's attempts are an instance of `ProofTools.Zipper`
(`ProofTools/Explore/Zipper.lean`), not rose trees, and the motions of its
cursor are that zipper's moves: `up`, `down`, `left`, `right`, with the
laws read off the generic ones (`ProofTools/Explore/Motion.lean`), and its
one change at a position is that zipper's `replace`
(`ProofTools/Explore/Session.lean`). Its
trees of moves are rose trees (`Cert S := Zip.RTree Unit S.Move`,
`ProofTools/Explore/Cert.lean`).
Every file ends with the
bound `#axioms_within_file [propext, Quot.sound]`; the tests are
`ProofToolsTest/Zipper/Rose.lean`: every move and edit, on Huet's parse
tree and on a binary tree.

## The method in brief

Work on a calculus is one campaign. It starts from five questions, asked of
the literature before anything is written: what the rules are; what has
been proved about them; what should run, and why; how people use the
calculus; which calculi it is related to. Then:

| Stage | What is done | What the reviewer gets |
|---|---|---|
| Survey | The five questions, answered from the sources. | A plan: goals, and what is left out. |
| Adopt | The rules, transcribed as an inductive family; a first explorer. | The rules printed as figures beside the source, and derivations to type by hand. |
| Prove | The theorems of the plan, statements first. | Each statement, marked proved, refuted or open. |
| Run | Search and countermodel procedures, each certified. | Verdicts with certificates the kernel checks. |
| Explore | The explorer in full, with its guides. | A tutorial to work through. |

No stage is automatic. An operator (a person, or a language model working
with one) does the work, and a reviewer decides at the end of each stage.
What is trusted is small: Lean's kernel, and two checkers per calculus, each
with a theorem. `docs/campaign.md` has the detail.

The procedure is written out as a Claude skill, in
`.claude/skills/calculus-campaign/`: `SKILL.md`, a reference for each of
adopting, certifying and exploring, a list of pitfalls, and templates (the
plan, a stage's brief and report, the instance of the explorer, as
compiled). In a Claude Code session whose project is a checkout of this
repository it is the command

    /calculus-campaign <the calculus, named in words>

whose first act is one proposal to the reviewer (the source, the system,
the results aimed at), after which it stops for an answer. A campaign's
files go in a Lake package of their own under `examples/`.

## Using it

    [[require]]
    name = "proof-tools"
    git = "https://github.com/fairflow/proof-tools"
    rev = "<a tag or a commit>"

Then `import LeanCertify`, `import ProofTools.Audit` or
`import ProofTools.Explore`. A project that imports `LeanCertify` alone
does not build the rest.

Build with `lake build`; the tests with `lake build LeanCertifyTest
ProofToolsTest` (a few seconds each; the lints, gates and audit commands
are pinned by `#guard_msgs`, their failing cases included). Pinned at Lean
v4.31.0.

## Coming from lean-certify

Nothing in `LeanCertify` has changed, and its imports are the same. In the
project that requires it, the package's name becomes `proof-tools` (and the
address, when the pin is moved to a release of this repository):

    [[require]]
    name = "proof-tools"                               # was "lean-certify"
    git = "https://github.com/fairflow/proof-tools"    # was .../lean-certify
    rev = "…"

A project that keeps its own copy of the audit commands (`Meta/Audit.lean`
and its neighbours, as lax-logic-in-lean does) cannot import that copy and
`ProofTools.Audit` in one file, since both declare the same commands: drop
the copy when moving. The commands' names and syntax are unchanged; their
namespace is now `ProofTools.Audit`.

Versioning, the downstream check before every tag, the list of known
downstream modules and the release notes are in `docs/lean-certify.md`, and
go on applying to the whole package.

Licence: Apache-2.0 (see `LICENSE`).
