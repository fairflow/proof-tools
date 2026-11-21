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
| `ProofTools.Zipper` | The zipper of an indexed family of trees: paths, moves and their laws, stated once. | New, 2026-11-19. `ProofTools/Zipper.lean`. |
| `ProofTools.Explore` | A proof explorer for any calculus given as a type of judgments, a type of moves, and a step function proved sound: derivations and unfinished derivations as data, scripts and their `run`, the two checkers as certifiers, one tactic (`apply_move`), a command to look at an attempt that is built (`#walk`, by typing motions or by clicking the ones it offers), and tactics of the calculus built from tactics. | New, 2026-11-19. `docs/explore.md`. |
| The method | How the parts are used on one calculus, in five stages. | Draft: `docs/campaign.md`. |

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
