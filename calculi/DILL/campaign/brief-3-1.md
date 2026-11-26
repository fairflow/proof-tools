# Brief: DILL, stage 3 (Run): two agents

Written 2026-11-26 15:28 GMT by the operator. Each agent reads the common
part and its own section.

The target and the rules of the project: `campaign/decisions.md`, the
first entry. The plan: `campaign/plan.md`, section "Q3" (the level aimed
at is 2: with `!` derivability is undecidable, so the producer answers
`flag` at its budget and no certificate against a derivation is
complete).

## Common part

The calculus is dual intuitionistic linear logic, sequents `Γ ⨾ Δ ⟹ C`,
in the lake package `calculi/DILL/` (Lean 4 core, v4.31.0; run every
command from that folder). Read: `DILL/Form.lean`, `DILL/System.lean`
(the family `Fam c`; `CF := Fam false`), `DILL/Perm.lean`,
`DILL/Proof.lean` (the moves, `step`, the proof system `S`, `step_sound :
S.SoundT (Fam true)`, `famToDer`), `DILL/Tactic.lean` (printers,
`sublists`). Then the method's text for this stage:
`../../.claude/skills/calculus-campaign/reference/certify.md` (all of
it), and the skill `lean-certify`, which is the file `SKILL.md` at the
root of this repository (`../../SKILL.md`): its six steps and rules R1 to
R11 hold. The same stage done for the neighbouring calculus is in
`../MALL/` and is the model to follow: the files your section names.

Rules of the work (as in `campaign/brief-2-1.md`, "Rules of the work",
which you should read: one writer per file; statements first; theory
files end with `#axioms_within_file [propext, Quot.sound]` and have no
`sorry`; helpers in your own namespace; `(!A)` and `(A ⊕ B)` in
parentheses; build by target only, never plain `lake build`; files on
disk early; no commit, no git command that changes anything; nothing
outside `calculi/DILL/`). Two more for this stage:

* **A pinned value is never typed from expectation**: evaluate, read the
  output, paste it. A time comes from a run, with the machine and the
  date (`date`); never an estimate.
* **A search is measured compiled, by a driver, under a deadline**, never
  by `#eval` in the interpreter; a measuring run goes in the background
  with its output in a file, and every generator of inputs is bounded
  (a size, a count, a deadline) before it is run. macOS has no
  `timeout`: the script that runs the cases imposes the deadline (as
  `../MALL/Corpus/measure.py` does).

Report (final message, at most 40 lines): files and line counts; what
builds; the statements proved, by name; negative tests; the figures
measured, with the frontier named (the smallest inputs not settled
within the budget); anything wrong or awkward found.

## G. The search and the "yes" side (namespace `DILL.Run`; files below)

Files: `DILL/Lazy.lean` (code: the producer), `DILL/Run.lean` (theory:
the certifiers), `DILL/RunTest.lean` (tests), `DILL/Corpus/Basic.lean`
(the corpus), `Main.lean` (the driver, an executable `dillrun`; the
operator adds it to the lakefile: say in your report the exact
`[[lean_exe]]` lines you need, and until then build it with
`lake env lean --run Main.lean` or ask nothing and compile with
`lake build` of a target you can name), `Corpus/measure.py`, and
`campaign/measurements.md` (the "yes" side; the template's shape is
`../MALL/campaign/measurements.md`). Models: `../MALL/MALL/Lazy.lean`,
`Run.lean`, `RunTest.lean`, `Corpus/Basic.lean`, `../MALL/Main.lean`,
`../MALL/Corpus/measure.py`.

1. `def treeCert : Certify.Certifier Seq (Cert S) (Fam true) :=
   Cert.certifier step_sound` and `scriptCert`, with
   `#certify_structural` and `#certify_statement` on each (if
   `DILL/Test.lean` of another agent already defines these names in
   `DILL.Test`, yours are in `DILL`, which is where they belong).
2. A producer `proveLazy : Seq → Nat → Option (Cert S)` (not trusted,
   may be `partial`): a search for a derivation without cut that returns
   a tree of moves. Design: the invertible rules first (⊸R, &R, ⊤R on
   the right; ⊗L, 1L, ⊕L, 0L, !L on the left; CCP Lemma 6), then the
   choices: init, 1R, !R, ⊕R₁, ⊕R₂, ⊗R, and on the left ⊸L, &L₁, &L₂,
   and copy. ⊗R and ⊸L divide the linear zone: do not enumerate the
   divisions; pass the whole zone to the first premise and give what it
   did not use to the second (input and output contexts, after Hodas and
   Miller 1994 and Cervesato, Hodas and Pfenning 2000; MALL's `Lazy.lean`
   has this for a one-sided calculus, with the care that a formula made
   inside a branch must be used inside it, and that ⊤ may take any
   rest). The moves `tensorR A B Δ` and `lolliL A B Δ` of the tree name
   the part actually used by the first premise. **copy is what makes the
   search endless**: the number is a budget on the uses of copy along a
   branch (or a fuel on the depth); when it is spent that branch fails,
   and the caller reads a failure at budget `n` as `flag`, not as "no".
   Check the tree with `Cert.check` before handing it on.
3. `Run.lean` also has `def produce : Seq → Nat → Certify.Verdict
   (Script S) Unit`-like producer for the yes side only (`pass` with the
   script of the checked tree, `flag` otherwise); the operator joins it
   to the "no" side in an engine afterwards, so leave the engine out.
4. The corpus (`Corpus/Basic.lean`): sequents of known status with the
   status and its source: the derivations of `DILL/Source.lean` if that
   file exists by then (another agent is writing it) and of the plan's
   Q4 (the laws of `!`: `!A ⟹ A`, `!A ⟹ !!A`, `!A ⟹ !A ⊗ !A`, `!A ⟹ 1`,
   `!(A & B)` and `!A ⊗ !B` each from the other, `!A, !(A ⊸ B) ⟹ !B`);
   the plan's "Known non-theorems"; and three families that grow: a
   chain `· ; a₀, a₀ ⊸ a₁, …, aₙ₋₁ ⊸ aₙ ⟹ aₙ`; the same with the
   implications in the unrestricted zone (`a₀ ⊸ a₁, … ; a₀ ⟹ aₙ`, which
   needs copy `n` times); a fan `· ; a₁, …, aₙ ⟹ a₁ ⊗ … ⊗ aₙ` with the
   zone reversed; and one family with no derivation (the chain with its
   last link missing).
5. `RunTest.lean`: for each of four or five corpus entries a fact
   `treeCert.verdict j c : Fam true j` with the tree pasted from the
   producer's output (R9: and negative tests: a tree with a wrong move
   and one that stops early, rejected by `decide`); `#certify_axioms` on
   a stated fact (R4).
6. Measure: the producer's time and the kernel's check of its tree
   against the size, on the three families, to the frontier; the
   budget at which each entry of the corpus is found; what is flagged.
   Write `campaign/measurements.md` with the machine and the date.

## H. Saturated sets: the "no" side (namespace `DILL.Sat`; files below)

Files: `DILL/Saturated.lean` (theory), `DILL/Refute.lean` (code: the
producer), `DILL/SatRun.lean` (theory: the certifier), `DILL/SatTest.lean`
(tests). Models: `../MALL/MALL/Saturated.lean` (its first 110 lines: the
check; the rest of that file builds a phase model, which is NOT wanted
here), `../MALL/MALL/Refute.lean` (its `search`, `witnesses`,
`refuteSet`; not its `Table`), `SatRun.lean`, `SatTest.lean`.

**The statements, fixed by the operator before any proof** (they are
entered in `campaign/statements.md` as S16). The certificate against a
derivation is a finite set of sequents, the record of a failed search:

    def refutedBy (D : List Seq) (j : Seq) : Bool
    theorem not_cf_of_refutedBy : ∀ (D : List Seq) (j : Seq), refutedBy D j = true → ¬ Nonempty (CF j)
    def noCFBySet : Certify.Certifier Seq (List Seq) (fun j => Nonempty (CF j) → False)

`refutedBy D j` is: `j` is a member of `D`, and `D` is saturated. A
member is counted up to a permutation of its linear zone and up to the
members of its unrestricted zone (the same conclusion; `permB` on the
linear zones; each unrestricted zone inside the other). `D` is
**saturated** when for every member `k`:

* `k` is no instance of a rule with no premise: not init (`k.lin` is not
  exactly `[k.goal]`), not 1R (not: goal `1` and empty linear zone), not
  ⊤R (the goal is not `⊤`), not 0L (`0` is not in the linear zone);
* for every instance of a rule of `CF` with conclusion `k`, one of its
  premises is a member of `D`: for each `A` in `k.unr`, the premise of
  copy; by the shape of the goal: ⊸R its premise; &R one of its two;
  ⊕R₁ and ⊕R₂ both premises (each is a rule of its own); !R, where the
  linear zone is empty, its premise; ⊗R, for every division of the
  linear zone into two, one of the two premises; and for each formula of
  the linear zone with the rest: ⊗L, 1L, !L its premise; ⊕L one of its
  two; &L₁ and &L₂ both; ⊸L, for every division of the rest, one of the
  two premises.

The soundness proof needs no semantics and no cut: by induction on a
derivation without cut of a sequent equivalent to a member, the last
rule is an instance at the member, one of its premises is in `D` up to
the equivalence, and the induction hypothesis applies to it. (So here
the check is syntactic and so is its theorem; MALL's went through a
model.) What it costs: with a non-empty unrestricted zone the premise of
copy is always asked for, and it is larger, so a finite saturated set
exists only for sequents whose search never reaches !L and that start
from an empty unrestricted zone. Say so in the file's header: the
certifier is for those, and the producer answers nothing for the rest.

Then: `DILL/Refute.lean`, a producer `refuteSet : Seq → Option (List
Seq)` (not trusted): a search that remembers every sequent it settles
and returns those it said "no" of, checked with `refutedBy` before it is
handed on; it returns `none` at once where the unrestricted zone is not
empty or !L would be reached. `DILL/SatRun.lean`: `noCFBySet`, with
`#certify_structural` and `#certify_statement`; and, **if**
`DILL/Cut.lean` exists and `lake build DILL.Cut` passes when you get
there (another agent is writing it; it gives `cutElimination : (j : Seq)
→ Fam true j → CF j`), also

    def noDerivableBySet : Certify.Certifier Seq (List Seq) (fun j => Derivable j → False)

in the same file, importing `DILL.Cut`; otherwise leave it out and say
so (the operator then adds it). `DILL/SatTest.lean`: for the plan's
known non-theorems with an empty unrestricted zone and no `!` on the
left, a fact by `noCFBySet.verdict j D` with `D` pasted from the
producer; one with `!` on the right (`· ; a ⟹ !a`); and at least five
negative tests in the kernel (a set with a member missing, a set that
contains an axiom, a set with a derivable member, the judgment not a
member, a set where one ⊗R division is not covered), each
`refutedBy … = false` by `decide`. Measure with a compiled driver of
your own (a few lines; do not write `Main.lean`, agent G does: put yours
in `Corpus/SatMain.lean` and run it with `lake env lean --run
Corpus/SatMain.lean`): the size of the set and the kernel's time to
check it, on the family `· ; a₀, a₀ ⊸ a₁, …, aₙ₋₂ ⊸ aₙ₋₁ ⟹ aₙ` (the
chain with its last link missing) to the frontier; write the figures to
`campaign/measurements-sat.md`.
