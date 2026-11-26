# Part (b): certifying what runs

Covers the Run stage. **The authority is the skill `lean-certify`**
(`SKILL.md` at the root of `proof-tools`): its six steps and its rules R1
to R11 hold here unchanged, and are not repeated; where that skill names
its reviewer, read "the reviewer". Its rule R10 (statements first) is
met here by displaying and screening the statements before their proofs
(`SKILL.md`, stage 3, step 1): nothing waits for an answer, and the
report that R10 speaks of is the closing page. Read the file in the
checkout, not a skill of the same name from your session's list: that
may be a copy from another repository, and older. One that says its
reviewer "is the gate" is the older text, and the file in the checkout
holds. This part
says only what a calculus
brings to them: which of the six steps the explorer library has already
done for every calculus, and which are written by hand for each.

Two words. A **certifier** is a Boolean checker packed with its soundness
theorem (`Certify.Certifier`). **Splicing** is `lean-certify`'s word for
putting a certificate that a producer computed into a Lean term the kernel
checks. Names of Lean declarations (`step_sound`, `Fam`, `Derivable`,
`treeCert`, `scriptCert`) are those of `templates/Instance.lean.txt`.

Contents: 1 the six steps, for a calculus; 2 what is by hand; 3 the
refutation side and its levels; 4 the producer; 5 statements, tests and
measurements; 6 deciders.

## 1. The six steps, for a calculus

The pattern of `lean-certify`: the theory says what holds; an untrusted
producer computes a certificate; a checker proved sound certifies it in
the kernel. For a calculus given as a proof system `S` whose moves are
sound (`reference/explore.md` §2 to §4), with `T` what holds on the yes
side (the family `Fam` itself, or a proposition) and `P` a proposition
(`Derivable`, or `Valid`):

| step of `lean-certify` | the "yes" side: `T j` | the "no" side: `P j → False` |
|---|---|---|
| 1 theory: `Spec`, `Holds` | `Spec` is `S.Judg`; `Holds` is `T` | `Holds` is `fun j => P j → False` |
| 2 certificate | a **tree of moves**, `Cert S`, or a **script**, `Script S` (`reference/explore.md` §7) | a finite **model**, as data: yours to define |
| 3 checker and soundness | `Cert.check j c`, or `derives S j ls`. The soundness of either is given: from your `hS : S.SoundT T`, the map out of the derivation the certificate builds (`Der.ofCert`, `Der.ofScript`) | a Boolean check of a model against a judgment, with the theorem that what a model refutes does not hold: yours |
| packaged | `Cert.certifier hS : Certify.Certifier S.Judg (Cert S) T`, or `certifier hS : Certify.Certifier S.Judg (Script S) T` | a `Certify.Certifier S.Judg Model (fun j => P j → False)`: `LeanCertify`'s, as it stands |
| 4 producer | a search that returns a tree or a script: yours | a search that returns a model: yours |
| 5 splice | the term `treeCert.verdict j c : T j`, written by you or by a generator of yours (§5) | the certifier's `verdict j M : P j → False`, likewise |
| 6 kernel check | the default argument of `verdict`, `by decide +kernel`: the kernel checks the tree, or runs the script | the kernel evaluates the check |

So for the yes side the library has done steps 2 and 3 and gives the gate
of step 6. **What you write for it is the one-step checker `step` and the
soundness of the moves, once; then a producer; and the splice.**

```lean
import LeanCertify                             -- the lints; not imported by ProofTools.Explore

def treeCert := Cert.certifier step_sound      -- step_sound : S.SoundT Fam
def scriptCert := certifier step_sound
#certify_structural treeCert                   -- R3
#certify_statement treeCert                    -- R2
def d₀ : Fam j₀ := treeCert.verdict j₀ c₀      -- the kernel checks the tree
```

With the family into `Type`, `d₀` is a derivation of the calculus as the
source states it: the certificate is then one for the derivation itself,
and not only for there being one. For a proposition proved sound by
membership (`h : S.Sound P`), the certifiers are `Cert.certifier h.soundT`
and `certifier h.soundT`.

`import LeanCertify` brings the words of its syntax with it: `size`
becomes a keyword, and a function of yours with that name no longer
parses (`reference/explore.md` §5).

Compiled, in the template's instance: both lints pass on both certifiers,
with the property a type. For the script, R3 adds a note that the path
reaches `Nat.repr` (the library's message for a failing line), "so this
is not an error".

**Which certificate.** Every derivation has both: `d.cert` and `d.script`.
The default for the facts a campaign states and keeps is **the tree**:
the kernel checks it 1.3 to 6.2 times faster than the script of the same
derivation (the library's guide, "Which to use", with the command that
measures it), its check builds nothing, and it is compared and printed as
it stands. Take **the script** where the order of the work matters: a
proof to be continued or replayed line by line in the editor; a producer
built from the tactics of the calculus, which gives scripts
(`reference/explore.md` §8); an attempt with open goals, which has no
tree; and the yes side of the library's `engine` (§3), which is the
script certifier. A campaign may use both; the plan says which is the
certificate of record (Q3), and it is recorded with the plan.

**Which functions are "the checkers".** What you write and prove sound is
`step` (and the check of a model). `Cert.check` and `derives` are the
library's functions that run `step` over a tree and along a script; with
your theorem each is the checker of its certifier. So "a negative test
for each certifier" means: one for each certifier of derivations that the
campaign uses, and one for the certifier against what holds.

State a result with the named certifier (`treeCert.verdict j c`), not
through an engine (`E.yes.verdict j ls`): the second names the engine and
so, for Lean's count of axioms, its producer (R4).

## 2. What is written by hand for each calculus

| by hand | where it is used | trusted? |
|---|---|---|
| `Judg`, `Move`, `step` | everything | `step` is the one-step checker: yes, through its theorem |
| the soundness of the moves: `S.SoundT T`, or `S.Sound P` for a proposition | `Cert.certifier`, `certifier`, `Der.mapOut`, `Der.sound`, `engine` | it is the theorem (for a family into `Type`, a definition) |
| a type of models, the check of a model against a judgment, its soundness (optional) | the no side | the check yes, through its theorem |
| every producer: proof search, countermodel search | `engine`, deciders | no |
| completeness of one side or of the pair (optional) | level 3 | it is a theorem of the Prove stage |
| a certificate of your own, with its own checker (optional): what a search already holds, say | where a search's own data is the cheapest to check (§5) | yes, through its own soundness theorem |
| the splice: a file of facts, and the program that writes it | step 5 of `lean-certify` | no: the kernel checks each fact |

Step 5 of `lean-certify` also offers "a tactic that runs the producer at
elaboration time"; the library has no such tactic.

**Rules of `lean-certify` that are still yours to meet**, since nothing in
the explorer does them for you: R1 (`#certify_domain` on the producer); R4
(`#certify_axioms` on each stated fact; the list is
`Harness.config.axioms`, see "Axioms" in `SKILL.md`); R5 and R7 (flags
rerun at a raised budget, every run under a deadline, every skip
reported); R6 (a smaller certificate checks faster: shorten it before the
kernel sees it, if kernel time matters); R8 and R9 (§5).

`step` is on the path the kernel evaluates. So R3 applies to it:
structural recursion, no `partial`, no well-founded recursion, `Decidable`
instances that compute. And where the axiom policy excludes
`Classical.choice`, R4's list applies to it too, the messages it returns
included: build them from literals with `++`, and keep `String.splitOn`,
`length`, `toList` and the others R4 names out of `step`.
`#certify_structural treeCert` and the file's bound are the checks.

## 3. The refutation side, and its three levels

The refutation side is optional: not every calculus comes with a notion of
finite model, a decidable check of it, and a way to find one. An instance
stops where its mathematics stops.

| level | the instance has | it gets |
|---|---|---|
| 1 | moves and their soundness | `Cert.certifier hS`, `certifier hS`: trees and scripts checked |
| 2 | also a certifier against what holds: a notion of model with a sound check | `engine h no produce : Certify.Engine S.Judg (Script S) Model P`, from `h : S.Sound P`. Its producer may answer `flag`, and nothing says a model is ever found |
| 3 | also a theorem that one side always answers | `Certify.Engine.Complete`, or the instance's own statement, such as `(∃ c, Cert.check j c = true) ∨ (∃ M, no.check j M = true)` |

A certifier against what holds is `LeanCertify`'s, as it stands; the
explorer has no structure of its own for it. The library's example has
one (`noValid` in `ProofToolsTest/Explore/Calculus.lean`; its proof is
left out here):

```lean
def noValid : Certify.Certifier Seq (List Nat) (fun s => Valid s → False) where
  check s M := refutes M s          -- your Boolean check of a model
  sound s M h hs := …               -- what a model refutes does not hold
```

Bundled with a name and a producer it is a `Certify.Disprover`. The
engine takes a proposition: where what holds is a family into `Type`, the
proposition is `Derivable`, and its soundness by membership is
`step_sound.nonempty` (`step_sound_derivable`).

At level 1 there is no engine. The producer is then a plain function,
for instance `S.Judg → Nat → Option (Script S)`, and a result is stated
with the certifier alone. The library's example is at level 2 on purpose,
to show both sides; your level is the plan's.

**What each level asks of the Prove stage.**

- Level 1 asks nothing beyond the soundness of the moves.
- Level 2, with `Derivable`: the `sound` of the certifier against it
  needs the soundness of the calculus for its semantics (a derivable
  judgment is true in every model), then that a model the check accepts
  makes the judgment false. With `Valid`, the second half is all of it.
- Level 3 is a completeness theorem: a result of Q2, proved if it is a
  goal. Trust never needs it: without it the answer is sometimes `flag`,
  and never wrong.

**Where the countermodel comes from** is a question for the Survey (Q3),
because calculi differ. In some an unfinished derivation that can go no
further is a countermodel as it stands; in others the countermodel is
assembled from several failed attempts; in others there is no such
reading. The library assumes none of these: how a model is found is a
producer.

**A certificate against a derivation need not be a model that the
kernel evaluates.** Three forms have served, and an instance may have
more than one:

- *A model, evaluated*: a finite structure given as data, its
  interpretation computed by the check. The producer of structures is
  seldom complete. Where the kernel is to compute over a finite carrier,
  tabulate each set once, as a list of Booleans indexed by the carrier,
  when it is made: an evaluator by closures did not end in 120 s on
  four elements, and the tabulated one was linear in the families
  measured.
- *The record of a failed search*: a finite set of judgments, saturated
  (the judgment is a member; no member is an axiom; every rule instance
  concluding a member has a premise in the set). The check is
  syntactic. Where completeness is proved by a syntactical model (the
  model built from the judgments with no derivation), the same
  construction with the set as parameter gives the theorem that a
  saturated set presents a model refuting its members, and the theorem
  that the set of all small judgments with no derivation is saturated
  makes the certificate complete. The semantics is in the theorem, not
  in the check. Its size is the search's: measure it.
  `calculi/MALL/MALL/Saturated.lean` is the worked case.
- *No certificate*: where a search is proved and the kernel can run it
  (§4), a certifier whose certificate is `Unit` and whose check is the
  decision procedure is a certifier against what holds. An instance
  with a proved search and no written countermodel has an engine and
  level 3 by it.

**Where derivability is not decidable**, no sound certificate against a
derivation is complete, and level 3 is not a goal: the plan sets level
2, the producer answers `flag` at its budget, and completeness of
refutation is stated, if at all, for a fragment whose search space is
finite. Say which fragment in the plan, before the Run stage is
designed.

A calculus whose derivations are disproofs is a calculus, with its own
proof system and its own campaign. No instance has used one as the no
side of an engine.

## 4. The producer

`produce : S.Judg → Nat → Certify.Verdict (Script S) Model`, with
`Verdict` one of `pass c`, `fail r`, `flag`. Compiled, untrusted, free to
be `partial`. The number is a budget handed in at the call; when it runs
out the answer is `flag`, never `fail`.

- A search that builds a tree of moves hands over that tree (`Cert S`),
  for `Cert.certifier`. For an engine it gives the script of the
  derivation its tree checks to: `(Der.ofCert j c h).script`.
- The combinators on tactics of the calculus (`Tac.move`, `orElse`,
  `andThen`, `iterate`, `first`; `reference/explore.md` §8) are one way to
  write a producer, and come with a theorem: a script they give has no
  failing line. Whether it closes its goal is for `derives` to say. The
  library's example does this (`auto`, `produce` in
  `ProofToolsTest/Explore/Calculus.lean`).
- Check the producer's own certificate before passing it on, and answer
  `flag` if it does not check: a rejected certificate is a defect of the
  tool, never a verdict.
- **A termination bound that makes a proof easy is seldom runnable.** The
  search does not use it.
- Bound every generator of test inputs before running it (a size, a
  count, a deadline). One that ran away wrote oversized files for
  minutes before it was stopped.

**Where Prove left a search that is proved, and structural: try the
direct decision first.** `lean-certify` is built for a producer that is
not trusted. A campaign that reaches level 3 (§3) may have more than
that: a function `(j : Judg) → Fam j ⊕ Refutation j`, proved to end and
to be right, written by structural recursion (R3 asks the same of a
checker). Then what holds is decidable by evaluation, and the kernel
can run the search itself:

```lean
instance (j : Judg) : Decidable (Valid j) := validDecidable j
example : Valid j₀   := by decide +kernel
example : ¬ Valid j₁ := by decide +kernel
```

No certificate is written out, and no producer is in the statement.
Plain `decide` may stop where `decide +kernel` goes through, since it
does not unfold the search. So, in this case:

- measure both routes on the corpus, the fact with its certificate and
  the kernel running the search, and report both (§5). In the one
  instance measured (`calculi/BrunnlerK/` of `proof-tools`) the kernel
  running the search was the cheaper at every size tried for a proof
  (0.44 s against 1.81 s at a tree of 655 moves) and answered where
  the certificate was not elaborated; against validity the tree was
  the cheaper (0.07 s against 2.04 s at 65 nodes);
- keep the certifiers all the same, for what the direct decision does
  not give: the proof as an object (a value of `Fam j` to print, walk
  and compare; a tree of moves to keep), and any producer that is not
  proved (a faster search, a person, a language model);
- the compiled producer is still that search, with its answer checked
  before it is handed on (above): being proved does not excuse it from
  the check, which costs little and guards the file against its own
  defects.

Where the search is not structural (well-founded recursion, a budget),
the kernel does not run it: R3. This route is then closed, and the
certifier is the only one.

**A fast search that is not proved, beside the proved one.** A proved
search may be slow because of what it returns, not because of a fault:
a derivation whose sequents grow at every step. A second producer may
then answer a weaker question (that a derivation exists) by another
route (a search over sets, where the calculus is on multisets). It
needs no proof of its own. A certifier checks its answer, and a
decision of this form, in outline,

```text
if check j (fast j) then <the answer, by the certifier> else <the proved decision>
```

is a decision procedure that the kernel runs, and is right whatever
`fast` does. Say in the frontier which property each certifier
certifies. And before a second search is blamed on the calculus,
compare the two on a small member: a second search that is slower than
the first there has a fault in its code (one such was a helper that
called itself twice on each element).

The fast search serves the "yes" side only: its tree is checked, and
the proof is had. For a judgment with no derivation the kernel must
then run the proved search, which may be the slow one (it tries each
formula as principal, and each division of a context). So where the
proved search is slow, the "no" side wants a certificate of its own
(§3): this is where a finite model property, or a saturated set, pays
in Run. Find out with the first measurements, on a family that is not
derivable, before the closing page (rule 6).

## 5. Statements, tests, measurements

**Statements first (R10).** The library's two certifiers of derivations
and the certifier against what holds were fixed in the plan: what holds,
the certificate of record, the level, the notion of model. Before any
producer is written, record in `decisions.md` which producers, and why
(who relies on the answers); and for any certifier of your own, enter
`Holds`, the certificate, and the type of `sound` in `statements.md`,
displayed and screened.

**Negative tests (R9).** For each certifier, one corrupted certificate,
rejected in the kernel and pinned. For a tree and for a script, two each:
one with a wrong move, and one that stops early (`bad_tree_rejected`,
`short_tree_rejected` and the two for scripts, in the template). A gate
never watched failing does not count.

**From a producer's answer to a checked fact.** The producer is compiled
code; its certificate has to be written into a term.

- For a few facts, by hand: evaluate the producer (`#eval`), and paste the
  certificate as a literal into `treeCert.verdict j c` (or
  `scriptCert.verdict j ls`). A tree and a script print as Lean data
  where the moves have `Repr`. Print a script on one line (a wide
  format width): `Repr`'s output broken over several lines is not
  always Lean source.
- For many: a small executable of your own that runs the producer on each
  judgment and prints one line for each fact,
  `theorem fact_i : Derivable j_i := … .verdict j_i c_i`. Commit the
  generated file beside the program that wrote it (step 5 of
  `lean-certify`). The library has no such generator.

**The corpus.** Judgments of known status, with the status and its source:
the paper's examples, its non-theorems, a family that grows (to find where
time goes). Each run gives pass, fail or flag; every skip and every cap is
reported. There is no driver for this in the library: the same executable
serves, run under a deadline imposed from outside (the operating system's
`timeout`, where it has one: macOS does not, and the deadline of the
script that runs the cases serves), with a case that is cut off
reported as a flag.

**Measure** (R8), and put the figures in `measurements.md`, with the machine and
the date. A search is measured compiled, by the driver, under a
deadline, from the first run: `#eval` runs it in the interpreter, and a
sizing loop by `#eval` did not end in five minutes on inputs the
compiled driver settled in milliseconds. A long timing run goes in the
background, its output to a file.

- kernel time against the size of the certificate (Lean's profiler,
  `set_option profiler true`, reports the time of each declaration);
- the check of the certificate even where the producer is slow. The
  kernel is lazy and compiled code is not: a tree of moves whose
  sequents double at every step was checked in under a second, where
  the compiled search took more than 20 s to build the derivation;
- the tree against the script, on your own derivations: the library's
  figures (1.3 to 6.2 times, least where a step costs most) are for its
  example. Where a search has a certificate of its own, that too;
- the size of the search's proof against one made by hand, where both
  exist. A depth-first search that shares nothing between branches can
  produce a proof many times longer than the one a person writes; the
  checker accepts either, and the difference says what the search should
  learn. Where it can be taught in a few lines (a search that applied a
  branching rule before it looked for an axiom gave `2ⁿ⁺¹ − 1` rule
  instances where one serves), teach it in this stage: stage 3, step 4,
  of `SKILL.md` says under what conditions and how it is recorded;
- where there is a search that is proved and structural (§4): the kernel
  running the search, beside the fact with its certificate.

**A certificate written as a term has limits before the kernel.** R6 and
R8 of `lean-certify` speak of kernel time. A large certificate fails
earlier, while Lean reads the term: a tree of 2 335 moves, and one of
258 moves nested 256 deep, were not elaborated (Lean's error names its
maximum recursion depth), where a tree of 655 moves took 1.8 s and one
nested 64 deep 0.5 s. So:

- find this limit for your certificate with the family that grows,
  both in size and in depth of nesting, and name it in the frontier as
  what it is: a term that was not elaborated is a **flag**, not a
  rejection. A certificate the checker rejects is a defect of the
  tool; one too large to read is a limit of the route;
- say what a column of times measures. Parsing, elaboration and the
  kernel's check are one figure unless they are separated; call it
  "kernel" only if they are;
- `certify_chunks` does not help: it splits a long `List.all`, not a
  deep tree. What does: a smaller certificate (R6); the direct
  decision, where §4 allows it; or a certificate of your own that is
  flat (§2);
- raising `maxRecDepth` moves the limit: `set_option maxRecDepth
  100000 in` before a fact let a tree of 195 moves, nested about 130
  deep, be elaborated where Lean had stopped without it. A driver can
  write the option before every fact.

## 6. Deciders

When a command-line tool or several tools with fallbacks are wanted, read
the section "Deciders" of `lean-certify`: `Certify.Prover.ofEngine` and
`Certify.Disprover.ofEngine` take the two sides of an engine. They take a
proposition, so a family into `Type` is reached as `Derivable`. A decider
is a decision procedure only where level 3 is proved; otherwise it may
answer `flag`.
