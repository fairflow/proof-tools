# Part (b): certifying what runs

Covers the Run stage. **The authority is the skill `lean-certify`**
(`SKILL.md` at the root of `proof-tools`): its six steps and its rules R1
to R11 hold here unchanged, and are not repeated; where that skill names
its reviewer, read "the reviewer". Its rule R10 (statements first) is
met here by displaying and screening the statements before their proofs
(`SKILL.md`, stage 3, step 1): nothing waits for an answer, and the
report that R10 speaks of is the closing page. Read the file in the
checkout (`SKILL.md`, stage 3). This part says only what a calculus
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
for each certifier" means: for each certifier of derivations that the
campaign uses, a certificate with a wrong move and one that stops early
(§5); and one for the certifier against what holds.

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
  State it as a function into the two subtypes of certificates,
  `(s) → { c // yes.check s c = true } ⊕ { r // no.check s r = true }`,
  and make the producer that function. A decision that returns the
  derivation as data is as large as the derivation, whatever the
  search does; the derivation is kept for the theorem about the calculus, which nothing
  runs. Where a second search is written because the proved one is
  slow, try its proof before building a fallback from one to the
  other.

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
  when it is made: an evaluator by closures does not end on four
  elements.
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

  Its soundness needs no model, and the syntactic proof is the first
  to try: an induction on a derivation without cut (the last rule of
  a member has a premise in the set), with cut elimination to reach
  the calculus with cut. The model is
  wanted only where the countermodel itself is. The induction is on
  the derivation and not on the set, so it does not ask that premises
  be smaller: a member may be its own premise, and members may ask for
  each other round a cycle. Where the rules keep their principal
  formula (a calculus on sets), take membership up to weakening: a
  premise need only be *below* a member, with the same conclusion and
  a larger context. Without it the set is exponential for a reason
  that is not the search's (`2ⁿ` members for `n` conjunctions on the
  left). Soundness then uses the
  height-preserving weakening of the calculus, and the list is the
  generators of the refutation: a theorem that the sequents below a
  closed list are closed in the strict sense, with its converse, keeps
  the definition and lets the checker use the short form. The worlds
  of the model of such a set are not its members but those with a
  maximal context among the members of the same conclusion; the truth
  lemma needs a maximal member above each member, which a list has by
  induction on the list.
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
- **A memo of failures is sound only where premises are smaller.** On a
  graph with cycles a failure can be provisional: a node met again
  while it is still being worked on. Search there by rounds. A failure
  is remembered for its round only; when a round adds no derivable
  node, its failures are final, and its fully tried nodes are the
  certificate (§3).
- Bound every generator of test inputs before running it (a size, a
  count, a deadline).

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
  the kernel running the search, and report both (§5): which is the
  cheaper differs by calculus and by side, and the kernel running the
  search may answer where a certificate is not elaborated;
- keep the certifiers all the same, for what the direct decision does
  not give: the proof as an object (a value of `Fam j` to print, walk
  and compare; a tree of moves to keep), and any producer that is not
  proved (a faster search, a person, a language model);
- the compiled producer is still that search, with its answer checked
  before it is handed on (above).

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
the first there has a fault in its code.

The fast search serves the "yes" side only: its tree is checked, and
the proof is had. For a judgment with no derivation the kernel must
then run the proved search, which may be the slow one (it tries each
formula as principal, and each division of a context). So where the
proved search is slow, the "no" side wants a certificate of its own
(§3): this is where a finite model property, or a saturated set, pays
in Run. Find out with the first measurements, on a family that is not
derivable, before the closing page (rule 6).

## 5. Statements, tests, measurements

**Statements first (R10).** `SKILL.md`, stage 3, step 1: the producers
recorded with why each is wanted, and each certifier of your own stated
and screened, before any producer is written.

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
- For one judgment typed at a shell: a command of the same executable,
  `<name>run prove '<judgment>'`. It is what a person with no Lean file
  open can use; what it has to do is the next paragraph.

**A judgment typed at a shell** (`prove`). Each calculus under
`calculi/` has one: `<Name>/Parse.lean` with the `prove` part of
`Main.lean`, a test file, and `Corpus/prove_corpus.py`. Read the one
nearest your calculus: Brünnler's K (a judgment that nests, a search
that always answers, a countermodel on the "no" side), GLS (a formula
or a two-sided sequent, two searches), MALL (one side, two searches run
together, two certificates on the "no" side), DILL (two zones, a
budget, flags that are real answers).

- *The reader.* It takes the signs of a keyboard as well as the signs
  the calculus prints (`-o` for ⊸, `[]` for □), and binds the
  connectives as the notations of the Lean file do (test it: the
  reader and Lean agree on texts with no parentheses). Where a sign is
  two things, whoever prints it (`[]` as □ and as an empty box; ⊥ as a
  unit and as the dual after a letter), say how they are told apart and
  guard each case. Say what an abbreviated or differently sided text
  is read as, and show the result in the first line: one formula with
  no turnstile; a two-sided text for a one-sided calculus. A text that
  is not a judgment is refused on the error stream, with nothing on the
  standard output: what was expected, and the place, counted from
  character 1, with a mark under it. The letters: `p q r s` and a
  numbered family, and let the refusal of a letter name them. The
  readers here differ in the family's letter and in its numbering, and
  a person who goes from one command to another meets the difference
  at once: the user's guide says the letters. Where the atoms of the formulas are words (a host library's),
  every word is a letter but for a list the reader keeps: the
  constants, and words refused with the sign to write. A letter that
  is a word of Lean, or a name of the file, is written out in the
  printed file, which declares its atoms in a namespace of its own.
  The misreading to test there is a constant's name read as a letter
  (`false`).
- *The printers, and two tests.* The first line shows the judgment in
  the calculus's notation; the fact is stated of the judgment as Lean
  source. So there are at least two printers (three with `--ascii`),
  and two directions to test for every entry of the corpus: the reader
  reads back what each printer writes; and Lean itself reads the
  Lean-source text as the judgment it was written from (`leanReads` in
  each test file). The second is not implied by the first. Where the
  reader computes (a negation that is a function, an implication that
  is defined), the first line shows the result and not the text typed:
  the user's guide says so, or it looks like a misreading. So does a
  member of a printed set whose hypotheses are in the order of the
  search's table, under a first line in the order typed.
- *What is printed.* The first line is a comment: the verdict
  (`derivable`, `not derivable`, `flag`) and the judgment as it was
  read. After it, a Lean file: the fact with its certificate through
  the campaign's certifiers, as declarations with names (an `example`
  cannot be audited), ending with the bound on axioms
  (`#axioms_within_file [propext, Quot.sound]`). The file writes both
  options that lift Lean's limits (`maxRecDepth` and `maxHeartbeats`,
  below), in every file: a threshold
  on the size of the answer looks at the wrong size. Do not print a
  certificate by `Repr`: it indents each line by its depth in the
  term, so the size of the text is the size of the term times its
  depth, most of it spaces. Write
  a printer, a node to a line; what guards a printer of one's own is
  that the files are elaborated. Count the spaces in a large file.
  Where a member of a printed set may be its own premise, or ask for a
  member that asks for it back, a comment above the set says that this
  is meant.
- *One kernel check, several facts.* Where one certificate gives
  several facts (a derivation as data and the proposition; not valid
  and not derivable), the check is a theorem of its own, stated through
  the certifier (`K.check s c = true := by decide +kernel`), and passed
  to each `verdict`: the default argument of `verdict` runs the check
  again for each fact. State the
  check as `K.check s c = true` and in no other form: where the type
  of the named check is not the same text as what `verdict` asks for,
  the elaborator computes the check itself to find the two equal,
  outside the kernel and once for each fact. Where even that costs,
  use the soundness lemma directly in place of `verdict`. A fact's
  import is paid by every
  answer: each printed file loads it. A second fact by a theorem of
  the library may be the statement people cite (derivability in
  natural deduction, by cut elimination). One through a heavier import
  (the model that a certificate with cycles presents) may stay a
  theorem about the certificate, and not a fact of the printed file.
- *More than one kind of answer for a verdict.* A side may have several
  certificates (a cyclic phase structure or a saturated set; a
  derivation as data or, beyond a cap, the proposition only). A comment
  in the file says which was used, and "one printed file of each kind"
  below counts kinds of certificate, not verdicts.
- *The program's own check.* The program prints only what it has
  checked, and that is the certifier's check, compiled. If the compiled
  check is slower than the kernel's on the same certificate, the
  checker's definition is at fault, and the kernel is hiding it: treat
  it as a defect and find it, do not work round it. The kernel keeps
  the terms it has reduced, and reduces only as far as a test looks;
  compiled code recomputes, and builds everything. So the two faults
  to look for are an evaluation that asks the same question again
  (`□A` at a world asks for `A` at every world below: `2ⁿ` calls for
  `n²` questions on a chain), and a replay that builds what it never
  reads (sequents that double at each step: gigabytes compiled and
  nothing in the kernel, a danger to the machine and not only a wait).
  The repairs: write the check as the algorithm one would run (a table
  over subformulas and worlds), proved sound, or prove it equal to the
  plain one and give it to compiled code by `@[csimp]` (the fast path
  of `lean-certify`); for a judgment that grows, check over a form
  that does not (sets for multisets), and cap the size of what a
  compiled check may build. A second check that is only tested against
  the certifier's is a stopgap: say so where it is used. Measure both
  sides on a family that grows before believing either, and on a
  second family made against whatever is thought to make it fast: a
  check that is fast in the kernel has not been shown to be a good
  algorithm. A proof of equality says nothing of cost, so a repaired
  check is measured as the faulty one was, compiled and in the kernel,
  and one size beyond. A deadline is not a cap on memory; and a timing
  taken inside compiled code is compared with the time of the whole
  process.
- *A check the kernel cannot run is a fault of the checker too.* "The
  kernel stops at `n`" is not a limit of the route until the
  definition has been cleared: the same fault is in the compiled
  check, where nobody runs it one size beyond the kernel's limit. The
  causes found so far: for each premise, a scan of the whole set; two
  sequents compared by counting every formula of both; the divisions
  of a context listed with repetition (`2ᵏ` for `k` copies of one
  formula, where there are `k + 1`); the principal formula looked for
  with the derived `DecidableEq`. How to find one, in the order that
  paid: time the parts of the printed file apart (the literal,
  membership, the check); `#print` each function on the path
  (`brecOn`, not `._unary`); run a copy of the check that counts its
  own operations (the count found in one run what the timings had
  not); then grow one thing at a time, and run the compiled check two
  sizes beyond where the kernel stops.
  What the kernel pays (Lean 4.31): two formulas it has not met,
  compared by the derived `DecidableEq`, 50 to 180 µs and 20 to 60 KB;
  a step of a recursion along a list, about 10 µs; an operation on
  numerals, a few µs whatever their size; a term met before, about
  3 µs. It keeps what it has reduced until the declaration ends, so
  memory follows work. A check written for the kernel therefore has
  few list steps and no comparison of formulas: a table of the
  formulas, each sequent a number whose digits are the multiplicities
  (in an odd base: a power of two cost ten times once the numbers
  passed 64 bits), a set as a search tree of the numbers; `bif` and
  `Nat.beq` where `if … == …` unfolds instances at every step. Where
  one theorem still passes the cap, state the check as several, one
  for each part of the set, joined by a proved lemma. The new check
  may be proved equal to the old one, or only sound for it at a
  certificate computed from the one given: that is enough, and a
  certificate it refuses is a flag. Measure each form before proving
  it, in a file with no proofs. The worked cases:
  `calculi/GLS/GLS/Table.lean`, `calculi/MALL/MALL/Coded.lean`,
  `calculi/DILL/DILL/SatFast.lean`.
- *A certificate beyond the kernel.* A search can print in
  milliseconds a certificate that Lean does not check within the
  memory cap. Find the largest size checked on every family tried (it
  is not a sharp bound: a larger set of one family may be checked
  where a smaller of another is not), and above it let the first
  line say what the answer rests on, in words that claim no more than
  was seen: "by the compiled check only (… ; the kernel has checked
  sets of up to <n>)". A verdict line that reads the same for a
  checked and an unchecked file claims more than was done. One measure
  of size may not separate the files checked from the others (the
  number of moves may not; the depth of nesting is then a second
  measure). Between the largest seen checked and the smallest seen to
  fail nothing is known: word that region as not checked. Measure the
  sizes on the file as it is finally printed, and again when its form
  changes: the largest tree checked grew by half when the certificate
  went from inside an `example` to a definition with the check a
  theorem of its own. Say on how many families each size was measured: "every
  family tried" may be one family. Where the certificate is a
  list of generators, its size is not the refutation's (`2ⁿ` members
  below a list of one or two): measure on a family whose generators
  grow, and give both figures.
- *The options.* `--short`: the first line only. `--ascii`: the
  judgment in that line with the signs of a keyboard. `--deadline=
  <seconds>` in every case, with a default, over the whole answer, so
  that the command ends by itself; `--budget=<n>` as well where a
  search has one. Try a family that grows before saying that the
  command ends: a search with no bound is found only so. Where
  the campaign has two searches, an option that asks the other one, so
  that its branch can be run on the corpus.
- *The exit codes*: 0 derivable, 1 not derivable, 3 flag, 2 a text not
  read. They are those of `Certify.Cli` (the end of
  `LeanCertify/Decider.lean`); its `main` needs a registry of tools
  that no campaign has, so only the numbers are taken.
- *What a flag is.* Where derivability is not decided, or the search is
  bounded: nothing found within the bound and no certificate that
  there is nothing. Where the search always answers: a search cut off
  at the deadline. Where derivability is decidable and the search is
  not proved to end, a third wording: "it has answered everything
  tried; the flags are those made at will". In each: a certificate
  that the program's check refused, and, where two searches run, both
  ended and disagreeing
  (defects; say whether each was ever seen, and give a flag that can be
  made at will if there is one). A flag prints no fact.
- *Run on the corpus, and beyond it.* The tests above are inside the
  library. The command itself is run on every entry: a command that
  lists the corpus as texts (`<name>run corpus`) and a script that
  compares each exit code with the recorded status and elaborates each
  printed file. The corpus may not reach every kind of answer: add
  members of the families (`<name>run families`) until each kind, and a
  flag, has been seen. Where the command can flag, a flag agrees with
  either status, so the script names the flagged entries and the
  measurements record the list. The script starts each command in a
  process group of its own and ends the group at its deadline
  (`os.killpg`; `subprocess.run(timeout=…)` ends `lake` and leaves
  `lean`). Report the counts by verdict and by kind of certificate, one
  printed file of each kind elaborated, and one of each kind altered
  and refused, the alteration chosen so that it cannot pass (a tree of
  moves altered at random may still be a derivation; a list of
  generators with its first member left out may still be closed, where
  the empty list in place of a list of one cannot pass, nor a list
  without a member that alone has its conclusion and that another
  member's rule instance needs). A text typed at a
  shell has a largest size, the operating system's limit on a command
  line: a family may end there, and no command yet reads its text from
  the standard input.

**The corpus.** Judgments of known status, with the status and its source:
the paper's examples, its non-theorems, a family that grows (to find where
time goes). Each run gives pass, fail or flag; every skip and every cap is
reported. There is no driver for this in the library: the same executable
serves, run under a deadline imposed from outside (the operating system's
`timeout`, where it has one: macOS does not, and the deadline of the
script that runs the cases serves), with a case that is cut off
reported as a flag. Where a status is cross-checked with another tool
that decides the logic: give that tool a deadline, read what it wrote
only if it ended, report a timeout as no verdict, and call no tool the
reference.

**Measure** (R8), and put the figures in `measurements.md`, with the machine and
the date, within the budget set before the first run (`SKILL.md`,
stage 3, step 3). A search is measured compiled, by the driver, under a
deadline, from the first run: `#eval` runs it in the interpreter, and a
sizing loop by `#eval` did not end in five minutes on inputs the
compiled driver settled in milliseconds. A long timing run goes in the
background, its output to a file. Every such run has a cap on memory
(`lake env lean -M <megabytes>`) as well as a deadline, and the deadline
ends the whole process group: ending `lake` leaves the `lean` process
under it running, with nothing to stop it.

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
  of `SKILL.md` says under what conditions and how it is recorded.

**A certificate written as a term has limits before the kernel.** R6 and
R8 of `lean-certify` speak of kernel time. A large certificate fails
earlier, while Lean reads the term: with the default options a tree of a
few thousand moves, or one nested a few hundred deep, is not elaborated
(Lean's error names its maximum recursion depth). So:

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
- two options move the limit, and a driver writes both before every
  fact: `set_option maxRecDepth 100000 in` and
  `set_option maxHeartbeats 0 in`. With the first alone a large tree
  stops at Lean's limit on heartbeats instead. So a frontier found
  with the default options is a frontier of those options, not of the
  route: say which it is, and find the route's with both lifted. The
  judgment itself, as a term, can meet the limit before its
  certificate does.

## 6. Deciders

`lean-certify` has deciders, with fallbacks and a command line (its
section "Deciders": `Certify.Prover.ofEngine` and
`Certify.Disprover.ofEngine` take the two sides of an engine, as
propositions). No campaign has used them: each wrote its own command
(§5), since the library's `main` needs a registry of tools. A decider is
a decision procedure only where level 3 is proved; otherwise it may
answer `flag`.
