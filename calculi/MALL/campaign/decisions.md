# MALL: the decisions

One entry for each choice the operator made, in order, and one for each
word of the reviewer. Written when the choice is made, not afterwards.
The closing page lists the entries by what they cost to reverse, the
costliest first.

The cost to reverse is one of:

* **little**: a name, a letter, the place of a file;
* **a stage**: the form of a goal, an encoding, which results are goals;
* **the campaign**: the source, the system, what "holds" means, the
  axiom policy.

## 2026-11-26 09:46 GMT. The target

*The first entry, and the one record of what it fixes: the other files of
the folder point here.*

* **The command's words**: "Propositional multiplicative-additive linear
  logic, MALL, in Girard's one-sided sequent calculus with cut;
  campaign folder calculi/MALL/". They reached the operator in a task
  written by another session of the reviewer's (the session that
  proposed the round: MALL, then dual intuitionistic linear logic, then
  focusing or Benton's LNL), which gave the calculus in more words:
  "Connectives ⊗, ⅋, 1, ⊥, &, ⊕, ⊤, 0; formulas in negation normal form
  over atoms `p` and `p⊥`, negation a defined function. Rules: axiom
  `⊢ A, A⊥`, cut, ⊗ (splits the context), ⅋, 1, ⊥, &, ⊕₁, ⊕₂, ⊤ (no
  rule for 0). Primary source: J.-Y. Girard, 'Linear logic',
  Theoretical Computer Science 50 (1987)." The same task lists seven
  "points known in advance", each to be decided by the operator and
  recorded; they are entered below where they arise. The skill was run
  as a command (the Skill tool), with the words above as its argument.
* **The paper and its version**: J.-Y. Girard, *Linear logic*,
  Theoretical Computer Science 50 (1987) 1-102, North-Holland. The
  journal article is the only version: there is no preprint or thesis
  of it. Read as a scan of the journal pages (below). The system is in
  Section 1, "The phase semantics", pp. 17-24: Definitions 1.1-1.3
  (phase spaces, duals, facts), 1.7, 1.8, 1.11 (the connectives on
  facts), the syntax on p. 21, Definition 1.14 (phase structures,
  validity), Definition 1.15 (the sequent calculus, p. 22),
  Proposition 1.16 (soundness), Theorem 1.17 (completeness).
  Not taken, a line each:
  - J.-Y. Girard, *Linear logic: its syntax and semantics* (in
    *Advances in Linear Logic*, 1995): a later survey by the same
    author, with the same rules; the command names the 1987 paper;
  - Girard, Lafont and Taylor, *Proofs and Types* (1989), appendix B: a
    summary;
  - A. S. Troelstra, *Lectures on Linear Logic* (1992): a textbook, two
    sided;
  - Lincoln, Mitchell, Scedrov and Shankar (1992): another
    presentation (one-sided, with literals in pairs, by the agent's
    reading of its p. 243), read here for decidability and for cut
    elimination on sequents, not for the rules.
  Could not be got: none of those the campaign reads.
* **The system**: the propositional fragment without exponentials of
  the "linear sequent calculus" of Definition 1.15, as Girard states it
  on p. 22, before the modalities are added (Definition 1.21) and
  before the quantifiers. Girard gives this fragment no name of its
  own ("the propositional framework of linear logic", p. 21); the
  literature calls it MALL, and so does this campaign. Its rules:
  logical axioms, cut, exchange, the additive rules (⊤, &, 1⊕, 2⊕; "no
  rule for 0"), the multiplicative rules (1, ⊥, ⊗, ⅋). Left out: the
  exponentials `!`, `?` and their four rules (Definition 1.21), the
  quantifiers, the proof nets of Section 2 (PN1, PN2), the coherent
  semantics.
* **The results aimed at**: of the standing list, cut elimination and
  the finite model property (the second as a stretch goal, by the
  task's words: "attempt them only after the rest stands"); the
  source's soundness (1.16) and completeness (1.17) for phase
  semantics; and what the task mentions: exchange, with where it
  lives; weakening and contraction REFUTED, each by a concrete pair of
  sequents; decidability, by a decision procedure proved correct; a
  search by lazy splitting as the untrusted producer. The Survey makes
  the list exact (`plan.md`, Q2).
* **The path**: adopted from the paper.
* **The place and the name**: `calculi/MALL/` of `proof-tools`, a Lake
  package of its own (`mall`, library `MALL`), core Lean only, the
  toolchain of the library (`leanprover/lean4:v4.31.0`).
* **The library**: this checkout of `fairflow/proof-tools`, a worktree
  on the branch `claude/ecstatic-benz-bee260`, at commit `906e2fa`;
  the remote's `main` is at `906e2fa` (`git ls-remote`, 2026-11-26
  09:46): the same commit, nothing to update. It has
  `ProofTools/Explore/Cert.lean` and `ProofTools/Explore/Session.lean`.
  The build was seeded by an APFS clone of the main checkout's `.lake`
  (the reviewer's standing rule for Lean worktrees).
* **The source's files** (public; fetched without asking, by the
  skill's "Downloading"; each in a folder of its own in the session's
  scratchpad, nothing run from them; none is committed):
  - `linear.pdf`, from `https://girard.perso.math.cnrs.fr/linear.pdf`
    (the author's page), 5 240 273 bytes, 102 pages, a scan of the
    journal issue with its cover (so the paper's page *n* is the
    file's page *n* + 1), no text layer; sha256 begins
    `7892034966d7b9bc`. Not LaTeX, so not compiled: the skeleton is
    written by hand from the printed numbers. Read as page images: the
    contents, pp. 1-7 (Parts I, II), pp. 17-26 (Section 1 to the
    exponential rules), pp. 40-44 (the cut rule and cut elimination
    for proof nets). Not read: Parts III-IV after p. 7, Sections 2
    (but for pp. 40-44) to 6, Part V.
  - the other works (Lafont 1997; Lincoln, Mitchell, Scedrov and
    Shankar 1992; Okada 1999; Hodas and Miller 1994; Cervesato, Hodas
    and Pfenning 2000) and the mechanisations (Yalla, cslib): fetched
    by an agent of the operator; each file is entered in the next
    entry, when its report is in.
* **Pushing**: by the reviewer's standing instructions and the task's:
  commits go to `main`, pushed only as
  `git push origin HEAD:refs/heads/main` after `git branch -vv`; the
  branch `claude/ecstatic-benz-bee260` is never pushed.
* **Not touched**: every tracked file outside `calculi/MALL/` (rule 7
  of the skill). Only the reviewer contacts the authors of the sources.
* **Told to the reviewer**: 2026-11-26, in the session's output, when
  this entry was committed: "MALL campaign begun. Source: Girard,
  *Linear logic*, TCS 50 (1987), Section 1 (Definition 1.15, p. 22),
  read from the author's scan. System: the propositional fragment
  without exponentials, with cut and Girard's exchange rule. Aimed at:
  soundness and completeness for phase semantics (1.16, 1.17), cut
  elimination, exchange, weakening and contraction refuted,
  decidability, a search by lazy splitting; the finite model property
  as a stretch. Place: `calculi/MALL/`."
* **Before this text was read**: nothing. After the skill's text and
  its four reference parts were read, and before this entry was
  written (it was written at 09:56 from notes), the session had: read
  the source's pages listed above; started the agent that fetches the
  other sources; and run three scratch screens of the encoding (stage
  0, step 3), which the plan reports.

## 2026-11-26 10:03 GMT. Stage 0: the other sources' files

Fetched by an agent of the operator (public material; `SKILL.md`,
"Downloading"), each into a folder of its own in the session's
scratchpad; nothing run from them; none committed. The agent's report is
[survey-report.md](survey-report.md).

| file | from | size | what it is |
|---|---|---|---|
| `lafont/model.ps`, converted to `fmp.pdf` | `https://www.i2m.univ-amu.fr/perso/yves.lafont/pub/model.ps` (the author's page) | 99 405 bytes; the PDF 138 260 bytes, 6 pages | Lafont 1997, the author's version: 6 pages against the journal's 7, not compared with the published text. **Cited by this file's page numbers** |
| `lmss/lmss.pdf` | `https://curien.galene.org/ECI2023/Lincoln%2B-decision-LL.pdf` | 5 200 610 bytes, 73 pages | LMSS 1992, a scan of the journal pages 239-311 with an OCR layer |
| `lmss/lmss-sri-tr.pdf` | `https://www.csl.sri.com/papers/lmss90/lmss90.pdf` | 562 323 bytes, 89 pages | the SRI version (dated 13 Sept 1994); numbering not compared with the journal's; not cited |
| `hodas-miller/hm.pdf` | `https://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/ic94.pdf` | 272 565 bytes, 32 pages | Hodas and Miller 1994, an author's copy |
| `chp/chp.pdf` | `https://www.cs.cmu.edu/~fp/papers/erm97.pdf` | 317 841 bytes, 26 pages | Cervesato, Hodas and Pfenning, the preprint of 29 Aug 1997 of the TCS 2000 paper |
| `okada/kurims-1023-4.pdf` | (the agent's report) | 1 646 962 bytes, 19 pages | a different paper (Okada and Terui, RIMS Kokyuroku 1023); not used |
| clones of Yalla (`a138437`), cslib (`907f934`), and single files of five other mechanisations | GitHub | | read, not run, not imported |

**Not obtained**: M. Okada, TCS 227 (1999): ScienceDirect and CORE
refused the download. Not needed: Lafont's Lemma 1 states and proves
the argument, and attributes it.

* **Cost to reverse**: little. Lafont's theorem numbers are those of
  the author's version; if the journal's differ, the citations change.

## 2026-11-26 10:03 GMT. Stage 0: sequents are lists read as multisets; exchange is in the rule format

* **Decided**: a sequent is a `List Form`. Every rule of the family
  concludes a variable `Ξ` under a hypothesis that `Ξ` is a permutation
  of the rule's conclusion as the figure writes it
  (`Ξ.Perm (A ⅋ B :: Γ)`); the ⊗ rule and cut write the split there
  (`Ξ.Perm (A ⊗ B :: (Γ ++ Δ))`). Girard's rule EXCH has no constructor
  in `Fam`: it is a theorem, with the height kept. A second family,
  `Lit`, has the figure as it stands (a constructor EXCH, each rule at
  the head), and is proved equivalent to `Fam`.
* **Not taken**: the figure's form as the working family (every proof
  by hand would be mostly exchanges, and each theorem would be stated
  up to permutation anyway); membership with `erase` in the premises,
  as in GLS (the split of ⊗ still needs a permutation, and exchange
  then needs an induction); a Boolean mask for the split (a mask says
  which, not what: unreadable in a move); a quotient type (no
  `Lean.ToExpr`, no matching).
* **Why**: the source itself names the form ("pedantically, in the
  variant without exchange, adapted to multisets of formulas", p. 24),
  and Lafont's calculus is that form. Screened in scratch on five rules
  (`plan.md`, "Choices of encoding").
* **Rests on it**: every file. The answer to the task's first two
  points: the split is a permutation hypothesis on a variable
  conclusion; exchange lives in the rule format, and is also a proved
  lemma with heights.
* **Cost to reverse**: a stage (Adopt, and every proof after it).
* **For phase 2** (dual intuitionistic linear logic): this carries
  over to the linear zone as it stands. The intuitionistic zone wants
  the other form, membership, which builds weakening in, as in GLS.

## 2026-11-26 10:03 GMT. Stage 0: two families, into `Type`; what holds is the family

* **Decided**: `Fam` is Definition 1.15 with cut; `CF` is the same
  without the cut rule. Both into `Type`. What holds, for the explorer
  and the certifiers, is `Fam` (the skill's default); the proposition
  is `Derivable Γ := Nonempty (Fam Γ)`.
* **Not taken**: one family with a Boolean that allows cut (it puts a
  parameter the source has not into the family the rule table is
  checked against); a predicate "has no cut" on derivations of `Fam`
  (every proof about cut-free derivations would carry it through every
  case); validity as what holds (the moves' soundness would then say
  nothing about the rules).
* **Rests on it**: the rule table (rows for both), goals 2, 5, 7.
* **Cost to reverse**: what holds, the campaign; two families against
  one, a stage.

## 2026-11-26 10:03 GMT. Stage 0: what "valid" means

* **Decided**: `Valid Γ` is: for every phase structure `S` (Definition
  1.14; its monoid a type in `Type`), the unit is in the
  interpretation of the par of the formulas of `Γ`, and of ⊥ when `Γ`
  is empty (the reading in the proof of 1.16). The interpretation of a
  formula is U2 of the plan. Stated directly, over all phase
  structures, sets of phases being predicates.
* **Not taken**: a restriction to two-valued structures
  (`reference/adopt.md` §5): the source's proofs of 1.16 and 1.17 use
  no excluded middle that the operator can see, and the planned proofs
  are constructive; if a proof turns out to need it, this entry is
  reopened. Universe-polymorphic structures: soundness would be
  stronger and completeness the same; not needed by any goal.
* **Why, and the screen**: `plan.md`, "Screened": 21 sequents over the
  cyclic groups of order at most 4.
* **Rests on it**: goals 1, 2, 7, 11.
* **Cost to reverse**: the campaign.

## 2026-11-26 10:03 GMT. Stage 0: the axiom policy, and its first cost

* **Decided**: every theory file within `[propext, Quot.sound]`.
* **Its cost, found in scratch**: core Lean's instance that decides
  `List.Perm`, and its lemmas `perm_cons_erase`, `Perm.erase`,
  `cons_perm_iff_perm_erase`, use `Classical.choice` on v4.31.0. The
  campaign writes its own (a file `Perm.lean`: permutations by
  counting, after `calculi/GLS/GLS/Structural.lean`).
* **Cost to reverse**: the campaign (to tighten); little (to loosen).

## 2026-11-26 10:03 GMT. Stage 0: which results are goals

* **Decided**: the eleven goals of `plan.md`, in its order. By rule:
  soundness, completeness, cut elimination, the finite model property.
  Decided by the operator: exchange with heights; identity expansion;
  the inversions of ⅋, ⊥, &; decidability; weakening and contraction
  REFUTED; the disjunction property for ⊕ (no source read for it); the
  subformula property.
* **Not goals**: PSPACE-completeness; proof nets and their
  normalisation and confluence (standing entries 4 and 5: they hold of
  the logic, for another system); the semantic equations as statements
  about facts.
* **The form of cut elimination**: a function `Fam Γ → CF Γ`, by
  structural recursion on a bound of the size of the cut formula and
  then on the derivations. The task expected "size of the cut formula,
  then heights": since no rule duplicates a derivation, the two
  derivations themselves serve, and no sum of heights is needed. The
  semantic route (Lafont's Theorem 1) is a second proof, of the
  proposition.
* **Cost to reverse**: a stage.

## 2026-11-26 10:13 GMT. Stage 1: what a constructor and a move carry

* **Decided**: (a) every constructor of `Fam` and `CF` takes its
  principal formulas and its contexts as explicit arguments
  (`.par A B Γ h d`); (b) a move names its principal formula
  (`par A B`), and the two rules that split, ⊗ and cut, also name the
  context of the first premise as a list (`tensor A B [Γ]`), the rest
  going to the second; (c) the rule **1** has the same form as the
  others (`Ξ ~ [𝟏]`), though `Fam [𝟏]` would do; (d) the connective
  "with" is `wth` in every name (D6 of the rule table); (e) the
  source's `⊕` is kept as the notation, with parentheses where core
  Lean's `⊕` for sum types would take over.
* **Not taken**: (a) implicit arguments (Lean cannot infer them from a
  variable conclusion: tried in scratch); (b) both contexts in a ⊗
  move (the second is computed), a Boolean mask (unreadable), a split
  by position (the sequent has no order); (c) `one : Fam [𝟏]`
  (exchange would then need a cast in one case); (e) another glyph
  for ⊕ (the page would no longer read as the source does).
* **Rests on it**: the proof system, the tests, the exercises, every
  certificate.
* **Cost to reverse**: (a), (c) a stage; the rest little.

## 2026-11-26 10:13 GMT. Stage 1: the derivations of the first check

* **Decided**: since the source draws no derivation of the fragment,
  ten derivations of what it asserts stand in (`MALL/Source.lean`;
  listed in `rule-table.md`, "The checks").
* **Cost to reverse**: little.

## 2026-11-26 10:21 GMT. Stage 2: two goals handed to agents

* **Decided** (rule 5 of the skill): cut elimination as a function
  (`MALL/Cut.lean`, `MALL/CutTest.lean`) and the decision procedure
  (`MALL/Decide.lean`, `MALL/DecideTest.lean`) were each written by a
  fresh agent of the operator, from a brief given in the session: the
  statements as the named types of `MALL/Statements.lean`, the files
  to write and no others, the axiom bound, the tests the result must
  pass. The briefs are not kept as files; their terms are these. The
  operator kept the files out of its commits until each agent
  reported, then built them itself, read the definitions, and checked
  that no `sorry`, `partial`, well-founded recursion or
  `native_decide` is in them. One change was made to an agent's file:
  its function `step` was renamed `searchStep`, since the proof
  system's `step` has that name.
* **The route of the cut**: the operator's brief proposed a structure
  of handlers with equations; the agent replaced it by an inductive
  family `Prin C Γ` ("a last rule that introduces `C` in the context
  `Γ`"), on which a dependent match discards the impossible pairs. The
  measure is as the plan decided.
* **Cost to reverse**: a stage.

## 2026-11-26 10:25 GMT. Stage 2: completeness is stated without cut; the finite model by a simpler bound

* **Decided**: (a) `Completeness` concludes a derivation without cut
  (Lafont's Theorem 1), which is stronger than the source's 1.17 and
  gives cut elimination as a proposition; (b) Okada's lemma is proved
  once, for any phase space with a phase for each formula whose
  antiphases are closed under the rules, and the syntactical model is
  built once, for any congruence on sequents; (c) in the finite model,
  Lafont's order `⊑` ("the least preorder such that …") is replaced by
  *small*: the formulas are subformulas of formulas of the sequent,
  and the size is at most its size.
* **Not taken**: (a) Girard's own proof, S(A) = Pr(A), which uses cut
  and gives less; (c) Lafont's `⊑` as an inductive relation: it would
  need its finiteness proved, where *small* is decidable and its
  finiteness is a list of lists.
* **Why (c) is the same theorem**: the argument uses three properties
  of "below" (the premises of a rule with a conclusion below are
  below; a part of a sequent below is below; finitely many are below),
  and *small* has them (`Small.sub₁`, `Small.par`, `Small.left`,
  `finiteModel_finite`). The model is larger than Lafont's.
* **Cost to reverse**: (c) little; (a), (b) a stage.

## 2026-11-26 10:27 GMT. Stage 2: the reading back, and what it changed

* **Run** by a fresh agent on an extract of 230 lines; its report is
  entered statement by statement in `statements.md`.
* **Changed**: `sat_perm` and `valid_perm` were added, since the
  reader noted that validity is written through an order-dependent
  formula. Nothing else.
* **Kept as it is, with the reader's remark recorded**: S9 (exchange
  keeps the height) is trivial by the encoding; the goals that are
  data have types that do not say which function; `Decidable` is
  inhabited classically for any proposition.

## 2026-11-26 10:40 GMT. Stage 3: the producers and the certificates

* **Decided**: (a) two producers of trees of moves: the proved search
  with every split tried, and a search by lazy splitting that is not
  proved (`MALL/Lazy.lean`: input and output contexts, a flag for ⊤,
  the tree built last as a function of what a ⊤ takes back). What
  either returns is checked before it is handed on; (b) the
  certificate of record for a derivation is the tree of moves, whose
  ⊗ and cut moves name the split; (c) against derivability there is
  no certificate: `noDerivable` has the decision procedure for its
  check, so the kernel runs the proved search; (d) the lazy search
  first looks for the logical axiom at any formula, then the rule of
  the chosen formula, then each formula of the context as the
  principal one.
* **Not built, and it was in the plan** (Q3, (iii)): a certifier of
  finite phase structures against a sequent (a table for the monoid,
  lists for the antiphases and the facts, a Boolean check proved
  sound). The finite model property is PROVED (S17), so such a
  structure exists for every sequent that is not derivable; but
  nothing here writes one down and checks it in the kernel.
  `MALL/Screen.lean` has an evaluator over small cyclic groups that is
  not proved. **Why not**: it is not needed for a verdict (the
  decision is proved), and the closing page comes first (rule 6). **What
  it would buy** is in `measurements.md`, "the frontier": a negative
  answer for a sequent too large for the kernel to run the search on.
* **Not repaired**: the proved search tries each formula as principal
  and each split, with no order among the rules, and is exponential on
  the families (`measurements.md`). A repair that keeps the statement
  would need its completeness proved again; it is left as it is, and
  the lazy search is the fast producer beside it
  (`reference/certify.md` §4).
* **Cost to reverse**: little.

## 2026-11-26 10:56 GMT. Stage 3: finite phase structures as certificates, built after all

* **Decided**: the certifier that the entry of 10:40 left out is built
  (`MALL/Model.lean`, `MALL/ModelRun.lean`, `MALL/ModelTest.lean`),
  because the first measurements showed what it buys: on `chainBad`
  neither search answers at 12 formulas within 20 s. A certificate is
  a phase structure on a cyclic group ℤ/(k+1), as data: the antiphases
  and a set for each letter, as lists of Booleans. The letter's fact
  is the closure of its set, so that every certificate is a phase
  structure and the check has no side condition. The check computes
  the interpretation; `ZModel.interp_eq` proves that it is the
  interpretation in the structure.
* **Not taken**: a multiplication table for an arbitrary finite
  commutative monoid (the check would have to verify the laws; no
  sequent of the corpus needs more than a cyclic group of order 3);
  the structure of the finite model property's proof as a certificate
  (its phases are all small sequents: far too many to write).
* **The producer** (`refuteBy`) is small on purpose, and not complete:
  `measurements.md`, "The frontier".
* **It was built before the closing page was written**, while the
  measuring run occupied the machine: rule 6 of the skill puts the page
  first. It delayed the page by about a quarter of an hour (10:43 to
  10:56).
* **Rests on it**: 14 facts of the corpus; S19.
* **Cost to reverse**: little.

## 2026-11-26 11:04 GMT. The closing: the remote's `main` had moved

* **Found** before the push: the remote's `main` was at `b698279`
  (one commit after `906e2fa`, by another campaign: `calculi/GLS`, ten
  files, nothing outside that folder; the library and the skill's text
  unchanged).
* **Decided**: the campaign's commits were rebased onto it, so that
  the push is a fast-forward. Their names changed; the names cited in
  these documents are the new ones. The full build was run again after
  the rebase.
* **Cost to reverse**: none.

## 2026-11-26 14:04 GMT. After the closing page: a complete certificate of non-derivability

* **The reviewer's word**, in the session, after the closing page:
  "Can you complete the counter model construction? Decidability +
  completeness means there must be one, that's complete of course. Also
  a tutorial modelled on the existing ones is needed." And later: "We
  don't need maximum efficiency, just an algorithm that doesn't
  terminate early with no result."
* **Decided**: a second certificate against a derivation, a *saturated
  set of sequents* (S20, S21; `MALL/Saturated.lean`, `MALL/SatRun.lean`,
  `MALL/Refute.lean`, `MALL/SatTest.lean`). The kernel checks a Boolean
  condition on the set; a theorem says that the set presents a finite
  phase structure in which the sequent does not hold. The certificate
  is proved complete, and its producer (a search that remembers what it
  settled) returns a set for every sequent with no derivation.
* **Not taken**: a finite monoid given by its tables, with the
  interpretation computed by the kernel (the structure of a set of 17
  sequents has 35 phases, and every dual is quadratic in that; and the
  check would have to verify the laws of the monoid, or the monoid be
  built so that they hold, which is what the saturated set does);
  enlarging the enumeration of cyclic groups (complete for no bound
  that is known here).
* **Its limit**: the set is exponential where ⊗ divides a context in
  many ways (`measurements.md`). The cyclic structures stay the first
  certificate tried.
* **`explain` is unchanged**; the new description of a countermodel is
  `describeCountermodel`.
* **Cost to reverse**: little.

## 2026-11-26 15:06 GMT. A command: Craig interpolation and uniform interpolation, as goals

* **The reviewer's words**, relayed by the session that started this
  one (15:04): to its question "Add Craig and uniform interpolation for
  MALL as goals of the MALL development?": "Yes, for MALL"; then
  "please delegate this to the existing agent MALL, phase 1 rather than
  starting a new one".
* **Decided, the statements** (`MALL/Statements.lean`, entered before
  any proof; `statements.md`, S22 to S25):
  (a) Craig interpolation as a function on derivations without cut, for
  a sequent divided in two, `⊢ Γ, Δ`: a formula `C` with `⊢ C, Γ` and
  `⊢ C⊥, Δ`. With Lyndon's condition, which in negation normal form is
  a condition on literals and costs nothing more: every literal of `C`
  occurs in `Δ` and, negated, in `Γ`. The condition on letters is a
  corollary.
  (b) Uniform interpolation for a sequent `Γ` and one letter `p`: a
  formula `I` without `p`, its letters among those of `Γ`, with
  `⊢ I⊥, Γ` and, for every `Δ` without `p` with `⊢ Γ, Δ`, `⊢ I, Δ`. As
  a proposition about `Derivable`; the interpolant is to be a function
  `ui p Γ`. For a formula: `∀p A` is `I` at `[A]`, and `∃p A` is the
  negation of `I` at `[A⊥]`.
* **The route decided for (b)**, before the sources were read: the
  interpolant by recursion on the size of `Γ`, along the rules read
  upwards (the search ends by itself, since no rule contracts), with a
  disjunct for each rule instance on `Γ` and one for each proper
  division of `Γ` (for a ⊗ of the other side); its two properties by
  induction, the second on a derivation without cut. This is Pitts's
  method as the sources are said to apply it to logics without
  contraction; whether it is their construction is to be checked when
  they are read.
* **Not taken**: interpolants of a set of letters at once (iterate);
  the properties of (b) as functions on derivations (the proof divides
  permutations, which gives existence and not data, and nothing asks
  for the data).
* **Cost to reverse**: a statement, little.

## 2026-11-26 15:21 GMT. Interpolation: the sources, read after the proofs; what was not attempted

* **The sources** were fetched and read by an agent while the proofs
  were being written; its report is
  [interpolation-sources.md](interpolation-sources.md), with each file's
  origin and size. Obtained: Alizadeh, Derakhshan and Ono 2014 (the
  publisher's PDF on an author's page, 246 606 bytes); Akbar Tabatabai
  and Jalali, arXiv:1808.06258 v2 and arXiv:1808.06256 v3; Roorda's
  thesis of 1991 (his deposit, a scan, read from page images, in part).
  **Not obtained**: Roorda, JSL 59 (1994): for purchase only.
* **What they changed**: no statement. They gave the items the
  statements are cited to, and one correction of names: MALL with its
  four units is InFLₑ in the first paper and CFLₑ in the second, and in
  the Craig paper CFLₑ is the logic with two units only.
* **The statement of uniform interpolation was made, screened and
  proved before any source was read**; it is the one-sided form of
  Theorem 4.3 of the first paper. That paper writes no proof for MALL.
* **Lyndon's condition** is in the statement of Craig interpolation
  because in negation normal form it is a condition on literals and its
  proof is no longer; Roorda states it, Akbar Tabatabai and Jalali do
  not.
* **Not attempted**: Roorda's fragment without interpolation as a
  REFUTED statement (the task's third item, "only if you can obtain the
  paper"): `statements.md`, "Not goals".
* **The reading back** of S22 to S25 was made by a fresh agent from an
  extract of 124 lines; no statement was found false, trivial or other
  than meant. It changed no statement and added one screen; its remarks,
  and one statement it suggested that is left OPEN (a condition on signs
  for the uniform interpolant), are in `statements.md`.
* **Cost to reverse**: little.

## Stops

*Each time a turn ended to wait for the reviewer. None so far.*

| date | what was asked, and why only the reviewer can answer it | what went on meanwhile | the answer, in the reviewer's words |
|---|---|---|---|
