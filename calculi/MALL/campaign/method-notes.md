# MALL: notes on the method

Each place where the skill `calculus-campaign` was wrong, silent or
unclear, and what was done there. Kept to what would change that text.
Phase 2 of this round is dual intuitionistic linear logic (Barber 1996):
a note says where a choice made here would, or would not, carry over.

## Stage 0

1. **A substructural calculus is not among the skill's forms for
   "Judgments as data"** (`reference/adopt.md` §3). It offers two: a
   list with membership ("so that exchange, weakening and contraction
   are admissible and need no rule"), or a list with an exchange rule.
   The first is wrong for a logic without weakening. *Done here*: a
   third form, every conclusion a variable `Ξ` under `Ξ.Perm (…)`. It
   builds in exchange and nothing else. *Proposed*: add it to §3, with
   what it costs: (a) Lean infers nothing from a variable conclusion,
   so the constructors take their formulas and contexts as explicit
   arguments; (b) S2 needs its induction generalised over a
   permutation of the sequent, since `step`'s premises are the rule's
   only up to one. *Phase 2*: the linear zone of DILL takes this form;
   its intuitionistic zone takes the membership form.
2. **The skill's list of where `Classical.choice` enters is short by
   the permutation lemmas** (`reference/adopt.md` §6 names
   `List.mem_erase_of_ne`). On Lean v4.31.0 also `List.isPerm_iff`
   (hence core's instance deciding `List.Perm`, hence any `by decide`
   of a permutation), `List.perm_cons_erase`, `List.Perm.erase`,
   `List.cons_perm_iff_perm_erase`. *Done here*: a file of the
   campaign's own (`MALL/Perm.lean`), copied in part from GLS.
   *Proposed*: say so in §6; and move `perm_count`, `perm_of_count`
   and the `erase` lemmas into the library (they are now written
   twice, in GLS and here, and phase 2 will want them a third time).
   That is a finding about the library (rule 7), not done here.
3. **A scan with no text layer.** The source is page images; the
   machine had `tesseract` with no language data. *Done*: the pages
   were read as images by the operator, the skeleton written by hand,
   and the cold reader given PNG files of four pages. The skill covers
   this ("From a PDF alone, write the list by hand"); nothing to
   change, but `pdftoppm -r 150 -png` is the command worth naming in
   §7, since a cold reader must be given files it can open.
4. **A source that draws no derivation of the fragment.** The skill
   says to take "the simplest instances of its theorems, or the axioms
   of the logic" for the exercises (`reference/explore.md` §10); stage
   1, step 4, asks for "the source's own worked derivations" as the
   first check of the transcription and is silent when there are none.
   *Done*: derivations of what the source asserts (two sentences of
   p. 5, the remark of p. 22, the semantic equations 1.9 and 1.13 read
   as sequents). *Proposed*: let step 4 say the same as §10.

## Stage 1

5. **A source's name that is a Lean keyword.** The connective & is
   "with"; a constructor `Form.with` is accepted by Lean (`.with A B`
   parses), a move `Move.with` is accepted too, and then
   `mallmove with p q` does not parse. The skill warns that the
   *tactic's* name becomes a keyword (`reference/explore.md` §5), not
   that a *move's* name must not be one. *Done*: renamed to `wth`
   (divergence D6). *Proposed*: one line in §2.
6. **A source's symbol that core Lean already uses.** `⊕` is core's
   notation for sum types, at a lower precedence. A scoped `⊕` for
   formulas works in most places, fails in a pattern, and is read as
   the sum type wherever an operator of precedence between the two
   follows it (`A ⊕ B :: Γ`, `A ⊕ B ∈ Γ`): the error names `Sum`.
   *Done*: kept the source's symbol; parentheses where needed;
   patterns by constructor. *Proposed*: a line in
   `reference/adopt.md` §3, "The source's letters", beside `λ Π Σ`:
   `⊕`, `×`, `∘`, `→` are taken, and what happens.
7. **The first act when a session is started by another session.** The
   skill says to tell the reviewer "in your own output". Done so. The
   entry "Told to the reviewer" of `decisions.md` cannot have a time
   "filled from the clock after the message is sent" when the message
   is part of the same turn as the commit that records it; the
   template might say "in the session's output, at the commit".

## Stage 2

8. **An agent's files and the default build.** Rule 5 says to leave an
   agent's files out of the commits until it reports. With the
   lakefile's glob (`MALL.+`) the default target also *builds* every
   file of the folder, so a plain `lake build` by the operator compiled
   an agent's half-written test file and failed. *Done*: built by
   target (`lake build MALL.Results`) until the agents reported, and
   told each agent to do the same. *Proposed*: say so in rule 5.
9. **An agent's names.** An agent wrote `def step` in the namespace
   `MALL`, where the proof system's `step` already is; its file did not
   import the other, so it compiled, and the clash showed only when
   both were imported. *Proposed*: `templates/brief.md` should ask for
   the names already taken in the namespace, or for a namespace of the
   agent's own.
10. **What a brief with a design in it bought.** The cut-elimination
    brief gave the operator's design (push the cut up one derivation,
    with handlers for the rules that introduce the formula; structural
    recursion on a bound of the size, then on the derivations). The
    agent kept the design and replaced the handlers by an inductive
    family indexed by the cut formula, which was better. So: give the
    design, and say that another is welcome. Both agents finished with
    nothing open (8.6 and 4.1 minutes by the environment's count).
11. **One abstraction served completeness and the finite model.** The
    skill's table of kinds (`reference/adopt.md` §2) lists the finite
    model property as "a construction of a model". Here it was the
    completeness construction over again with another congruence and
    another set of antiphases. *Proposed*: a line there: before a model
    is built for completeness, ask whether the finite model is the same
    construction with a parameter, and build it with the parameter.
12. **The reading back found no fault, and was still worth its three
    minutes.** It found, unprompted, the instances that refute
    weakening and contraction; it called the exchange statement
    trivial, which is what the encoding intends and is now said beside
    the statement; and its remark that validity is written through an
    order-dependent formula led to `valid_perm`. *Proposed*: the skill
    might say that a reader's "this is trivially true" and "this is
    false, here is the instance" are findings to enter, not noise.
13. **`perm_count` and a negation that is not unfolded.** `omega`
    takes `(A ⊗ B)ᗮ` and `Aᗮ ⅋ Bᗮ` for different atoms. A `show` with
    the unfolded list before the tactic settles it. A note for phase 2,
    where the same tactic will be used.

## Stage 3

14. **Against what holds, with no certificate.** `reference/certify.md`
    §4 describes the direct decision (`by decide +kernel`), and §3 the
    engine, which wants a certifier against what holds. The two meet in
    a certifier whose certificate is `Unit` and whose check is the
    decision procedure (`noDerivable` here). *Proposed*: say so in §3,
    so that a campaign with a proved search and no notion of written
    countermodel still has an engine and level 3.
15. **A pinned value written from expectation, again.** The screen's
    countermodel for `⊢ 1, 1` was pinned as the operator expected it
    and was wrong in its second component; the build refused it.
    Pitfall 11 says this already. It held.
16. **The proved search is the slow one.** Here the proved decision
    procedure is exponential in practice (it tries each formula as
    principal and each split), and the fast search is the one that is
    not proved. For a derivable sequent that costs nothing, since the
    fast search's tree is checked. For a sequent that is not derivable
    there is then no fast certified answer: the kernel must run the
    slow search. The skill's "a fast search that is not proved, beside
    the proved one" (§4) covers the first half only. *Proposed*: say
    that the "no" side then wants a certificate of its own (here: a
    finite phase structure), and that this is where a finite model
    property pays in Run.

## For phase 2 (dual intuitionistic linear logic)

* The linear zone: this campaign's form (a variable conclusion, a
  permutation hypothesis, explicit arguments), with `MALL/Perm.lean`
  as it stands. The intuitionistic zone: membership, as in GLS.
* A rule then has a hypothesis for each zone.
* Cut: the measure used here (the cut formula, then the two
  derivations, all structural) covers a cut on a linear formula. A cut
  on a formula of the intuitionistic zone uses its premise many times:
  it wants a substitution function of its own, by recursion on the
  derivation that uses the hypothesis (the cut agent's note).
* The decision procedure does not carry over as it is: with `!` the
  search has no bound of this kind.
* The lazy search carries over, and is closer to its sources there:
  Hodas and Miller's system is two-sided and intuitionistic.
