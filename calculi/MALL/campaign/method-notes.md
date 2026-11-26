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
