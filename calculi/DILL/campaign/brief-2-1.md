# Brief: DILL, stage 2 (Prove): the goals, handed to five agents

Written 2026-11-26 15:19 GMT by the operator. One page for all five; each
agent reads the common part and its own section.

The target, the place of the files and the rules of the project are in
`calculi/DILL/campaign/decisions.md`, the first entry; the plan is
`calculi/DILL/campaign/plan.md` (read its sections "Q1", "Choices of
encoding" and "Goals").

## Common part

**The calculus.** Dual intuitionistic linear logic as a two-zone sequent
calculus, in Lean 4 core only (toolchain v4.31.0, no Mathlib), in the
lake package `calculi/DILL/` of the repository (run every command from
that folder). Read, in this order:

1. `DILL/Form.lean` (formulas, `Seq`, the notation `Γ ⨾ Δ ⟹ C`);
2. `DILL/System.lean` (the family `Fam (c : Bool) : Seq → Type`, with the
   two cuts where `c = true`; `CF := Fam false`; `Fam.exch` for the
   linear zone; `Fam.mono` for the unrestricted zone, of which weakening
   and contraction are instances; `Fam.lift`; `Fam.height`, kept by
   `exch` and `mono`);
3. `DILL/Perm.lean` (permutation lemmas free of `Classical.choice`, the
   tactic `perm_count [h₁, …]` that proves a `List.Perm` goal from
   `Perm` hypotheses by counting, `permB`, `sub`, `perm_cons_cases`,
   `perm_singleton_eq`, `perm_nil_eq`);
4. `DILL/Statements.lean`: **your goals are named types there.** A goal
   that is a `Prop` is proved by `theorem name : Statement`; a goal that
   is an `abbrev … : Type` by `def name : Statement` (a function on
   derivations, written by pattern matching, not by the tactic
   `induction`: the code generator refuses `Fam.rec`);
5. for a model of the same work on a neighbouring calculus,
   `calculi/MALL/MALL/` (one-sided classical linear logic, the same
   treatment of the linear zone): the file your section names.

**Rules of the work.**

* Write only the files your section names. Do not edit any other file
  (not `Statements.lean`, not `System.lean`, not `DILL.lean`); if a
  statement looks wrong or unprovable, do not change it: say so in your
  report, with the counterexample.
* **Statements first.** Before proving a goal, try to refute it on small
  cases (empty zones, each constant, a formula that occurs twice). A
  refuted statement is a finding: report it, with the instance.
* Every file is a theory file: it ends with
  `#axioms_within_file [propext, Quot.sound]` (the command is in
  `ProofTools.Audit`, imported through `DILL.Form`), and has **no
  `sorry`**. Known sources of `Classical.choice` on this toolchain: core
  Lean's permutation lemmas (`List.perm_cons_erase`, `List.Perm.erase`,
  `List.isPerm_iff`, `decide` of a `Perm`), `omega` on a goal that is a
  conjunction (split first), `List.mem_erase_of_ne`. `DILL/Perm.lean`
  has replacements. `#choice_path d` shows where the axiom enters.
* A case that will not close becomes a **named hypothesis**: a
  `def Name : Prop := …` taken as an argument by the theorem. Not a
  `sorry`, and not a weaker statement under the same name.
* **Names.** Other agents write other files into the same namespace at
  the same time. Put every helper of yours in a namespace of your own
  (given in your section), and only the final theorems under the names
  your section gives. Taken already in `DILL`: `Form`, `Seq`, `ssize`,
  `Fam`, `CF`, `Derivable`, `CFDerivable`, `cons_sub`, `PhaseSpace`,
  `PhaseModel`, `tensorAll`, `Valid`, `ILL`, `ILLDerivable`, `Move`,
  `Rule`, `step`, `S`, `step_of`, `step_ok`, `step_sound`, `famOfDer`,
  `FamToDer`, `famToDer`, every name of `Statements.lean` and of
  `Perm.lean`.
* **Notation traps.** `!` is core Lean's Boolean negation and takes all
  that follows: write `(!A) :: Δ`, `(!A) ⊗ B`. `⊕` is core's sum type at
  a low precedence: write `(A ⊕ B) :: Δ`, `(A ⊕ B) ∈ Δ`. In a pattern,
  match by constructor (`.plus A B`, `.bang A`).
* **Build by target**, never the whole library (other agents' files are
  half written): `lake build DILL.<YourFile>`, from `calculi/DILL/`. The
  first build is seconds. Do not run `lake clean` or `lake update`.
* **Write your files to disk early and grow them**: a session can end
  under a running command, and what is only in the conversation is then
  lost. A build that may pass two minutes goes in the background with
  its output in a file.
* Do not commit, and run no git command that changes anything. Do not
  push. Do not touch anything outside `calculi/DILL/`.
* The operator's design is given below where there is one. **Another
  design is welcome** if it proves the same named statements.
* **Report** (your final message, at most 40 lines): each goal by name,
  PROVED or not, with the file; `lake build DILL.<YourFile>` passing or
  not; the lines of each file; anything you found wrong, awkward or
  refuted; what you would tell the next agent. If a goal is not reached,
  say what was tried and where it stopped.
* Budget: about 45 minutes of work. If a goal is not done by then,
  finish what builds, leave the rest as named hypotheses or out, and
  report.

## A. Cut (namespace `DILL.Cut`; files `DILL/Cut.lean`, then `DILL/Invert.lean`)

Goals, in `DILL/Cut.lean`: `def cutAdmissible : CutAdmissible`,
`def cutUAdmissible : CutUAdmissible`, `def cutElimination :
CutElimination`. Then, in `DILL/Invert.lean` (it imports `DILL.Cut`):
`tensorLInv`, `oneLInv`, `lolliRInv`, `withRInv`, `plusLInv`, `bangLInv`,
`bangRInv` (each a `def` of the type of the same name with a capital),
and `theorem deductionLinear : DeductionLinear`,
`theorem deductionUnrestricted : DeductionUnrestricted`. The source
proves the inversions by cut (CCP Lemma 6: cut against a small
derivation such as `Γ ; A, A ⊸ B ⟹ B`); with `cutAdmissible` each is a
few lines.

The source's proof (CCP Theorem 3, p. 12; Pfenning's notes Theorem 3.8):
nested induction on the cut formula `A`, then the linear cut before the
unrestricted one at the same `A`, then the two derivations.

Design. The trouble with structural recursion is the unrestricted zone:
commuting a cut above `!L` (or above `cutU`'s like) puts a new formula
into `Γ` on one side, and the other derivation must be weakened, which
is not a structural sub-derivation. Avoid weakening inside the
recursion by generalising over the zone: prove

    cutL : (∀ B ∈ Γ₁, B ∈ Γ') → (∀ B ∈ Γ₂, B ∈ Γ') →
           CF (Γ₁ ⨾ Δ ⟹ A) → Ξ ~ A :: Δ' → CF (Γ₂ ⨾ Ξ ⟹ C) → CF (Γ' ⨾ Δ ++ Δ' ⟹ C)
    cutU : (∀ B ∈ Γ₁, B ∈ Γ') → (∀ B ∈ Γ₂, B = A ∨ B ∈ Γ') →
           CF (Γ₁ ⨾ [] ⟹ A) → CF (Γ₂ ⨾ Δ' ⟹ C) → CF (Γ' ⨾ Δ' ⟹ C)

(or with the conclusion's linear zone a variable under a permutation
hypothesis, whichever is easier), by structural recursion on a bound `n`
of `A.size` (outermost), with `cutL` at `n` defined before `cutU` at `n`
(the copy case of `cutU` calls `cutL` at the same formula; the `!`
principal case of `cutL` calls `cutU` at a smaller one), then on the
derivations: for `cutL`, the right derivation (the one that uses `A`)
first, and where its last rule is a left rule on the cut formula, the
left derivation; for `cutU`, recursion on the derivation that uses the
hypothesis. `calculi/MALL/MALL/Cut.lean` (304 lines) did the one-sided
case with an inductive family indexed by the cut formula for the
principal cases; read it for the shape. `cutElimination` is then a
structural recursion on `Fam true j`, with `Fam.lift` nowhere needed.

Tests the result must pass (put them at the end of `Cut.lean` as
`example`s): cut elimination applied to a derivation with one `cut` and
one with one `cutU` returns a `CF` derivation (it type-checks), and
`(cutElimination _ d).height` evaluates by `#eval` or `decide` on a
small `d` (the function must compute: no `noncomputable`).

## B. Semantics (namespace `DILL.Sem`; files `DILL/Soundness.lean`, `DILL/Completeness.lean`)

Goals: `theorem soundness : Soundness` (in `Soundness.lean`);
`theorem completeness : Completeness` and
`theorem cutEliminationProp : CutEliminationProp` (in
`Completeness.lean`, which imports `DILL.Soundness`). Read
`DILL/Semantics.lean` first: it is Kanovich, Okada and Terui's
intuitionistic phase semantics (a commutative monoid with a closure
operator, `!X := Cl (X ∩ I)`, `I` the strict idempotents of `1`), and
`Valid j` is satisfaction of the formula `Seq.form j` at the unit.
Model of the work: `calculi/MALL/MALL/Soundness.lean` and
`Completeness.lean` (the latter builds its syntactic monoid as a
`Quotient`, within `[propext, Quot.sound]`).

Design. First a lemma that takes the formula of the sequent apart:
`S.Sat (Γ ⨾ Δ ⟹ C)` iff every product of phases `g₁ · … · gₙ · d₁ · … ·
dₘ` with `gᵢ ∈ ⟦!Gᵢ⟧` and `dⱼ ∈ ⟦Dⱼ⟧` is in `⟦C⟧` (every interpretation
is closed: prove `interp_closed` by induction on the formula; `X ⊸ Y` is
closed when `Y` is, by (Cl4)). Soundness is then an induction on
`Fam true j`, one case a rule; the facts wanted are that `Cl (X ∩ I)` is
inside `X` and inside `1`, that products of elements of `I` are in `I`,
and that `!X ⊆ Cl (!X · !X)`.

Completeness, by the canonical model (KOT, proof of Theorem 2.9 and
Remark 2.11, after Okada), built on the two-zone calculus itself: the
phases are pairs `(Γ, Δ)` of lists, up to the equivalence "`Γ` and `Γ'`
have the same members, and `Δ ~ Δ'`" (a `Quotient`; then `(Γ, [])` is a
strict idempotent, with no further identification); the product is
componentwise append, the unit `([], [])`; for each sequent
`Γ' ⨾ Δ' ⟹ C` the set `⟦Γ' ⨾ Δ' ⟹ C⟧ := {(Γ, Δ) | Nonempty (CF (Γ ++ Γ'
⨾ Δ ++ Δ' ⟹ C))}`, well defined by `Fam.mono` and `Fam.exch`; and
`Cl X` is the intersection of those sets that contain `X` (KOT Theorem
2.8: a family closed under `{y} ⊸ –` induces a closure operator, and
this family is closed under it since `{(Γ₀, Δ₀)} ⊸ ⟦Γ' ⨾ Δ' ⟹ C⟧ =
⟦Γ₀ ++ Γ' ⨾ Δ₀ ++ Δ' ⟹ C⟧`). The valuation of an atom `a` is
`⟦[] ⨾ [] ⟹ a⟧`. The main lemma (KOT Lemma 2.10), by induction on `B`:

    ([], [B]) ∈ ⟦B⟧   and   ⟦B⟧ ⊆ ⟦[] ⨾ [] ⟹ B⟧

each half using only rules without cut. For `!B`: `([B], [])` is in
`⟦B⟧` (from `([], [B]) ∈ ⟦B⟧`, since `⟦B⟧` is an intersection of sets of
the family, each closed under copy with weakening), is idempotent, and
is in `1` (weakening of `Γ`), so `([], [!B])` is in every set of the
family that contains `⟦B⟧ ∩ I`, by !L; conversely an idempotent `(Γ, Δ)`
has `Δ = []`, and `!R` applies. Then a valid sequent holds in this
model, `(Γ, Δ)` is in the product of the interpretations of its
hypotheses, so in `⟦C⟧`, so `CF (Γ ⨾ Δ ⟹ C)`. `cutEliminationProp` is
soundness then completeness. Everything constructive: no excluded
middle is expected to be needed (MALL's needed none).

If time is short, soundness comes first and must be finished; a
completeness that stops is reported with the lemma it stopped at as a
named hypothesis.

## C. Results (namespace `DILL.Res`; file `DILL/Results.lean`)

Goals, all by direct recursion or induction on derivations, none needs
cut: `def weakeningU : WeakeningU`, `def contractionU : ContractionU`,
`theorem exchangeKeepsHeight : ExchangeKeepsHeight`,
`theorem exchangeUKeepsHeight : ExchangeUKeepsHeight` (these four are
one line each from `System.lean`); `def identityExpansion :
IdentityExpansion` (first a function `(A : Form) → (Γ : List Form) →
{ d : CF (Γ ⨾ [A] ⟹ A) // d.Atomic }` by recursion on `A`, then replace
each init); `theorem subformulaProperty : SubformulaProperty`. And these
forms without cut, which the operator will join to cut elimination:

    theorem consistencyCF : ¬ Nonempty (CF ([] ⨾ [] ⟹ 𝟎))
    def disjunctionCF : (A B : Form) → CF ([] ⨾ [] ⟹ A ⊕ B) → CF ([] ⨾ [] ⟹ A) ⊕ CF ([] ⨾ [] ⟹ B)
    theorem not_cf_weak : ¬ Nonempty (CF ([] ⨾ [.atom 0] ⟹ 𝟏))
    theorem not_cf_contr : ¬ Nonempty (CF ([] ⨾ [.atom 0] ⟹ .atom 0 ⊗ .atom 0))

(the last two are the instances that will refute weakening and
contraction of the linear zone: `· ; · ⟹ 1` and `· ; a, a ⟹ a ⊗ a` are
derivable; give those two derivations as well, as `def`s of type
`CF …`). Model: `calculi/MALL/MALL/Results.lean`.

## D. Decidability (namespace `DILL.Dec`; file `DILL/Decide.lean`)

Goal: a decision of derivability without cut for sequents with an empty
unrestricted zone and no `!`:

    def decideCF : (Δ : List Form) → (C : Form) → (∀ A ∈ C :: Δ, A.bangFree = true) →
        Decidable (Nonempty (CF ([] ⨾ Δ ⟹ C)))

(the operator joins it to cut elimination to prove `BangFreeDecidable`).
It must be **run by the kernel**: structural recursion only (on a bound
of `ssize Δ + C.size`), no well-founded recursion, no `partial`,
`Decidable` instances that compute, so that
`example : ¬ Nonempty (CF ([] ⨾ [.atom 0] ⟹ 𝟏)) := by decide` (or
`decide +kernel`) goes through; put six such examples at the end of the
file, three derivable and three not, among them
`· ; a ⊸ (b ⊗ c) ⟹ (a ⊸ b) ⊗ (a ⊸ c)` (not derivable) and
`· ; a ⊸ b, a ⟹ b` (derivable). Design: a Boolean search `search n Δ C`
that tries init, each right rule by the shape of `C`, each left rule at
each formula of `Δ` (`List.erase`), and for ⊗R and ⊸L each division of
the rest of the zone into two sublists (by a list of Boolean masks, or
MALL's enumeration of sublists); in such a sequent no rule but copy and
!L changes the unrestricted zone, neither applies, and every premise is
smaller, so `n = ssize Δ + C.size` suffices. Then soundness (`search … =
true → Nonempty (CF …)`) and completeness (by induction on the `CF`
derivation, generalised over a permutation of the linear zone, using
that an empty `Γ` stays empty and bang-free stays bang-free). Model:
`calculi/MALL/MALL/Decide.lean` (409 lines), which did this for the
one-sided calculus. Speed matters less than that it is proved; say in
the report how long the six examples take.

## E. Translation (namespace `DILL.Tr`; file `DILL/Translate.lean`)

Goals: `def toILL : ToILL`, `def ofILL : OfILL`,
`theorem illEquivalence : ILLEquivalence`. Read `DILL/ILL.lean`: one-zone
intuitionistic linear logic with !D, !C, !W, !r (Kanovich, Okada and
Terui's Figure 1), in the same form as `Fam`. The source of the
statement is CCP Theorem 7 (p. 20), items 1 and 3; its proof sketch for
!L of ILL: "by i.h., by weakening (Thm. 2 (1)), by copy, by !L".

Design. `toILL`, by recursion on the two-zone derivation, generalised
over a permutation of the one-zone context (`Ξ ~ Γ.map Form.bang ++ Δ →
ILL c Ξ C`): init is identity after weakening every `!G` (!W); copy is
!D then !C; a rule with two premises that share `Γ` needs every `!G`
contracted after the rule (a lemma: from `ILL c (Γ.map bang ++ Γ.map
bang ++ Θ) C` to `ILL c (Γ.map bang ++ Θ) C`); !L adds nothing (the
formula `!A` is already where it should be); !R is !r; cut is Cut and
cutU is !r on the first premise then Cut. `ofILL`, by recursion on the
one-zone derivation with the context any list: first
`ILL true Θ C → Fam true ([] ⨾ Θ ⟹ C)` (!D: weaken `Γ` by `A`, copy,
!L; !W: weaken `Γ`, !L; !C: invert !L twice, contract, !L; !r: invert !L
on each formula of the context, !R, then !L back), then from
`Fam true ([] ⨾ Γ.map bang ++ Δ ⟹ C)` to `Fam true (Γ ⨾ Δ ⟹ C)` by
inverting !L for each formula of `Γ`. The inversion of !L in the
calculus *with* cut is short and needs no cut elimination:
`Fam true (Γ ⨾ (!A) :: Δ ⟹ C) → Fam true (A :: Γ ⨾ Δ ⟹ C)` is a `cut`
against `A :: Γ ⨾ [] ⟹ !A` (!R, copy, init) after weakening. Write it
in your own namespace; do not wait for agent A's `bangLInv`.
