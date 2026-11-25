# Brief: GLS, stage 2 (Prove), goals 4 to 6

Written 2026-11-25 09:38 GMT, by the operator, for a fresh agent that the
operator starts (the skill's rule 5). The agent works in the operator's
checkout while the operator goes on with stage 3; it reports back, and
the operator takes the result in.

The target, the place of the files and the rules of the project are in
`calculi/GLS/campaign/decisions.md`, the first entry.

## The task

Prove, in Lean 4 (v4.31.0, core Lean only), goals 4, 5 and 6 of the
plan: the statements S11 to S19 of `calculi/GLS/campaign/statements.md`.
Their types are already in `calculi/GLS/GLS/Semantics.lean`, and **must
not be changed**:

    Exchange  WeakeningL  WeakeningR  InversionImpR  InversionImpL
    ContractionL  ContractionR  PSEquivalent  CutAdmissible

Done is: new theory files, each ending with
`#axioms_within_file [propext, Quot.sound]` and building with no error,
no `sorry` and no warning of yours, that define

    def exchange : Exchange              def weakeningL : WeakeningL        def weakeningR : WeakeningR
    def inversionImpR : InversionImpR    def inversionImpL : InversionImpL
    def contractionL : ContractionL      def contractionR : ContractionR
    def psEquivalent : PSEquivalent
    def cutBySource : CutAdmissible      -- cut admissibility by the source's induction

`cutBySource` must be the syntactic construction below, made from the
two given derivations. It must not use `proofOrRefutation`, `soundness`,
`completeness` or `cutAdmissible` (the semantic proof, which exists
already in `GLS/Completeness.lean`).

## Read, in this order

1. `calculi/GLS/GLS/Form.lean`, `System.lean` (the family `Fam`, the
   height), `Semantics.lean` (the statements, at its end), `Lemmas.lean`
   (lists: `mem_erase_of_ne`, `eq_or_mem_erase`, `perm_cons_erase`,
   `Perm.erase'`, `mem_xbox`, `xbox_append`, `xbox_cons_box`,
   `xbox_perm`), `Identity.lean` (`Fam.id`), `Measure.lean` (`Closed`,
   `weight`, `PSPrem.step`, `closed_self`), `Search.lean` (`classify`,
   `Shape`, and the finders).
2. Nothing else is needed. Do not read or edit the campaign folder
   except this brief, and do not read the skill.

## What is decided

* The axiom policy: no `Classical.choice`. On Lean v4.31.0 core's
  `List.mem_erase_of_ne`, `List.Perm.erase` and `List.perm_cons_erase`
  use it: use the versions in `GLS/Lemmas.lean`. When a bound fails,
  `#print axioms name` on the lemmas you used finds the culprit; `omega`
  given a conjunction brings it in (split first); `by_cases` on an
  equation of formulas does not.
* A function on derivations is written by pattern matching on the
  constructors with recursive calls on the premises, not by the tactic
  `induction` (the code generator refuses `Fam.rec`). Where the
  recursion is not on a subterm (contraction, cut), recurse on a number
  that bounds the height or the measure.
* Lists are read as multisets. Every statement that the induction needs
  is stated up to a permutation, so that `List.erase` never has to be
  computed by cases.

## The route (the operator's design; change it where it does not go through, and say so)

**File `GLS/Structural.lean`.** One function,

    def Fam.wk : {Γ Δ : List Form} → (d : Fam (Γ ⇒ Δ)) → (Ξ Ξ' Γ' Δ' : List Form) →
        Γ'.Perm (Γ ++ Ξ) → Δ'.Perm (Δ ++ Ξ') → { d' : Fam (Γ' ⇒ Δ') // d'.height ≤ d.height }

by recursion on `d`. In ImpR and ImpL, `(Γ ++ Ξ).erase X = Γ.erase X ++ Ξ`
where `X ∈ Γ` (prove it without choice); in GLR,
`xbox (Γ ++ Ξ) ++ [□A]` is a permutation of `(xbox Γ ++ [□A]) ++ xbox Ξ`,
and the succedent `[A]` is weakened by nothing. Exchange is `wk` at
`Ξ = Ξ' = []`; `weakeningL` and `weakeningR` are `wk` at one formula,
with `List.perm_middle`.

**File `GLS/Invert.lean`.** With `X := A ⟶ B`:

    invR : (d : Fam (Γ ⇒ Δ)) → (Δ₀ : List Form) → Δ.Perm (X :: Δ₀) →
             { d' : Fam (A :: Γ ⇒ B :: Δ₀) // d'.height ≤ d.height }
    invL : (d : Fam (Γ ⇒ Δ)) → (Γ₀ : List Form) → Γ.Perm (X :: Γ₀) →
             { d' : Fam (Γ₀ ⇒ A :: Δ) // d'.height ≤ d.height } ×
             { d' : Fam (B :: Γ₀ ⇒ Δ) // d'.height ≤ d.height }

by recursion on `d`. Where the last rule is on the same formula `X`, the
premise is the answer up to exchange (`Δ.erase X` is a permutation of
`Δ₀`). Where it is on another implication `Y`, then `Y ∈ Δ₀` (or `Γ₀`),
the recursive call is at `Δ₀.erase Y` with what the rule added, and the
rule is applied again; the one lemma needed is

    Y ∈ L → ((B :: L).erase Y).Perm (B :: L.erase Y)

(both when `B = Y` and when not). At GLR the premise is unchanged for
`invL` at the first component (`xbox` of an implication is empty) and is
weakened by `Form.xb` of the formula added to the antecedent otherwise
(`Fam.wk`). The statements `inversionImpR`, `inversionImpL` are these at
`Δ₀ := Δ.erase X` with `perm_cons_erase`.

**File `GLS/Contract.lean`.** Left and right together, by recursion on a
bound `n` of the height, since the recursive calls are on derivations
that the inversions return:

    ctrL : (n : Nat) → (d : Fam (Γ ⇒ Δ)) → d.height ≤ n → (A : Form) → (Γ₀ : List Form) →
             Γ.Perm (A :: A :: Γ₀) → { d' : Fam (A :: Γ₀ ⇒ Δ) // d'.height ≤ d.height }
    ctrR : the same with Δ.Perm (A :: A :: Δ₀), giving Fam (Γ ⇒ A :: Δ₀)

(mutually recursive on `n`, or one function returning a pair). Cases of
the last rule: an axiom, immediate; a rule on another formula, the
recursive call on its premises and the rule again; ImpR with principal
formula the contracted `A = C ⟶ D` on the right: invert the other copy
in the premise (`invR`), then contract `C` on the left and `D` on the
right, and apply ImpR; ImpL with principal `A` on the left: `invL` on
each premise, contract `C` on the right of the first and `D` on the left
of the second, and apply ImpL; GLR while contracting `A = □E` on the
left: the premise has `E, □E, E, □E`, contract both; GLR otherwise: the
premise is unchanged up to exchange. `contractionL`, `contractionR` are
these with the permutation
`Γ0 ++ A :: Γ1 ++ A :: Γ2 ~ A :: A :: (Γ0 ++ Γ1 ++ Γ2)`.

**File `GLS/PS.lean`.** `psEquivalent`. From `Fam` to `PSFam` by
recursion on the derivation; at GLR, decide as data whether the
conclusion is an instance of IdP, BotL or IdB (the finders of
`GLS/Search.lean`: `findIdP`, `findIdB` with their `_some` and `_none`
lemmas, or `classify`), and use that axiom of PSGLS if it is, PSGLR with
the three negations if not. From `PSFam` to `Fam`: IdB is `Fam.id`.

**File `GLS/Cut.lean`.** The source's proof (`GLS_cut_adm_main`,
`GL/GLS_additive_cut.v` of `ianshil/CE_GLS`): induction on the size of
the cut formula, then on the termination measure of the conclusion (the
source uses `mhd`, the maximal height of a PSGLS derivation; here
`weight U`, which falls along `PSPrem` by `PSPrem.step`). Two levels,
both structural:

    abbrev CutFor (m : Nat) : Type :=
      (A : Form) → (Γ Δ : List Form) → A.size ≤ m → Fam (Γ ⇒ A :: Δ) → Fam (A :: Γ ⇒ Δ) → Fam (Γ ⇒ Δ)

    def cutStep {m : Nat} (ih : CutFor m) : (k : Nat) → (U : List Form) → (A : Form) → (Γ Δ : List Form) →
        A.size ≤ m + 1 → Closed U (Γ ⇒ Δ) → weight U (Γ ⇒ Δ) < k →
        Fam (Γ ⇒ A :: Δ) → Fam (A :: Γ ⇒ Δ) → Fam (Γ ⇒ Δ)

    def cutFor : (m : Nat) → CutFor m      -- at m + 1: cutStep (cutFor m) at U := (Γ ⇒ Δ).boxSubs, k := weight + 1

`cutStep` at `k + 1` looks at the **conclusion** `s = Γ ⇒ Δ` first
(`classify s`), as the source does:

* `s` is an axiom (IdP, BotL, or IdB by `Fam.id`): done.
* `s` has an implication `C ⟶ D` on the right (or on the left): invert
  it in both given derivations (`invR`, `invL`), call `cutStep k` on the
  premise or premises (they are `PSPrem`-premises of `s`: `PSPrem.step`
  gives `Closed` and the smaller weight), and apply the rule.
* `s` is prime (`Shape.prime`: no axiom, no implication at top level).
  Match on the first derivation `d₁ : Fam (Γ ⇒ A :: Δ)`:
  - IdP on `p`: `var p ∈ Γ`; as `s` is no instance of IdP, `var p ∉ Δ`,
    so `A = var p`; contract `var p` in the second derivation (`ctrL`).
  - BotL, ImpL: impossible in a prime `s`.
  - ImpR on `C ⟶ D`: it is not in `Δ`, so `A = C ⟶ D`, and the premise is
    `C :: Γ ⇒ D :: Δ`. Invert `A` on the left in the second derivation
    (`invL`): `Γ ⇒ C :: Δ` and `D :: Γ ⇒ Δ`. Cut on `C` (by `ih`, with
    the first weakened by `D` on the right) to `Γ ⇒ D :: Δ`, then on `D`
    (by `ih`).
  - GLR on `□B`, with premise `d₀ : Fam (xbox Γ ++ [□B] ⇒ [B])`. If
    `□B ∈ Δ`: GLR on `s` with the same premise. Otherwise `A = □B`;
    match on the second derivation `d₂ : Fam (□B :: Γ ⇒ Δ)`: every rule
    but GLR is impossible in a prime `s`; GLR on `□C ∈ Δ` has the
    premise `e₀ : Fam (B :: □B :: xbox Γ ++ [□C] ⇒ [C])`
    (`xbox_cons_box`). Let `s' := xbox Γ ++ [□C] ⇒ [C]`, the
    `PSPrem`-premise of `s` by GLR on `□C`. Then:
    1. cut on `B` by `ih`: `d₀` weakened to
       `□B :: (xbox Γ ++ [□C]) ⇒ B :: [C]`, with `e₀`, gives
       `e₄ : Fam (□B :: (xbox Γ ++ [□C]) ⇒ [C])`;
    2. GLR on `□B` at `xbox Γ ++ [□C] ⇒ □B :: [C]`: its premise
       `xbox (xbox Γ ++ [□C]) ++ [□B] ⇒ [B]` is a weakening of `d₀`,
       since `xbox (xbox Γ)` is a permutation of
       `xbox Γ ++ xbox (Γ.filterMap Form.unbox?)` (a lemma to prove);
    3. `cutStep k` on `s'` with cut formula `□B`, the same size, and the
       smaller weight: `Fam s'`;
    4. GLR on `□C` at `s`.

`cutBySource` is `cutFor A.size A` after two exchanges that bring the
cut formula to the head.

## What is not decided

The names of lemmas, how the files are split, and any change of route:
yours. If a case will not close after two honest attempts by different
routes, do **not** leave a `sorry` and do not weaken a statement: stop
that goal, leave the files that do build, and report exactly which goal
and which case, with Lean's goal at that point.

## Limits

* Create only these files, in `calculi/GLS/GLS/`: `Structural.lean`,
  `Invert.lean`, `Contract.lean`, `PS.lean`, `Cut.lean`. Change no other
  file anywhere (not `GLS.lean`, not `Semantics.lean`, not `Lemmas.lean`:
  put the lemmas you need in your own files). Do not commit, do not
  push, do not use `git stash`.
* Build only your own modules: in `calculi/GLS/`, `lake build
  GLS.Structural` and so on (another process builds other modules of
  the package at the same time; do not run a bare `lake build`, and do
  not `lake clean`).
* No web access is needed.

## Done looks like

The five files, each building within its bound. Your last message: for
each of the nine definitions, PROVED (the file and the line) or not
(the goal and the case, with what was tried); the number of lines of
each file; each place where you left the route above, and why; and the
output of `#print axioms` for `cutBySource`, `contractionL` and
`psEquivalent`.
