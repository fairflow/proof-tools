# ∧ and ∨ in GLS: defined, their rules derived, the sides exchanged

2026-11-26. Operator: Claude Opus 5.5. The reviewer's task, verbatim:

> (C) there's no ∨ or ∧ in this development that I can see, it
> corresponds to a minimal logic, can we define these or extend to
> these? Clearly multiple premises implies ∧ on the left and multiple
> conclusions ∨ on the right, but can we switch sides?

**Answers.**

1. The `{→, ⊥}` fragment here is **classical, not minimal**. ImpR keeps the
   whole succedent, so a sequent may have several conclusions, and that is
   enough for Peirce's law. Classically `{→, ⊥}` is functionally complete,
   so `∧` and `∨` are **definable**. They are now defined
   (`GLS/Connectives.lean`).
2. Each defined connective has a left rule and a right rule in GLS. Each
   rule is derived from the rules of GLS, with at most a height-preserving
   weakening by `⊥`. Each has an admissible inverse. All of these are
   PROVED in Lean (`GLS/ConnectiveRules.lean`), within `[propext, Quot.sound]`.
3. **Sides can be switched, in two senses.** As connectives: `∨` gets a
   left rule and `∧` a right rule, both with two premises. And a formula
   changes sides by negation, both ways: `Γ ⇒ A, Δ` is derivable iff
   `¬A, Γ ⇒ Δ` is. What cannot be switched is the *comma*. A comma on the
   left always reads as `∧` and a comma on the right as `∨`. That is
   PROVED too: `Γ ⇒ Δ` is derivable iff `⇒ ⋀Γ → ⋁Δ` is.
4. **Define rather than add.** Definitions cost nothing: every result of
   the campaign holds for them at once. Primitive rules would reopen cut
   admissibility, the measure, the search, the semantics and the
   interpolant (§5).

## 1. The definitions

    ¬A := A → ⊥        ⊤ := ⊥ → ⊥        ◇A := ¬□¬A
    A ∧ B := ¬(A → ¬B)                    A ∨ B := ¬A → B

with `⋀[A₁, …, Aₙ] := A₁ ∧ (… ∧ ⊤)` and `⋁[A₁, …, Aₙ] := A₁ ∨ (… ∨ ⊥)`.
In Lean, `A ⋏ B` and `A ⋎ B` (`Form.and`, `Form.or`), with lemmas giving
their truth at a tree: `holds_and`, `holds_or`, `holds_dia` (`◇A` holds iff
`A` holds at some proper descendant), `holds_conjL` and `holds_disjL`.

The tutorial (§1) already used `¬`, `◇` and `⊤` informally. They are now
definitions, and `∧` and `∨` join them.

## 2. Classical, not minimal

    def GLS.peirce (p q : Nat) : Fam ([] ⇒ [((Form.var p ⟶ Form.var q) ⟶ Form.var p) ⟶ Form.var p])
    PROVED · axioms: propext

The derivation is short. ImpR, then ImpL on `(p → q) → p`, whose first
premise `⇒ p → q, p` is closed by ImpR and IdP on the *second* conclusion
`p`. That second conclusion is exactly what a single-succedent
(intuitionistic or minimal) calculus lacks. The tutorial's exercise A4
derives `¬¬p → p` in the same way. In minimal and intuitionistic logic,
`∧` and `∨` are not definable from `→` and `⊥` (the connectives are
independent there, a classical result of McKinsey, 1939, cited from
memory). So the question "define or extend" has different answers in
the two settings. Classically, here, the answer is define.

## 3. The rules

Each rule is stated with the principal formula first, as `Fam` terms.
"Derived" means built from the premises by rules of GLS (ImpR, ImpL,
BotL, GLR), with at most a height-preserving weakening by `⊥` on the right
(`GLS/Structural.lean`).

| rule | premises ⟹ conclusion | Lean |
|---|---|---|
| ∧L | `A, B, Γ ⇒ Δ`  ⟹  `A ∧ B, Γ ⇒ Δ` | `Fam.andL` |
| ∧R | `Γ ⇒ A, Δ` and `Γ ⇒ B, Δ`  ⟹  `Γ ⇒ A ∧ B, Δ` | `Fam.andR` |
| ∨L | `A, Γ ⇒ Δ` and `B, Γ ⇒ Δ`  ⟹  `A ∨ B, Γ ⇒ Δ` | `Fam.orL` |
| ∨R | `Γ ⇒ A, B, Δ`  ⟹  `Γ ⇒ A ∨ B, Δ` | `Fam.orR` |
| ¬L | `Γ ⇒ A, Δ`  ⟹  `¬A, Γ ⇒ Δ` | `Fam.negL` |
| ¬R | `A, Γ ⇒ Δ`  ⟹  `Γ ⇒ ¬A, Δ` | `Fam.negR` |
| ⊤R | `Γ ⇒ ⊤, Δ` | `Fam.topR` |
| ◇L | `A, xbox Γ, □¬A ⇒`  ⟹  `◇A, Γ ⇒ Δ` | `Fam.diaL` |
| ◇R | `□¬A, Γ ⇒ Δ`  ⟹  `Γ ⇒ ◇A, Δ` | `Fam.diaR` |

As Lean prints the four for `∧` and `∨` (pinned in `GLS/InterpolationTest.lean`):

    def GLS.Fam.andL (A B : Form) {Γ Δ : List Form} (d : Fam (A :: B :: Γ ⇒ Δ)) : Fam ((A ⋏ B) :: Γ ⇒ Δ)
    def GLS.Fam.andR (A B : Form) {Γ Δ : List Form} (d₁ : Fam (Γ ⇒ A :: Δ)) (d₂ : Fam (Γ ⇒ B :: Δ)) :
      Fam (Γ ⇒ (A ⋏ B) :: Δ)
    def GLS.Fam.orL (A B : Form) {Γ Δ : List Form} (d₁ : Fam (A :: Γ ⇒ Δ)) (d₂ : Fam (B :: Γ ⇒ Δ)) :
      Fam ((A ⋎ B) :: Γ ⇒ Δ)
    def GLS.Fam.orR (A B : Form) {Γ Δ : List Form} (d : Fam (Γ ⇒ A :: B :: Δ)) : Fam (Γ ⇒ (A ⋎ B) :: Δ)

all PROVED, axioms within `propext, Quot.sound`. The derivations, read
upwards:

* ∧L: ImpL on `(A → ¬B) → ⊥`. One premise is BotL. The other is
  `Γ ⇒ A → ¬B, Δ`, which is ImpR twice and then `B, A, Γ ⇒ ⊥, Δ`: the
  given premise, exchanged and weakened by `⊥`.
* ∧R: ImpR, then ImpL on `A → ¬B` and on `¬B`. The leaves are the two
  premises, weakened by `⊥`, and BotL.
* ∨L: ImpL on `¬A → B`. The left premise `Γ ⇒ ¬A, Δ` is ImpR on the first
  given premise, weakened by `⊥`. The right premise is the second given
  premise.
* ∨R: ImpR, then ImpL on `¬A`. The leaves are the given premise and BotL.
* ◇L is the dual of GLR. `◇A` on the left is `□¬A` on the right, so GLR
  applies, and its premise `xbox Γ, □¬A ⇒ ¬A` is ImpR on the given
  premise. The premise carries `□¬A`, the Löb diagonal: a witness for `◇A`
  can be taken to be a last world where `A` holds. The tests confirm
  `◇p → ◇(p ∧ □¬p)`.
* ◇R has no modal content. A diamond on the right is a box on the left,
  and GLS uses a boxed antecedent formula only as a side formula of GLR.

The **inverses**, all admissible (PROVED): `andLInv`, `andRInv` (both
premises), `orLInv` (both premises), `orRInv`, `negLInv`, `negRInv`,
`diaRInv`. They use the height-preserving inversion of ImpR and ImpL
(`GLS/Invert.lean`). Where a `⊥` must be removed from a succedent, they
use the source's cut on `⊥` against BotL (`Fam.botRElim`, `GLS/Cut.lean`).
So `∧L`, `∨R`, `¬L`, `¬R` are invertible single-premise rules, and `∧R`,
`∨L` are invertible branching rules, exactly as in G3c.

## 4. Switching sides

    def GLS.switchRL (A : Form) {Γ Δ : List Form} :
      (Fam (Γ ⇒ A :: Δ) → Fam (A.neg :: Γ ⇒ Δ)) × (Fam (A.neg :: Γ ⇒ Δ) → Fam (Γ ⇒ A :: Δ))
    def GLS.switchLR (A : Form) {Γ Δ : List Form} :
      (Fam (A :: Γ ⇒ Δ) → Fam (Γ ⇒ A.neg :: Δ)) × (Fam (Γ ⇒ A.neg :: Δ) → Fam (A :: Γ ⇒ Δ))
    def GLS.seqFormula (Γ Δ : List Form) :
      (Fam (Γ ⇒ Δ) → Fam ([] ⇒ [conjL Γ ⟶ disjL Δ])) × (Fam ([] ⇒ [conjL Γ ⟶ disjL Δ]) → Fam (Γ ⇒ Δ))

all PROVED. `seqFormula` is the precise form of "multiple premises are ∧
on the left and multiple conclusions ∨ on the right". It is proved by the
semantic route (truth at a tree, then the search), so its derivations
are the search's, not built from the given ones.

So: `A₁, A₂, Γ ⇒ Δ` iff `A₁ ∧ A₂, Γ ⇒ Δ` (∧L and its inverse), and
`Γ ⇒ B₁, B₂, Δ` iff `Γ ⇒ B₁ ∨ B₂, Δ` (∨R and its inverse). Moving a formula
across the arrow negates it, and so turns a right-hand `∨` into a
left-hand `∧` of negations, as de Morgan says. A *comma* meaning `∨` on the
left would need a different structure: hypersequents, or a "dual" sequent
read as `⋁Γ → ⋀Δ`. GLS has neither. The tests (`GLS/InterpolationTest.lean`)
check by search that `p ∨ q ⇒ p, q` is derivable while `p ∨ q ⇒ p` is not,
and that `p, q ⇒ p ∧ q` is derivable while `q ⇒ p ∧ q` is not.

**Under the box** (search, pinned): `□(p ∧ q) ↔ □p ∧ □q` and
`◇(p ∨ q) ↔ ◇p ∨ ◇q` are derivable, and so is `□p ∨ □q → □(p ∨ q)`. Its
converse `□(p ∨ q) → □p ∨ □q` is refuted. The countermodel returned is a
root with two children, one where only `q` holds and one where only `p`
holds. This is where the modal rule differs from the propositional ones:
GLR keeps only one succedent formula, so the comma-as-`∨` does not pass
under `□`.

## 5. Define or add?

**Defined (what is done).** No rule, file or proof of the campaign
changes. Soundness, completeness, cut admissibility, the termination of
PSGLS, the finite model property, decidability, uniform interpolation and
the tutorial all hold for formulas with `∧` and `∨` as they stand, because
those formulas are formulas of the old language. The cost is size: `A ∧ B`
adds three connectives, and the search spends three or four rule
applications on each `∧`, where a primitive rule would spend one.

**Primitive (what it would cost).** Adding constructors `and`, `or` to
`Form`, and rules ∧L, ∧R, ∨L, ∨R to `Fam` and `PSFam`, would touch:

* *the family and every induction on it*: weakening, exchange, the two
  inversions (plus four new ones), contraction (new cases, with the usual
  height-preserving invertibility arguments), and `Fam.height`;
* *cut admissibility* (`GLS/Cut.lean`, the source's route): new principal
  cases for `∧` and `∨`. These are standard and reduce the cut formula's
  size. The GLR case is unaffected, because GLR does not look inside its
  side formulas;
* *the measure* (`GLS/Measure.lean`): `nImp` must count `∧` and `∨`. The
  number of usable boxes is unchanged. ∧R and ∨L branch, as ImpL does, and
  the lexicographic measure still falls;
* *the search and its countermodels* (`GLS/Search.lean`): two invertible
  cases more in `classify`, and the refutation lemmas for each premise.
  Nothing new at the prime case;
* *the semantics*: two cases of `sat` and `holds`, and of soundness;
* *the interpolant* (`GLS/Interpolation.lean`): new invertible cases,
  ∧R and ∨L giving `∨` of the premises' interpolants as ImpL does, ∧L and
  ∨R passing through;
* *the source*: GLS as Goré, Ramanayake and Shillito state it has only
  `→`, `⊥`, `□`. A primitive `∧` and `∨` would make the calculus a
  different one from the source's, and the second-transcription checks of
  `rule-table.md` would not cover it. Bílková's G_GL has them primitive
  (report A, §5), so there is a source to follow.

None of this is hard. All of it is work for no gain in what can be proved,
since the defined connectives' rules are already derived and invertible.
Primitive connectives are worth having for only two reasons. The first is
readability of derivations in the explorer, where one ∧L move is clearer
than three moves on implications. That can be had without changing the
calculus: a *macro move* in the explorer (`glsmove andL`) that applies the
derived rule. The second is an intuitionistic variant (report B), where
`∧` and `∨` are not definable and must be primitive.

## 6. Status

| statement | status |
|---|---|
| `∧`, `∨`, `¬`, `⊤`, `◇` defined; truth lemmas | PROVED |
| ∧L, ∧R, ∨L, ∨R, ¬L, ¬R, ⊤R, ◇L, ◇R derived | PROVED |
| their inverses admissible | PROVED |
| switching sides by negation, both ways | PROVED |
| `Γ ⇒ Δ` iff `⇒ ⋀Γ → ⋁Δ` | PROVED |
| Peirce's law derivable (the calculus is classical) | PROVED |
| a `glsmove` macro for the derived rules | not done |
