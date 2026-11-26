# DILL: the source's numbered results

Written by hand from the PDFs (no LaTeX of any of them is public, so
there are no labels): the printed number, with the version, is the key.

## CCP: Chang, Chaudhuri, Pfenning, CMU-CS-03-131R (revised 29 December 2003)

Sections 2 and 3 only; printed page numbers.

| item | page | statement, in brief | in the fragment? |
|---|---|---|---|
| Principle 1 (Substitution) | 2 | if `Δ ⊩ A true` and `Δ′, A true ⊩ C true` then `Δ, Δ′ ⊩ C true` | natural deduction: left out |
| Figure 1 | 8 | natural deduction for JILL | left out |
| Theorem 1 (Structural Properties) | 9 | substitution; weakening and contraction of valid hypotheses, for natural deduction | left out |
| Principle 6 (Cut) | 10 | if `Δ ⊩ A goal` and `Δ′, A res ⊩ C goal` then `Δ, Δ′ ⊩ C goal` | the linear cut, before the zones |
| init, copy, promote | 11 | the judgmental rules | init, copy |
| Theorem 2 (Structural Properties) | 11 | 1. if `Γ ; Δ ⟹ γ` then `Γ, A ; Δ ⟹ γ` (weakening). 2. if `Γ, A, A ; Δ ⟹ γ` then `Γ, A ; Δ ⟹ γ` (contraction) | yes |
| Principle 7 (Cut) | 11 | 1. if `Γ ; · ⟹ A ; ·` and `Γ, A ; Δ′ ⟹ γ` then `Γ ; Δ′ ⟹ γ`. 2. if `Γ ; Δ ⟹ A ; ·` and `Γ ; Δ′, A ⟹ γ` then `Γ ; Δ, Δ′ ⟹ γ`. 3. (possibility) | 1 and 2 |
| Figure 2 | 12 | the sequent calculus for JILL: 21 rules | 18 of them |
| Theorem 3 | 12 | "The above principles of cut are admissible rules in JILL" | rows 1 and 2 |
| Theorem 4 (Soundness of ⟹ wrt ⊢) | 14 | sequent derivations give natural deductions | left out |
| Theorem 5 (Completeness of ⟹ wrt ⊢) | 16 | natural deductions give sequent derivations without cut | left out |
| Lemma 6 | 17-18 | invertible: ⊗L, 1L, ⊸R, &R, ⊤R, ⊕L, 0L, !L, ?R; weakly invertible: 1R, !R, ?L; not invertible: ⊗R, ⊸L, &L₁, &L₂, ⊕R₁, ⊕R₂ | without ?L, ?R |

## Pfenning: *Linear Logic*, draft of 26 January 2002, chapter 3

Read, not the source of record (its title page asks that it not be
cited). Printed page numbers.

| item | page | statement, in brief |
|---|---|---|
| the rules | 46-48 | the same calculus, with ∀, ∃, ⊃ besides |
| Theorem 3.1, 3.2 | 48-49 | soundness and completeness of sequent derivations against normal natural deductions |
| Theorem 3.8 (Admissibility of Cut) | 57 | 1. if `Γ; Δ ⟹ A` and `Γ; (Δ′, A) ⟹ C` then `Γ; (Δ, Δ′) ⟹ C`. 2. if `Γ; · ⟹ A` and `(Γ, A); Δ′ ⟹ C` then `Γ; Δ′ ⟹ C` |
| Theorem 3.9 (Cut Elimination) | 59 | if `Γ; Δ ⟹ C` with cut and cut! then `Γ; Δ ⟹ C` without |
| Theorem 3.10 | 59 | normalisation for natural deductions |
| Theorem 3.11 (Consistency) | 59 | `·; · ⊢ 0 true` is not derivable |
| Theorem 3.12 (Disjunction Property) | 60 | if `·; · ⊢ A ⊕ B true` then `·; · ⊢ A true` or `·; · ⊢ B true` |
| a non-theorem | 60 | `·; A ⊸ (B ⊗ C) ⟹ (A ⊸ B) ⊗ (A ⊸ C)` |

## KOT: Kanovich, Okada, Terui, author's final version for MSCS (2006), §2

Printed page numbers (they are the file's).

| item | page | statement, in brief |
|---|---|---|
| Definition 2.1 | 3 | formulas and sequents of ILL (with ⊥; `Γ ⊢ Δ`, `|Δ| ≤ 1`) |
| Definition 2.2 | 3 | intuitionistic phase space: a commutative monoid with a closure operator, (Cl1) to (Cl4) |
| Figure 1 | 4 | the inference rules of ILL: identity, cut, 16 rules for the connectives, !D, !C, !W, !r |
| Definition 2.4 | 4 | the operations on sets; `!X := Cl(X ∩ I)`, `I := {x ∈ 1 | x·x = x}` |
| Definition 2.6 | 5 | intuitionistic phase model; a formula is satisfied iff `ε ∈ v(A)` |
| Theorem 2.8 | 5 | a family of sets closed under `{y} ⊸ –` induces a closure operator |
| Theorem 2.9 | 6 | `A` is provable in ILL iff satisfied in every intuitionistic phase model |
| Lemma 2.10 | 6 | in the canonical model, `B ∈ v₀(B) ⊆ ⟦ ⊢ B⟧` |
| Remark 2.11 | 6 | with "cut-free provable" in the canonical model, cut elimination at the same time (Okada 1996) |

## Barber: ECS-LFCS-96-347 (1996)

| item | statement, in brief |
|---|---|
| §2, the logic | natural deduction `Γ; Δ ⊢ A` for I, ⊗, ⊸, ! |
| Lemma 2.1 (Intuitionistic Cut) | the cut on the intuitionistic zone is admissible |
| Lemma 2.3 (!-Equivalence) | `!` against the zone |
| Theorem 3 (Conservative Extension), Lemmas 5.1.1, 5.1.2 | `Δ ⊢_ILL t : A` gives `; Δ ⊢_DILL Φ(t) : A`; `Γ; Δ ⊢_DILL t : A` gives `!Γ, Δ ⊢_ILL Ψ(t) : A` |

The survey report quotes these, and the results of the other papers it
read, with pages.
