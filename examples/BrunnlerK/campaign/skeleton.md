# Brünnler's system K: the source's numbered results

Source: K. Brünnler, *Nested Sequents*, arXiv:1004.1845 v1, Chapter 2.
Written by hand from the PDF (the page images), 2026-11-23. **Labels: not
known.** The TeX source was not fetched, so every citation is the printed
number and page of this version. Statements are shortened; `X` is a
subset of `{d, t, b, 4, 5}`, and the campaign reads everything at
`X = ∅`.

"Bears on K" says whether the item says anything at `X = ∅`.

## §2.1 Modal axioms as logical rules

| item | page | statement, shortened | bears on K |
|---|---|---|---|
| Figure 2.1 | 5 | frame conditions and modal axioms; `k: □(A ∨ B) ⊃ (□A ∨ ◇B)` | the k line |
| Figure 2.2 | 6 | the modal cube | no |
| Example 2.1 | 8 | filling a unary context: `A, [[B], { }]` with `C, [D]` | yes |
| Example 2.2 | 9 | filling a binary context | no (only `◇5_c` uses one) |
| Figure 2.3 | 10 | System `K + {◇d_c, ◇t_c, ◇b_c, ◇4_c, ◇5_c}`: the axiom `Γ{p, p̄}` and the rules `∧`, `∨`, `□`, `◇k_c`, then the five further rules | the first five lines |
| Figure 2.4 | 10 | `nec`, `wk`, `ctr`, `cut` | yes |
| Example 2.3 | 9–10 | a proof in system K of `□(a ∨ b) ⊃ (□a ∨ ◇b)` | yes: the only worked proof in K |
| Lemma 2.4 | 10–11 | for each `K + ◇X_c`: (i) `nec`, `wk`, `ctr` are depth-preserving admissible; (ii) all its rules are depth-preserving invertible | yes |
| Figure 2.5 | 12 | the diamond rules without built-in contraction | the `◇k` line |
| Proposition 2.5 | 11–12 | for `ρ ∈ {k, d, t, b, 4, 5}`: (i) `◇ρ` is derivable for `{◇ρ_c, wk}` and admissible for `K + ◇ρ_c`; (ii) `◇ρ_c` is derivable for `{◇ρ, ctr}` | at `ρ = k` |
| Definition 2.6 | 12 | frames (a nonempty set of states and a relation), models, `⊨`, validity in a model, in a frame, validity; `X`-frames | yes |
| Lemma 2.7 | 12 | `◇5_c` is derivable for `{◇5₁, ◇5₂, ◇5₃, ctr}` | no |
| Lemma 2.8 | 13 | if `A ⊃ B` is `X`-valid then `Γ{A} ⊃ Γ{B}` is `X`-valid | yes |
| Theorem 2.9 | 13 | Soundness: (i) each rule of K preserves validity; (ii) each `◇ρ_c` preserves `ρ`-validity; (iii) `K + ◇X_c ⊢ Γ` implies `Γ` is `X`-valid | (i) and (iii) |
| Fact 2.10 | 13 | two incomplete combinations of rules | no |
| Definition 2.11 | 14 | 45-closed sets of axiom names | no (`∅` is 45-closed) |
| Definition 2.12 | 14 | immediate subtree, proper subtree, subtree, `st(Γ)`; a formula *in* and *inside* a sequent | yes |
| Definition 2.13 | 14 | the set sequent of a sequent | yes |
| (unnumbered) | 14–15 | the systems `S°`: `∧°`, `∨°`, `□°`, `◇d_c°`, each keeping its main formula; `□°` only where the node has no child containing `A`; every rule with the proviso that each premise's set sequent differs from the conclusion's | yes, but for `◇d_c°` |
| Lemma 2.14 | 15 | `(K + ◇X_c)° ⊢ Γ` implies `K + ◇X_c ⊢ Γ` | yes |
| Definitions 2.15, 2.16 | 15 | closures of a relation; euclidean connections | no |
| Lemma 2.17 | 15–16 | `→^X` is well defined | no |
| Definition 2.18, Lemma 2.19 | 16 | serial closure, and that it keeps frame conditions | no |
| Definition 2.20 | 16 | a cyclic leaf of a sequent; a finished node, a finished sequent; the procedure `prove(Γ, X)`; it succeeds, it fails | yes |
| Definition 2.21 | 16 | the size of a sequent; `sf(Γ)` | yes |
| Figure 2.6 | 17 | the algorithm `prove(Γ, X)` | yes |
| Lemma 2.22 | 17 | Termination: `prove(Γ, X)` terminates after at most `2^|sf(Γ)|` iterations | yes |
| Theorem 2.23 | 17–19 | Completeness, for 45-closed `X`: (i) `Γ` `X`-valid implies `K + ◇X_c ⊢ Γ`; (ii) if `prove(Γ, X)` fails there is a finite `X`-frame in which `Γ` is not valid | yes; of Claim 3 only the case K |
| Corollary 2.24 | 19 | Finite model property | yes |
| Corollary 2.25 | 19 | Decidability of `X`-validity | yes |
| Definition 2.26 | 19 | the depth of a formula | yes |
| Definition 2.27 | 20 | cut rank; `cut_r`; cut-rank preserving | yes |
| Definition 2.28 | 20 | the rule `Y-cut`, for `Y ⊆ {4, 5}` | at `Y = ∅` it is `cut` |
| Fact 2.29 | 20 | properties of `Y-cut` | its first line |
| Figure 2.7 | 21 | the modal structural rules `[d]`, `[t]`, `[b]`, `[4]`, `[5]` | no |
| Lemma 2.30 | 21 | for `K + Y`, `Y ⊆ ◇X_c ∪ {[d]}`: (i) `nec`, `wk`, `ctr` are depth- and cut-rank preserving admissible; (ii) all rules depth- and cut-rank preserving invertible | yes |
| Lemma 2.31 | 21–24 | admissibility of the modal structural rules | no |
| Definition 2.32, Lemma 2.33 | 24 | the rule `Y-str` and its admissibility | at `Y = ∅` the rule changes nothing |
| Lemma 2.34 | 24–27 | Reduction Lemma: a `cut_{r+1}` (and a `Y-cut_{r+1}`) whose premises are proved in `K + Z + cut_r` has its conclusion provable in `K + Z + cut_r` | yes, part (i) |
| Theorem 2.35 | 27 | Cut-Elimination, for 45-closed `X`: `K + ◇X_c + cut ⊢ Γ` implies `K + ◇X_c ⊢ Γ` | yes |

## §2.2 and §2.3 (left out at the target gate)

Figure 2.8 (p. 28), system `K_c + {[d], [t], [b], [4], [5]}`; Theorems
2.36 (soundness), 2.37 (cut elimination), 2.38 (completeness, by a
Hilbert system and cut); Lemmas 2.39 to 2.44; Proposition 2.45;
Definition 2.46; Fact 2.47; Lemmas 2.48 to 2.52; Proposition 2.53
(pp. 28–38). Figures 2.10 and 2.11, Propositions 2.54 and 2.55, Corollary
2.56, Remark 2.57 (pp. 39–41): the deep inference systems.
