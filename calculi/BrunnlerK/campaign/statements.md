# Brünnler's system K: the statements

Started in Adopt, 2026-11-23; filled in Prove. Every statement the
campaign will cite, with its status. A statement is entered here, OPEN,
and shown to the reviewer before its proof is begun. Nothing is removed:
a refuted statement stays, with its countermodel. Lemmas on the way are
not entered. Every goal of the plan has an entry.

Status is exactly one of:

* **PROVED**: checked by the kernel, no `sorry`, within the bound of its
  file;
* **REFUTED**: its negation is proved, or a countermodel is checked by the
  kernel; named here;
* **OPEN**: everything else. An OPEN statement is in Lean as a named
  proposition (`def Name : Prop := …`), not as a theorem with `sorry`.

**As of 2026-11-23 every statement below is OPEN, and none is in Lean
yet.** The goals are displayed as the plan has them, in the source's
notation. Each is stated in Lean, in the encoding's terms, and shown to
the reviewer at the gate of Prove, before its proof (`gates.md`, the
third entry; the plan, "Goals"). S1 and S2 are stated when the proof
system is written, after the rule table is signed.

The axiom policy of the development: every theory file within
`[propext, Quot.sound]`.

## Definitions the statements are about

Read these first: no tool checks that they say what the source means.

| definition | Lean name, file | the source's item | seen by the reviewer |
|---|---|---|---|
| formulas; the negation `Ā`; `⊃` | `Form`, `Form.dual`, `Form.imp`, `BrunnlerK/Form.lean` | "Formulas", p. 6 | put with the rule table, 2026-11-23 |
| nested sequents; a place in a sequent | `NSeq`, `Path`, `NSeq.node?`, `NSeq.setNode`, `BrunnlerK/Sequent.lean` | "Nested sequents", "Sequent contexts, unary", pp. 6–8 | put with the rule table, 2026-11-23 |
| set sequents: that two are equal | `NSeq.sameSet`, `BrunnlerK/Sequent.lean` | Definition 2.13, p. 14 | put with the rule table, 2026-11-23 |
| the family of rules: K, and K + cut | `Fam`, `K`, `Kcut`, `BrunnlerK/System.lean` | Figures 2.3 (`fig:kx`), 2.4 (`fig:admissible`) | the rule table: put, not signed |
| the family of rules: K° | `FamO`, `BrunnlerK/SystemO.lean` | p. 14 | the rule table: put, not signed |
| what holds | the family itself, `Fam` | | the plan, passed 2026-11-23 |
| the corresponding formula `Γ_F` of a sequent | not in Lean yet | p. 6 | |
| the models, truth in a model, two-valued models, `Valid` | not in Lean yet | Definition 2.6, p. 12 | the form, with the plan (passed 2026-11-23); the Lean, at the gate of Prove |
| a finite model as data | not in Lean yet | Theorem 2.23 (ii) | at the gate of Prove |
| the depth of a derivation; `→ⁿ` | not in Lean yet | p. 8, not defined there (the rule table, D13) | at the gate of Prove |
| permutation inside every node, `~` | not in Lean yet | none: the source's sequents are multisets | at the gate of Prove |

## The statements

### S1. The soundness of the moves

    S.SoundT K

`step_sound`, not written. Source: none; it joins `step` to what holds,
which is the family. Status: OPEN. With the family into `Type` it is a
definition, and PROVED when the file that holds it builds within its
bound. This is not the source's soundness theorem.

### S2. Every derivation of the family is a derivation of the proof system

    K Γ → Nonempty (Der S Γ)

`FamToDer`, not written. Source: none. Status: OPEN.

### Goal 1. Soundness

    K ⊢ Γ  →  Valid Γ

Source: Theorem 2.9 (i), (iii), p. 13 (no label), with Lemma 2.8
(`l:deepsound`). `Valid Γ`: `M, s ⊨ Γ_F` for every two-valued model `M`
and every state `s` of `M`; `M` is two-valued if for every formula `A`
and state `s`, `M, s ⊨ A` or not `M, s ⊨ A`. Screened (stage 0, in
scratch, not kept): the steps of `◇k_c` and of `cut` at the root, and the
sequent `◇p, [p̄]`, hold in every two-valued model with no axiom. Status:
OPEN.

The source's form, for comparison (not a goal): `ValidF Γ`, the same with
"every model". `(∀ Γ, K ⊢ Γ → ValidF Γ) → ∀ P : Prop, P ∨ ¬P`, by the
screen of stage 0 together with a proof of `◇p, [p̄]` in K that is by
hand. OPEN as a statement in Lean; set aside as a goal (below).

### Goal 2. Invertibility

    K ⊢ Γ{A ∧ B}  →ⁿ  K ⊢ Γ{A}  and  K ⊢ Γ{B}
    K ⊢ Γ{A ∨ B}  →ⁿ  K ⊢ Γ{A, B}
    K ⊢ Γ{□A}     →ⁿ  K ⊢ Γ{[A]}

Source: Lemma 2.4 (ii), pp. 10–11 (`l:stradm`). `→ⁿ`: with a proof of at
most the same depth. Status: OPEN.

### Goal 3. The admissible structural rules

    K ⊢ Γ        →ⁿ  K ⊢ [Γ]          (nec)
    K ⊢ Γ{∅}     →ⁿ  K ⊢ Γ{Δ}         (wk)
    K ⊢ Γ{Δ, Δ}  →ⁿ  K ⊢ Γ{Δ}         (ctr)

Source: Lemma 2.4 (i) (`l:stradm`); the rules are those of Figure 2.4
(`fig:admissible`). Status: OPEN.

### Goal 4. Exchange

    Γ ~ Γ′  →  (K ⊢ Γ  →ⁿ  K ⊢ Γ′)

Source: none; the source's sequents are multisets. `~`: permutation of
the formulas and of the boxes inside every node. It is what entitles a
list to stand for a multiset (the rule table, D1, D3). Status: OPEN.

### Goal 5. The general axiom

    K ⊢ Γ{A, Ā}        for every formula A

Source: not stated; used on p. 29 (the proof of Theorem 2.38). Status:
OPEN.

### Goal 6. K° into K

    K° ⊢ Γ  →  K ⊢ Γ

Source: Lemma 2.14, p. 15 (`l:equiv`), at `X = ∅`. Status: OPEN.

### Goal 7. Termination

    the search terminates

Source: Lemma 2.22, p. 17 (`l:terminates`), at `X = ∅`, for the search
without cyclic leaves (`gates.md`, the second and third entries). The
statement takes its form from the search, which is not written. Status:
OPEN.

### Goal 8. A proof or a countermodel

    for every Γ:   K ⊢ Γ,   or a finite model M, as data, and a state s
                   with  not  M, s ⊨ Γ_F

Source: Theorem 2.23, pp. 17–19 (`t:completeness`), at `X = ∅`. A
function into a sum type. Status: OPEN.

### Goal 9. Completeness, the finite model property, decidability

    Valid Γ  →  K ⊢ Γ
    if Γ is not valid in some two-valued model, it is not valid in a finite one
    Valid Γ is decidable

Source: Theorem 2.23 (i); Corollary 2.24, p. 19; Corollary 2.25, p. 19
(no labels). The second line is the plan's "finite model property" in
words; its form in Lean is put at the gate of Prove. Status: OPEN.

### Goal 10. Cut elimination

    K + cut ⊢ Γ  →  K ⊢ Γ

Source: Theorem 2.35, p. 27 (`t:ce`), at `X = ∅`; and p. 19, "cut
admissibility is an easy corollary of the completeness theorem". First by
the short route; whether the procedure of §2.1.4 is a further goal is
decided at the report of Prove. Status: OPEN.

## Refuted

| statement | the countermodel, or the proof of the negation | where it is checked | what replaced the statement |
|---|---|---|---|
| none | | | |

## Set aside

| result | why, and the reviewer's word (the entry of `gates.md`) |
|---|---|
| Proposition 2.5 at `ρ = k` (`◇k` admissible) | used only by §2.2; the plan's non-goals, passed (the third entry) |
| everything with `X ≠ ∅`; §2.2; §2.3; Chapter 3 | left out at the target's gate (the first entry) |
| soundness for `ValidF` (every model the host logic defines) | it implies excluded middle; the plan's non-goals, passed (the third entry) |
| any statement of complexity | the source has only the bound of Lemma 2.22; the plan's non-goals, passed (the third entry) |
| deduction theorems, normalisation, the Church-Rosser property, the disjunction and existence properties | do not apply to this system (the plan's Q2; the third entry) |

## Summary

| | PROVED | REFUTED | OPEN |
|---|---|---|---|
| of the goals from the standing list (cut elimination, 10; the finite model property, in 9) | 0 | 0 | 2 |
| of the other goals (1 to 8, and the rest of 9) | 0 | 0 | 9 |
| of our own (S1, S2) | 0 | 0 | 2 |
