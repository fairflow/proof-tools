# MALL: the statements

Every statement the campaign cites, displayed as Lean, with its status.
The goals were written as named statements in `MALL/Statements.lean`
(commit `c81bc59`) before any of them was proved; S1 to S3 were entered
in Adopt. Nothing is removed: a refuted statement stays.

Status is exactly one of **PROVED** (checked by the kernel, no `sorry`,
within the bound of its file), **REFUTED** (its negation is proved),
**OPEN** (everything else).

The axiom policy of the development: every theory file within
`[propext, Quot.sound]`, and each ends with
`#axioms_within_file [propext, Quot.sound]`. No exception was needed.
`Γ ~ Δ` is `List.Perm`.

## Definitions the statements are about

Read these first: no tool checks that they say what the source means.

| definition | Lean name, file, length | the source's item | read back |
|---|---|---|---|
| formulas, linear negation | `Form`, `Form.neg` (`Aᗮ`), `MALL/Form.lean`, 50 lines with the notations | Girard, p. 21 | agrees: ten constructors, negation a function by the source's nine equations, "the order of the two components is not reversed" |
| judgments | `List Form`, read as a multiset | Definition 1.15, p. 22; p. 24 | agrees |
| the family of rules | `Fam` (10 rules), `CF` (9, no cut), `MALL/System.lean`, 30 and 25 lines; the figure as it stands, `Lit` (11 rules), `MALL/Source.lean`, 26 lines | Definition 1.15 | the second transcription (`rule-table.md`): agrees. The reading back states each rule as the figure's, "for any Ξ that is a permutation of the displayed conclusion", and notes "no rule for 0 and no separate exchange rule" |
| what holds | `Fam`; `Derivable Γ := Nonempty (Fam Γ)` | | agrees |
| the height | `Fam.height`, `CF.height`: 1 at a rule with no premise, one more than the highest premise otherwise | (ours) | agrees ("leaf height is 1, not 0") |
| phase spaces, duals, facts | `PhaseSpace`, `.dual`, `.IsFact`, `.prod`, `MALL/Semantics.lean`, 33 lines | Definitions 1.1, 1.2, 1.3, 1.8 | agrees. The reader notes the two unit laws are redundant beside commutativity (they are the source's: "1p = p1 = p") |
| phase structures, the interpretation | `PhaseStructure`, `.interp`, 28 lines | Definition 1.14; 1.5, 1.7, 1.8, 1.11 (U2 of the plan) | agrees, clause by clause. The reader notes ⟦**1**⟧ is ⊥^⊥ and ⟦**0**⟧ is M^⊥, "these agree" with {1}^⊥⊥ and ∅^⊥⊥: they are the source's 1.5(ii) and (iv) |
| a sequent in a structure; validity | `parAll`, `PhaseStructure.Sat`, `Valid`, 14 lines | the proof of 1.16, p. 23 (U3); 1.14(iii), (iv) | agrees: "parAll [] = ⊥; parAll [A] = A; right-nested, no trailing ⊥". The reader notes that `Sat` depends on the order of Γ as written: `sat_perm` and `valid_perm` (`MALL/Soundness.lean`) prove that it does not, and were added for this remark. And that the carrier is in `Type` (universe 0): a choice, `decisions.md` |
| a finite structure | `PhaseStructure.Finite`: a list has every phase | Lafont, p. 3 ("finite phase models") | agrees |

The reading back was made on 2026-11-26 by a fresh agent given only an
extract of 230 lines (the definitions above and the statements below, with
comments removed and the statements named T1 to T17), and told to open
nothing else. Its eighteen remarks are entered where they bear, below;
none found a definition or a statement that says something other than
what was meant.

## The statements

### S1. The soundness of the moves

    S.SoundT Fam

`step_sound`, `MALL/Proof.lean`. Source: none; it joins `step` to what
holds. A definition: one constructor of `Fam` for each move. **PROVED.**
This is not the source's soundness theorem.

### S2. Every derivation of the family is a derivation of the proof system

    ∀ Γ : List Form, Fam Γ → Nonempty (Der S Γ)

`FamToDer`, proved by `famToDer`, `MALL/Proof.lean`. Source: none. By
induction on the derivation, for every permutation of its sequent.
**PROVED.**

### S3. The figure as it stands and the family derive the same sequents

    ∀ Γ : List Form, Nonempty (Lit Γ) ↔ Derivable Γ

`lit_iff_fam`, `MALL/Source.lean`, from `Lit.toFam` and `Fam.toLit`.
Source: none; the divergence D1 of the rule table rests on it.
**PROVED.**

### S4. Soundness (Girard, Proposition 1.16)

    ∀ Γ : List Form, Derivable Γ → Valid Γ

`Soundness`, proved by `soundness`, `MALL/Soundness.lean`. Source:
"Linear sequent calculus is sound w.r.t. validity in phase structures",
p. 23. By induction on the derivation, the source's ten cases; a sequent
`⊢ A, Γ` holds in a structure exactly if every phase of the context of
`Γ` is a phase of `A` (`holds_cons`). Screened: with the Boolean
evaluator of `MALL/Screen.lean` over the cyclic groups of order at most
4 (1 605 structures at order 4), ten derivable sequents valid in all,
with a control. Read back: agrees ("Soundness of the calculus with
cut"). **PROVED**, with no excluded middle.

### S5. Completeness (Girard, Theorem 1.17; Lafont, Theorem 1, (2) ⟹ (4))

    ∀ Γ : List Form, Valid Γ → Nonempty (CF Γ)

`Completeness`, proved by `completeness`, `MALL/Completeness.lean`.
Source: "Linear sequent calculus is complete w.r.t. phase semantics",
p. 23. The source's conclusion is a derivation with cut; this is the
stronger form of Lafont's Theorem 1: without cut. By Okada's lemma
(Lafont, Lemma 1), `A• ⊂ {A}⊥` in the syntactical model, proved once for
any phase space with a phase for each formula whose antiphases are
closed under the rules (`RuleModel.okada`). The monoid of sequents is a
quotient of lists by permutation. Screened: eleven sequents that must
not be derivable are each refuted by a cyclic group of order at most 4
(`MALL/Screen.lean`). Read back: agrees ("Completeness, cut-free").
**PROVED**, with no excluded middle. So the direct statement of validity
over all phase structures implies no classical principle here: it is
equivalent to a decidable proposition.

### S6. Cut elimination, as a proposition (Lafont, Theorem 1, (1) ⟹ (4))

    ∀ Γ : List Form, Derivable Γ → Nonempty (CF Γ)

`CutEliminationProp`, proved by `cutEliminationProp`,
`MALL/Completeness.lean`: soundness, then completeness. This proof
ignores the derivation it is given. **PROVED.**

### S7. A cut is admissible without cut, as a function

    (A : Form) → (Γ Δ : List Form) → CF (A :: Γ) → CF (Aᗮ :: Δ) → CF (Γ ++ Δ)

`CutAdmissible`, defined by `cutAdmissible`, `MALL/Cut.lean`. Source:
standing entry 1; the induction is of the kind of LMSS's Theorem A.3
(not read by the operator) and of every textbook. **Which function**:
the cut is pushed up the left derivation to the rules that introduce
`A` (`push`), then up the right one to the rules that introduce `A⊥`,
and where the two meet it is replaced by cuts on the immediate
subformulas (`reduce`). The measure: the size of the cut formula, then
the left derivation, then the right one; every recursion is structural
(`cutN` on a bound of the size), with no sum of heights, since no rule
uses a premise twice. The type alone does not say this (the reader's
remark 5: "bare function types: nothing relates output to input").
Tested: `MALL/CutTest.lean` pins the height and the rules of the result
for each pair of dual rules. Read back: agrees; "demands the conclusion
Γ ++ Δ exactly, not up to permutation" (exchange brings it anywhere).
**PROVED.**

### S8. Cut elimination, as a function

    (Γ : List Form) → Fam Γ → CF Γ

`CutElimination`, defined by `cutElimination`, `MALL/Cut.lean`: by
recursion on the derivation, `cutAdmissible` at each cut. Tested: the
cut of `Source.cutEx` (height 4) is removed, leaving `⊗(ax, ax)` of
height 2. **PROVED.**

### S9. Exchange keeps the height (the source's rule EXCH)

    ∀ (Γ Γ' : List Form) (e : Γ ~ Γ') (d : Fam Γ), (d.exch e).height = d.height

`ExchangeKeepsHeight`, proved by `exchangeKeepsHeight`,
`MALL/Results.lean` (`Fam.height_exch`, `MALL/System.lean`). Read back:
"trivially true: exch only replaces the root's permutation proof …
exchange is built into every rule". That is the point of the encoding,
and the statement is kept to say where exchange lives; what has content
is S3. **PROVED.**

### S10. The logical axiom may be restricted to letters (Girard, p. 22)

    (Γ : List Form) → CF Γ → { d : CF Γ // d.Atomic }

`IdentityExpansion`, defined by `identityExpansion`, `MALL/Results.lean`,
where `d.Atomic` says that every logical axiom of `d` is `⊢ a, a⊥` at a
letter (`CF.Atomic`, `MALL/Statements.lean`). Source: "(It is enough to
restrict it to the case of a propositional letter a.)". **Which
function**: each axiom `⊢ A, A⊥` is replaced by its derivation `idExp A`,
by recursion on `A`. Read back: agrees; "P's axiom clause allows A = p_a
or A = p̄_a; both give the same sequent". **PROVED.**

### S11. Weakening

    ∀ (Γ : List Form) (A : Form), Derivable Γ → Derivable (A :: Γ)

`Weakening`. **REFUTED**: `not_weakening`, `MALL/Results.lean`: `⊢ 1` is
derivable and `⊢ 1, 1` is not (`not_derivable_one_one`, by the decision
procedure, run by the kernel). The cold reader found the same instance
unprompted, and a countermodel: ℤ/2 with antiphases {1}; the screen's
`countermodel [𝟏, 𝟏]` is that structure.

### S12. Contraction

    ∀ (Γ : List Form) (A : Form), Derivable (A :: A :: Γ) → Derivable (A :: Γ)

`Contraction`. **REFUTED**: `not_contraction`: `⊢ a ⊕ a⊥, a ⊕ a⊥` is
derivable and `⊢ a ⊕ a⊥` is not. The cold reader found the same
instance.

### S13. The inversions of ⅋, ⊥ and &

    (A B : Form) → (Γ : List Form) → CF (A ⅋ B :: Γ) → CF (A :: B :: Γ)
    (Γ : List Form) → CF (⊥ :: Γ) → CF Γ
    (A B : Form) → (Γ : List Form) → CF (A & B :: Γ) → CF (A :: Γ) × CF (B :: Γ)

`ParInversion`, `BotInversion`, `WithInversion`, defined by
`parInversion`, `botInversion`, `withInversion`, `MALL/Cut.lean`: each
by a cut (two for &) against a small derivation. Source for &: Girard,
p. 24, (vii). **PROVED.**

### S14. Decidability (LMSS, Theorem 2.2)

    (Γ : List Form) → Decidable (Derivable Γ)
    (Γ : List Form) → Decidable (Valid Γ)

`DerivableDecidable`, `ValidDecidable`, defined by `derivableDecidable`,
`validDecidable`, `MALL/Results.lean`. **Which procedure**: `search`
(`MALL/Decide.lean`), by structural recursion on a bound of the size of
the sequent: the logical axiom, the rule 1, then each formula of the
sequent as principal, and at ⊗ every split of the rest; it returns a
derivation (`Option (CF Γ)`), and `search_complete` proves that it finds
one whenever there is one. With S6 it decides `Derivable`, and with S4
and S5, `Valid`. The reader's remark 4: "`Decidable P` has an element
for every proposition by classical choice, so as types these say
nothing unless the function is required to be axiom-free": the file's
bound excludes `Classical.choice`, and the kernel runs the procedure
(`decide +kernel`, `MALL/DecideTest.lean`: 23 sequents). **PROVED.**

### S15. The disjunction property, for ⊕

    ∀ A B : Form, Derivable [A ⊕ B] → Derivable [A] ∨ Derivable [B]

`DisjunctionProperty`, proved by `disjunctionProperty`,
`MALL/Results.lean`: the last rule of a derivation without cut of
`⊢ A ⊕ B` is 1⊕ or 2⊕. Source: none read; the standing entry 6. Read
back: "restricted to a singleton sequent (no context)": so it must be,
since `⊢ a ⊕ a⊥, a ⊕ a⊥` is derivable. **PROVED.**

### S16. The subformula property (LMSS, Corollary A.4)

    ∀ (Ξ : List Form) (d : CF Ξ), d.All fun Θ => ∀ C ∈ Θ, ∃ D ∈ Ξ, C.IsSub D

`SubformulaProperty`, proved by `subformulaProperty`,
`MALL/Results.lean`, where `d.All P` says that `P` holds of every
sequent of the derivation, and `C.IsSub D` that `C` is a subformula of
`D` (`MALL/Statements.lean`). Read back: agrees; "R is the literal
subformula relation, with no closure under negation": right for a
one-sided calculus without cut. **PROVED.**

### S17. The finite model property (Lafont, Theorem 2, (2) ⟹ (1))

    ∀ Γ : List Form, (∀ S : PhaseStructure, S.Finite → S.Sat Γ) → Derivable Γ

`FiniteModelProperty`, proved by `finiteModelProperty`,
`MALL/FiniteModel.lean`; and `finite_countermodel`: a sequent that is
not derivable is refuted by a finite structure, `finiteModel Γ`. Source:
"A is provable in MALL" iff "A is satisfied by all finite phase models"
(with S4 this is the equivalence). By Lafont's construction with one
change, said in the file: his order `⊑` is replaced by *small*, "the
formulas are subformulas of formulas of Γ and the size is at most that
of Γ", which has the three properties the argument uses. The model's
phases are sequents up to "permutations of each other, or neither is
small"; its antiphases are "derivable without cut, or not small"; it is
the second instance of the construction of S5. Read back: agrees;
"concludes D (with cut) from the weaker hypothesis": as the source
states it; the proof gives a derivation without cut
(`cf_of_sat_finiteModel`). **PROVED**, with no excluded middle.

### S18. One side always answers (level 3 of the Run stage)

    ∀ Γ : List Form, (∃ c, treeCert.check Γ c = true) ∨ noDerivable.check Γ () = true

`decided`, `MALL/Run.lean`. Source: none. `treeCert` is the library's
certifier of trees of moves at `step_sound`; `noDerivable` is the
certifier against derivability whose check is the decision procedure
and whose certificate carries nothing:

    noDerivable : Certify.Certifier (List Form) Unit (fun Γ => Derivable Γ → False)

**PROVED.**

### S19. A finite phase structure that refutes a sequent is a certificate

    noValidBy     : Certify.Certifier (List Form) ZModel (fun Γ => Valid Γ → False)
    noDerivableBy : Certify.Certifier (List Form) ZModel (fun Γ => Derivable Γ → False)

    ∀ (z : ZModel) (Γ : List Form), z.refutes Γ = true → ¬ Valid Γ

`MALL/ModelRun.lean`; `ZModel.not_valid_of_refutes`, `MALL/Model.lean`.
Source: none (Definitions 1.1 to 1.14 on a cyclic group). `Holds` is
`fun Γ => Valid Γ → False`. The certificate `ZModel` is a number `k`
and two lists: the antiphases of ℤ/(k+1), and a set of phases for each
letter, whose closure is the letter's fact. `z.refutes Γ` computes the
interpretation of the par of `Γ` by the clauses of Definition 1.14 and
asks that 0 be not in it; `ZModel.interp_eq` proves the computed sets
are the interpretation in the phase structure `z.str`. Entered when it
was written (10:56), after the plan's other certifiers; screened
against the Boolean evaluator of `MALL/Screen.lean`, which was written
first and is not proved: the two agree on each of that screen's 314
structures on ℤ/1, ℤ/2, ℤ/3 for each of its 21 sequents (a `#guard` of
`MALL/ModelTest.lean`); and by its negative tests (the same file: no
structure on ℤ/1, ℤ/2, ℤ/3 for two letters, 584 of them, is accepted
against four derivable sequents). Not read back (it has no item of the source).
**PROVED.**

### S20. A saturated set of sequents is a certificate, and presents a finite countermodel

    noDerivableBySet : Certify.Certifier (List Form) (List (List Form)) (fun Γ => Derivable Γ → False)
    noValidBySet     : Certify.Certifier (List Form) (List (List Form)) (fun Γ => Valid Γ → False)

    ∀ (D : List (List Form)) (Γ : List Form), refutedBy D Γ = true →
      ∃ S : PhaseStructure, S.Finite ∧ ¬ S.Sat Γ

`MALL/SatRun.lean`; `countermodel_of_refutedBy`, `MALL/Saturated.lean`.
Source: none for the certificate; the structure is Lafont's finite model
(p. 3 of the author's version) with the set `D` in place of "below `A`
and not provable", and the argument is his Lemma 1 (Okada).
`refutedBy D Γ` is `memP D Γ && saturated D`: `Γ` is a member of `D` up
to the order of its formulas, and at every formula of every member the
rule that introduces it has a premise in `D`: the premise of ⅋ and of ⊥;
one of the two of &; both that of 1⊕ and that of 2⊕; for every way to
divide the context of a ⊗, one of the two; and no member is `⊢ a, a⊥`,
`⊢ 1`, or has ⊤. The structure `satModel D`: its phases are the parts of
the members and one phase for every other sequent; its antiphases are
the phases that are not members; the fact of a letter `a` is `{a}⊥`. The
kernel checks the saturation and computes no interpretation. Entered
when it was written (2026-11-26, after the closing page, at the
reviewer's word). Screened: the structure is also computed by tables
(`Table`, `MALL/Refute.lean`, not proved), and for each of the 15
non-theorems of the corpus no member of its set holds in the computed
structure and each of the 23 derivable entries does (`#guard`s of
`MALL/SatTest.lean`); seven negative tests in the kernel, the same file.
Not read back by a cold reader. **PROVED.**

### S21. The certificate is complete: every sequent has a written certificate

    ∀ Γ : List Form, ¬ Derivable Γ → refutedBy (fullRefutation Γ) Γ = true

    ∀ Γ : List Form,
      (∃ c, treeCert.check Γ c = true) ∨ (∃ D, noDerivableBySet.check Γ D = true)

`refutation_complete`, `MALL/Saturated.lean`; `certified`,
`MALL/SatRun.lean`. Source: none. `fullRefutation Γ` is the list of the
small sequents of S17 that have no derivation without cut; it is
saturated because the premises of a rule with a small conclusion are
small, and a sequent all of whose premises under some rule have
derivations has one. That set is for the proof: the producer
(`refuteSet`, `MALL/Refute.lean`, code) returns the far smaller set of
the sequents a failed search visits. This strengthens S18: there the
"no" side was the decision procedure run by the kernel, with nothing
written. An instance is run by the kernel (`full_one_one`,
`MALL/SatTest.lean`). **PROVED.**

### S22. Craig interpolation, with Lyndon's condition, as a function

    structure Interpolant (Γ Δ : List Form) where
      C : Form
      left : CF (C :: Γ)
      right : CF (Cᗮ :: Δ)
      lits : ∀ ℓ ∈ C.lits, ℓᗮ ∈ litsL Γ ∧ ℓ ∈ litsL Δ

    (Γ Δ : List Form) → CF (Γ ++ Δ) → Interpolant Γ Δ

`CraigInterpolation`, defined by `craigInterpolation`, `MALL/Craig.lean`.
Entered as a named type before its proof (commit `e7628b3`), at the
reviewer's word (`decisions.md`). Sources, read after the proof
(`interpolation-sources.md`): D. Roorda, thesis (Amsterdam 1991),
chapter V, §5: interpolation for every fragment with negation, MALL
among them, with the condition "every proposition letter having a
positive (negative) occurrence in I, also has positive (negative)
occurrences in A and in B" (p. 63), by induction on a derivation without
cut; A. Akbar Tabatabai and R. Jalali, arXiv:1808.06256, Definition 5.2
and Theorem 5.7: for a sequent divided in two, with the condition on
letters only. The form here: one-sided, for a division of the sequent
into `Γ` and `Δ`; read two-sided, `Γ⊥ ⊢ C` and `C ⊢ Δ`. `C.lits` is the
list of the literals of `C` (letters and negated letters, formulas being
in negation normal form), so the fourth field is Lyndon's condition; the
condition on letters follows (`Interpolant.letters`). The interpolant
may use the four units. **Which function**: Maehara's, by structural
recursion on the derivation (`CF.interp`), for every division: where the
principal formula is in `Γ`, the rules ⊥, ⅋, ⊕ keep the premise's
interpolant, & gives `C₁ ⊕ C₂`, ⊗ gives `C₁ ⅋ C₂` (the contexts divided
by `split4`, `MALL/Split.lean`), ⊤ gives `𝟎`, an axiom gives `Aᗮ` or `⊥`;
where it is in `Δ`, the dual (`Interpolant.flip`). The interpolant is not
simplified, and two derivations of one sequent can give two interpolants
(`hand₁`, `hand₂` of `MALL/CraigTest.lean`). Written by an agent from the
operator's design; built and inspected by the operator. Tested: sixteen
interpolants pinned by the kernel, the same file. **PROVED.**

### S23. Craig interpolation, for an implication

    ∀ A B : Form, Derivable [Aᗮ, B] →
      ∃ C : Form, Derivable [Aᗮ, C] ∧ Derivable [Cᗮ, B] ∧
        ∀ a ∈ C.letters, a ∈ A.letters ∧ a ∈ B.letters

`CraigForFormulas`, proved by `craigForFormulas`, `MALL/Craig.lean`: cut
elimination, then S22 at the division `([Aᗮ], [B])`. Source: Akbar
Tabatabai and Jalali, Definition 5.1. **PROVED.**

### S24. Uniform interpolation

    ∀ (p : Nat) (Γ : List Form), ∃ I : Form,
      (∀ a ∈ I.letters, a ≠ p ∧ a ∈ lettersL Γ) ∧
      Derivable (Iᗮ :: Γ) ∧
      ∀ Δ : List Form, (∀ a ∈ lettersL Δ, a ≠ p) → Derivable (Γ ++ Δ) → Derivable (I :: Δ)

`UniformInterpolation`, proved by `uniformInterpolation`,
`MALL/Uniform.lean`, with `I := ui p Γ` (`ui_spec`). Entered before its
proof (commit `e7628b3`). Sources, read after the proof: M. Alizadeh,
F. Derakhshan and H. Ono, Review of Symbolic Logic 7 (2014), Theorem 4.3,
for the logic they call InFLₑ ("i.e., MALL"): a formula `A_p(Γ; Δ)` for a
two-sided sequent, with the letters of `Γ, Δ` other than `p`,
`⊢ Γ, A_p ⇒ Δ`, and `⊢ Π ⇒ A_p, Λ` whenever `⊢ Π, Γ ⇒ Δ, Λ` with `Π, Λ`
without `p`; a table of 20 clauses and no written proof for this logic.
A. Akbar Tabatabai and R. Jalali, arXiv:1808.06258, Definition 5.1 and
Theorems 4.3 and 5.9, for a family of calculi that has the one they call
CFLₑ. The statement here is the one-sided form of the first: `Γ` here is
their `Γ ⇒ Δ` moved to one side, and `Δ` here their `Π ⇒ Λ`.
**Which function**: `ui p Γ := uiN p (ssize Γ + 1) Γ`, by recursion on a
bound of the size; `uiN p (n+1) Γ` is the ⊕, simplified, of the
disjuncts of `uiStep`: `⊥` for the empty sequent; `A` for the one
formula `A` without `p`; `𝟏` for `A, A⊥`; for each formula of `Γ` with
the rest `r`: `⊤` for ⊤, the interpolant of the premise for ⊥ and ⅋ and
for each side of ⊕, the & of the two for &, the ⊗ of the two for each
division of `r` for ⊗; and for each division of `Γ` into two parts, the
first formula in the first and the second not empty, the ⅋ of the two
interpolants. This is Pitts's method, of the kind of the first source's
table; it was made before the sources were read, and differs in having
identity at every formula and in the simplification (`sTensor`, `sPar`,
`sWith`, `sBig`: `𝟎` annihilates ⊗ and is dropped from ⊕, units are
removed, a disjunct is taken once, `⊤ ⊗ ⊤` is `⊤`). The proofs:
`uiN_below` by recursion on the bound; `uiN_letters` the same;
`uiN_greatest` by induction on a derivation without cut of `⊢ Γ, Δ`, for
every division and every bound above the size of `Γ`. Screened before
the proof: for 21 formulas `A` and the letter `p`, `∀p A ⊢ A` and
`A ⊢ ∃p A`, and for each of 264 formulas `B` without `p` with at most
one connective, `B ⊢ A` gives `B ⊢ ∀p A` and `A ⊢ B` gives `∃p A ⊢ B`,
by the decision procedure, with no failure; kept as `#guard`s of
`MALL/UniformTest.lean`, where sixteen interpolants are pinned by the
kernel. Its limit: for a sequent of several formulas the interpolant is
long (it is not simplified up to commutativity), and its computation is
exponential in the number of formulas. **PROVED.**

### S25. The uniform interpolants of a formula

    ∀ (p : Nat) (A : Form),
      (∃ U : Form, (∀ a ∈ U.letters, a ≠ p ∧ a ∈ A.letters) ∧ Derivable [Uᗮ, A] ∧
        ∀ B : Form, p ∉ B.letters → Derivable [Bᗮ, A] → Derivable [Bᗮ, U]) ∧
      (∃ E : Form, (∀ a ∈ E.letters, a ≠ p ∧ a ∈ A.letters) ∧ Derivable [Aᗮ, E] ∧
        ∀ B : Form, p ∉ B.letters → Derivable [Aᗮ, B] → Derivable [Eᗮ, B])

`UniformInterpolationForFormulas`, proved by
`uniformInterpolationForFormulas`, `MALL/Uniform.lean`, with
`U := forallP p A = ui p [A]` and `E := existsP p A = (ui p [Aᗮ])ᗮ`.
Source: Akbar Tabatabai and Jalali, Definition 4.1 (one letter, both
interpolants); Alizadeh, Derakhshan and Ono state it for a set of letters
and reduce to one (their Lemma 3.4). **PROVED.**

### S26. Uniform interpolation, with the condition on signs

    ∀ (p : Nat) (Γ : List Form), ∃ I : Form,
      (∀ ℓ ∈ I.lits, ℓ ∈ litsL Γ) ∧
      (∀ a ∈ I.letters, a ≠ p ∧ a ∈ lettersL Γ) ∧
      Derivable (Iᗮ :: Γ) ∧
      ∀ Δ : List Form, (∀ a ∈ lettersL Δ, a ≠ p) → Derivable (Γ ++ Δ) → Derivable (I :: Δ)

    ∀ (p : Nat) (A : Form),
      (∃ U : Form, (∀ ℓ ∈ U.lits, ℓ ∈ A.lits) ∧ … as S25 …) ∧
      (∃ E : Form, (∀ ℓ ∈ E.lits, ℓ ∈ A.lits) ∧ … as S25 …)

`UniformInterpolationLyndon`, `UniformInterpolationLyndonForFormulas`,
proved by `uniformInterpolationLyndon` and
`uniformInterpolationLyndonForFormulas`, `MALL/UniformLyndon.lean`, with
the same interpolants `ui p Γ`, `forallP p A`, `existsP p A` (`ui_lits`,
`forallP_lits`, `existsP_lits`). Source: none found: of the sources
read, none states a condition on signs for a uniform interpolant
(Alizadeh, Derakhshan and Ono, and Akbar Tabatabai and Jalali, state
conditions on variables). Asked by the cold reader of S22 to S25; made a
goal by the session that started this one, not by a word of the reviewer
(`decisions.md`). Entered as named types before its proof (commit
`7fb54d3`). Screened before the proof: both forms, for two letters, on 46
formulas; and, as a control on the polarity of `∃p A`, which is defined
through a negation, the other polarity (literals of `∃p A` among those of
`A⊥`), which fails on 21 of the 46 (`#guard`s of `MALL/UniformTest.lean`).
The proof follows that of the condition on letters: the simplifying
connectives add no literal, and each disjunct of the interpolant is built
from interpolants of sequents whose formulas are formulas of `Γ` or
immediate subformulas of one. For `∃p A` the two negations cancel
(`Form.mem_lits_neg`, `Form.neg_neg`). Not read back by a cold reader.
**PROVED.**

### The reading back of S22 to S25

Made on 2026-11-26 by a fresh agent given only an extract of 124 lines
(the formulas, the two families, `Interpolant` as `Itp`, and the four
statements as T1 to T4, comments removed), told to open nothing else and
not told what the statements were meant to be. It named each correctly
(Craig-Lyndon interpolation in Maehara's form; Craig for formulas;
Pitts's `∀p` of a sequent; the two uniform interpolants of a formula),
checked the polarity side of `Interpolant` on the four divisions of
`⊢ p⊥, p` and found the constants forced (`Γ = [⊤, p]`, `Δ = [q]` needs
`𝟎`), and found no statement false or trivial. Its remarks:

* the formula `I` of S24 stands on the other side from the `C` of S22:
  `I⊥`, not `I`, is the interpolant in the sense of `Interpolant`. So it
  is; the doc comment of S24 says `I` is the weakest formula implying
  the par of `Γ`;
* S22 is about derivations without cut and S23 to S25 about
  derivability with cut: the bridge is cut elimination and exchange (it
  is; S23 says so);
* S24 is an existence statement and discards the function: the function
  is `ui`, and `ui_spec` has the three clauses for it;
* **S24 has no condition on signs** though S22 has one. That every
  literal of `ui p Γ` is a literal of `Γ` is the natural strengthening.
  It was then made a goal and is S26, PROVED;
* the division of S22 is written `Γ ++ Δ`: the function is `CF.interp`,
  which takes any `Ξ ~ Γ ++ Δ`;
* the two ways of saying "without `p`" in S24 and S25 could be one; the
  field `lits` could be named `lyndon`. Not changed.

## Refuted

| statement | the proof of the negation | where it is checked | what replaced the statement |
|---|---|---|---|
| S11, weakening | `⊢ 1` derivable, `⊢ 1, 1` not | `not_weakening`, `MALL/Results.lean` | nothing: the source forbids it (p. 22) |
| S12, contraction | `⊢ a ⊕ a⊥, a ⊕ a⊥` derivable, `⊢ a ⊕ a⊥` not | `not_contraction`, the same file | nothing: the same |

## Not goals, and set aside

| result | why not a goal |
|---|---|
| PSPACE-completeness (LMSS, Theorem 2.12) | needs a theory of machines that the library has not (`plan.md`) |
| normalisation and confluence (Girard, 2.11, 2.12, Section 4) | they are of proof nets, another system: standing entries 4 and 5 |
| deduction theorems; the existence property | do not apply: standing entries 3 and 7 |
| the semantic equations 1.9, 1.12, 1.13 as statements about facts | their syntactic forms are the corpus (`MALL/Corpus/Basic.lean`) |

| interpolation fails for the fragment (⊸, ⅋), the interpolant to stay in the fragment (Roorda, JSL 59, 1994) | the paper was not obtained. Roorda's thesis has the counterexample (p. 78) for his counting form of the condition, and its proof was not read; a refutation in the kernel would decide many candidate interpolants (tens of thousands, by the operator's rough count) on sequents beyond the practical reach of the proved search. Not attempted |

Nothing was set aside by the reviewer.

## Summary

| | PROVED | REFUTED | OPEN |
|---|---|---|---|
| of the goals from the standing list (cut elimination S6-S8; the finite model property S17) | 4 | 0 | 0 |
| of the other goals (S4, S5, S9, S10, S13, S14, S15, S16; S11, S12 as refutations) | 8 | 2 | 0 |
| of our own (S1, S2, S3, S18, S19, S20, S21) | 7 | 0 | 0 |
| added by command after the closing page (interpolation: S22 to S25) | 4 | 0 | 0 |
| added by the starting session's decision (S26) | 1 | 0 | 0 |
