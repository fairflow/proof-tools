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

**As of 2026-11-23 18:32 GMT.** Of the ten goals: goals 1, 2, 3, 4, 5, 8, 9 and 10
are PROVED; goals 6 and 7 are set aside by the reviewer (`gates.md`, the
entry "which goals stay, and the gates lifted"). Of our own: S1, S2, S3,
`SoundnessCut` and `TreeModelTwoValued` are PROVED. Nothing is OPEN and
nothing is REFUTED. Every PROVED statement is checked by the kernel,
with no `sorry`, within `[propext, Quot.sound]`. The statements of goals
2 to 5 and of the finite model property were not signed before their
proofs: the reviewer lifted the gates, and they are entered as decided
by the operator.

The axiom policy of the development: every theory file within
`[propext, Quot.sound]`.

## Definitions the statements are about

Read these first: no tool checks that they say what the source means.

| definition | Lean name, file | the source's item | seen by the reviewer |
|---|---|---|---|
| formulas; the negation `Ā`; `⊃` | `Form`, `Form.dual`, `Form.imp`, `BrunnlerK/Form.lean` | "Formulas", p. 6 | signed with the rule table, 2026-11-23 |
| nested sequents; a place in a sequent | `NSeq`, `Path`, `NSeq.node?`, `NSeq.setNode`, `BrunnlerK/Sequent.lean` | "Nested sequents", "Sequent contexts, unary", pp. 6–8 | signed with the rule table, 2026-11-23 |
| set sequents: that two are equal | `NSeq.sameSet`, `BrunnlerK/Sequent.lean` | Definition 2.13, p. 14 | signed with the rule table, 2026-11-23 |
| the family of rules: K, and K + cut | `Fam`, `K`, `Kcut`, `BrunnlerK/System.lean` | Figures 2.3 (`fig:kx`), 2.4 (`fig:admissible`) | the rule table: signed 2026-11-23 |
| the family of rules: K° | `FamO`, `BrunnlerK/SystemO.lean` | p. 14 | the rule table: signed 2026-11-23 |
| the proof system: moves, one step | `Move`, `step`, `S`, `BrunnlerK/Proof.lean` | none: the rules of Figure 2.3 as moves | the rule table's last column and its section "The proof system"; put with the report of Adopt |
| the comma `Γ, Δ`; a sequent context `Γ{ }`; filling its hole, `Γ{Δ}`; its depth | `NSeq.comma`, `Ctx`, `Ctx.fill`, `Ctx.depth`, `BrunnlerK/Ctx.lean` | "Sequent contexts, unary", pp. 7–8 | put 2026-11-23 (`gates.md`, the entry "decision 2: the rules in the figure's shape") |
| the depth of a proof; "with a proof of at most the same depth" | `Fam.depth`, `BrunnlerK/Structural.lean`; `∃ d', d'.depth ≤ d.depth` | p. 8, used and not defined (the rule table, D13) | decided by the operator, 2026-11-23 |
| exchange: formulas and boxes permuted inside the nodes | `Exch`, `NSeq.swap`, `NSeq.withForms`, `BrunnlerK/Structural.lean` | none: the source's sequents are multisets | decided by the operator, 2026-11-23 |
| a model with finitely many states; the levels of a tree as a model; the modal depth | `Model.Finite`, `Tree.level`, `Tree.model`, `Form.md`, `BrunnlerK/FiniteModel.lean` | Corollary 2.24 | decided by the operator, 2026-11-23 |
| tools of the proofs, in no statement here: embedding (`NSeq.Sub`, `NSeq.SubR`), counting replaced occurrences (`Cnt`, `Inv`), mapping into (`NSeq.Hom`) | `BrunnlerK/Structural.lean`, `BrunnlerK/Invert.lean`, `BrunnlerK/Contract.lean` | none | not put |
| what holds | the family itself, `Fam` | | the plan, passed 2026-11-23 |
| the corresponding formula `Γ_F` of a sequent | `Form.bot`, `Form.disj`, `NSeq.boxForms`, `NSeq.form`, `BrunnlerK/Semantics.lean` | p. 7 | signed 2026-11-23 (`gates.md`, the entry "Stage 2: the definitions and the statements, first sending") |
| the models, truth in a model, two-valued models, `Valid` | `Model`, `Model.sat`, `Model.TwoValued`, `Valid`, `BrunnlerK/Semantics.lean` | Definition 2.6, p. 12 | the form, with the plan (passed 2026-11-23); the Lean: signed 2026-11-23 |
| a countermodel as data: a finite tree, and the model of finite trees | `Tree`, `treeModel`, `Form.holds`, `Refutation`, `BrunnlerK/Semantics.lean` | Theorem 2.23 (ii) | signed 2026-11-23 |
| truth of a sequent, stated on the sequent: a tool of the proofs, in no statement here; `Model.sat_form` proves that it is truth of `Γ_F` | `NSeq.sat`, `BrunnlerK/Soundness.lean` | none | not put |
| the weight of a sequent, which the search goes down by: in no statement here | `Form.weight`, `NSeq.weight`, `BrunnlerK/Weight.lean` | none (the source's measure is Definition 2.21) | not put |
| the depth of a derivation; `→ⁿ` | not in Lean yet | p. 8, not defined there (the rule table, D13) | at the gate of Prove |
| permutation inside every node, `~` | not in Lean yet | none: the source's sequents are multisets | at the gate of Prove |

## The statements

### S1. The soundness of the moves

    S.SoundT K

that is, for every move `m`, sequent `Γ` and list of sequents `ps`:

    S.step m Γ = .ok ps  →  Each K ps  →  K Γ

`BrunnlerK.step_sound`, in `BrunnlerK/Proof.lean`. Source: none; it joins
`step` to what holds, which is the family. Status: **PROVED**, within
`[propext, Quot.sound]` (the family is into `Type`, so it is a
definition: a function from derivations of the premises to a derivation
of the conclusion). This is not the source's soundness theorem.

### S2. Every derivation of the family is a derivation of the proof system

    K Γ → Nonempty (Der S Γ)

`BrunnlerK.famToDer : FamToDer`, in `BrunnlerK/Proof.lean`, from
`der_of_fam : Fam c Γ → c = false → Nonempty (Der S Γ)` by induction on
the derivation. Source: none. Status: **PROVED**, within
`[propext, Quot.sound]`.

### S3. The rules as the figures print them

For a context `C`, formulas `A`, `B`, a proposition `p`, a sequent `Δ`,
and either family (`c` is `false` for K, `true` for K + cut):

    Fam c (C.fill (p, p̄))                                              (axC)
    Fam c (C.fill A) → Fam c (C.fill B) → Fam c (C.fill (A ⋏ B))        (andC)
    Fam c (C.fill (A, B)) → Fam c (C.fill (A ⋎ B))                      (orC)
    Fam c (C.fill [A]) → Fam c (C.fill □A)                              (boxC)
    Fam c (C.fill (◇A, [Δ, A])) → Fam c (C.fill (◇A, [Δ]))              (diaC)
    Kcut (C.fill A) → Kcut (C.fill Ā) → Kcut (C.fill ∅)                 (cutC)

`BrunnlerK.Fam.axC` and the five after it, in `BrunnlerK/Ctx.lean`; the
fillings are written there with `leaf` and `cons`. Source: Figures 2.3
and 2.4, as printed. Each is a function on derivations, derived from the
constructor of `Fam` for its rule. Status: **PROVED**, within
`[propext, Quot.sound]`. What this does not say: that every instance of
a constructor is an instance of one of these. It is not, as lists:
`fill` puts what fills the hole in front of the node's formulas, so a
rule here acts on the first formula of its node. Exchange (goal 4) is
what would close that.

### Goal 1. Soundness

    K ⊢ Γ  →  Valid Γ

In Lean (`BrunnlerK/Semantics.lean`):

    def Soundness : Prop := ∀ Γ : NSeq, K Γ → Valid Γ

    def Valid (Γ : NSeq) : Prop :=
      ∀ M : Model, M.TwoValued → ∀ s : M.W, M.sat s Γ.form

    def Model.TwoValued (M : Model) : Prop :=
      ∀ (A : Form) (s : M.W), M.sat s A ∨ ¬ M.sat s A

Source: Theorem 2.9 (i), (iii), p. 13 (no label), with Lemma 2.8
(`l:deepsound`). Screened (stage 0, in scratch, not kept): the steps of
`◇k_c` and of `cut` at the root, and the sequent `◇p, [p̄]`, hold in
every two-valued model with no axiom. Screened again (stage 2,
`BrunnlerK/Test/Semantics.lean`): 21 rule instances, at the root and one
and two boxes deep, on 28 564 finite trees; no counterexample. Status:
**PROVED**: `BrunnlerK.soundness`, in `BrunnlerK/Soundness.lean`, within
`[propext, Quot.sound]`. By induction on the proof. A rule that is sound
at a node is sound in a context, by induction on the path
(`NSeq.deep₂`: the source's Lemma 2.8, proved on the models and not
through a Hilbert system). The model's two values are used at the axiom
and at `◇k_c`, and nowhere else.

With it, of our own, for goal 10:

    def SoundnessCut : Prop := ∀ Γ : NSeq, Kcut Γ → Valid Γ

Source: none; the source's Theorem 2.9 is for the rules of K. Screened:
four instances of `cut`, on the same trees. Status: **PROVED**:
`BrunnlerK.soundnessCut`, in `BrunnlerK/Soundness.lean`, within
`[propext, Quot.sound]`. The case of `cut` does not use that the model
is two-valued: a formula and its negation are not both true at a state
of any model (`Model.not_sat_dual`).

The source's form, for comparison (not a goal): `ValidF Γ`, the same with
"every model". `(∀ Γ, K ⊢ Γ → ValidF Γ) → ∀ P : Prop, P ∨ ¬P`, by the
screen of stage 0 together with a proof of `◇p, [p̄]` in K that is by
hand. OPEN as a statement in Lean; set aside as a goal (below).

### Goal 2. Invertibility

    K ⊢ Γ{A ∧ B}  →ⁿ  K ⊢ Γ{A}  and  K ⊢ Γ{B}
    K ⊢ Γ{A ∨ B}  →ⁿ  K ⊢ Γ{A, B}
    K ⊢ Γ{□A}     →ⁿ  K ⊢ Γ{[A]}

In Lean (`BrunnlerK/Invert.lean`), for a context `C` and either family:

    (d : Fam c (C.fill (A ⋏ B))) → ∃ d' : Fam c (C.fill A),      d'.depth ≤ d.depth     (inv_andL_C)
    (d : Fam c (C.fill (A ⋏ B))) → ∃ d' : Fam c (C.fill B),      d'.depth ≤ d.depth     (inv_andR_C)
    (d : Fam c (C.fill (A ⋎ B))) → ∃ d' : Fam c (C.fill (A, B)), d'.depth ≤ d.depth     (inv_or_C)
    (d : Fam c (C.fill □A))      → ∃ d' : Fam c (C.fill [A]),    d'.depth ≤ d.depth     (inv_box_C)

and, more generally, by membership: for a node `Θ` at the path `a` of `Γ`
with the formula in `Θ.forms`, a proof of the premise of the rule there
(`inv_andL`, `inv_andR`, `inv_or`, `inv_box`). Source: Lemma 2.4 (ii),
pp. 10–11 (`l:stradm`). Status: **PROVED**, within `[propext,
Quot.sound]`. All four are instances of one theorem, `Fam.invert`: a
proof of `Γ` gives a proof, no deeper, of any `Γ'` that `Γ` embeds in
with some occurrences of the rule's formula replaced by what the premise
has for it.

### Goal 3. The admissible structural rules

    K ⊢ Γ        →ⁿ  K ⊢ [Γ]          (nec)
    K ⊢ Γ{∅}     →ⁿ  K ⊢ Γ{Δ}         (wk)
    K ⊢ Γ{Δ, Δ}  →ⁿ  K ⊢ Γ{Δ}         (ctr)

In Lean, for either family:

    (d : Fam c Γ)                   → ∃ d' : Fam c [Γ],        d'.depth ≤ d.depth      (nec)
    (d : Fam c (C.fill ∅))          → ∃ d' : Fam c (C.fill Δ), d'.depth ≤ d.depth      (wk)
    (d : Fam c (C.fill (Δ.comma Δ))) → ∃ d' : Fam c (C.fill Δ), d'.depth ≤ d.depth      (ctr)

`nec` and `wk` in `BrunnlerK/Structural.lean`, `ctr` in
`BrunnlerK/Contract.lean`. Source: Lemma 2.4 (i) (`l:stradm`); the rules
are those of Figure 2.4 (`fig:admissible`). Status: **PROVED**, all
three, within `[propext, Quot.sound]`. `nec` is `Fam.lift`. `wk` is an
instance of `Fam.sub` (if `Γ` embeds in `Γ'`, a proof of `Γ` gives one of
`Γ'`, no deeper). `ctr` is an instance of `Fam.hom` (the same where `Γ`
maps into `Γ'`, two boxes possibly into one), which is by induction on
the depth and uses goal 2.

### Goal 4. Exchange

    Γ ~ Γ′  →  (K ⊢ Γ  →ⁿ  K ⊢ Γ′)

In Lean (`BrunnlerK/Structural.lean`), for either family:

    Exch Γ Γ' → ∀ d : Fam c Γ, ∃ d' : Fam c Γ', d'.depth ≤ d.depth                     (exchange)

    inductive Exch : NSeq → NSeq → Prop where
      | refl (Γ) : Exch Γ Γ
      | forms (a) (fs) (hΘ : Γ.node? a = some Θ) (hp : Θ.forms.Perm fs) :
          Exch Γ (Γ.setNode a (Θ.withForms fs))
      | boxes (a) (i) (hΘ : Γ.node? a = some Θ) : Exch Γ (Γ.setNode a (Θ.swap i))
      | trans : Exch Γ₁ Γ₂ → Exch Γ₂ Γ₃ → Exch Γ₁ Γ₃

Source: none; the source's sequents are multisets. `Exch`: the formulas
of a node permuted, two neighbouring boxes of a node exchanged, and one
after another. It is what entitles a list to stand for a multiset (the
rule table, D1, D3). Status: **PROVED**, within `[propext, Quot.sound]`;
an instance of `Fam.sub`.

### Goal 5. The general axiom

    K ⊢ Γ{A, Ā}        for every formula A

In Lean (`BrunnlerK/Identity.lean`), functions, for either family:

    Fam.gaxC (C : Ctx) (A : Form) : Fam c (C.fill (A, Ā))
    Fam.gax (A : Form) (a : Path) : Γ.node? a = some Θ → A ∈ Θ.forms → ∼A ∈ Θ.forms → Fam c Γ

Source: not stated; used on p. 29 (the proof of Theorem 2.38). Status:
**PROVED**, within `[propext, Quot.sound]`. By recursion on `A`.

### Goal 6. K° into K

    K° ⊢ Γ  →  K ⊢ Γ

Source: Lemma 2.14, p. 15 (`l:equiv`), at `X = ∅`. Status: **set aside
by the reviewer**, 2026-11-23 (below). Not in Lean; not attempted.

### Goal 7. Termination

    the search terminates

Source: Lemma 2.22, p. 17 (`l:terminates`), at `X = ∅`, for the source's
search without cyclic leaves. Status: **set aside by the reviewer**,
2026-11-23 (below). Not in Lean; not attempted. The search of goal 8 is
another, and ends by structural recursion on a bound of a weight.

### Goal 8. A proof or a countermodel

    for every Γ:   K ⊢ Γ,   or a finite model M, as data, and a state s
                   with  not  M, s ⊨ Γ_F

In Lean (`BrunnlerK/Semantics.lean`), a type; what is to be given is a
function of this type:

    abbrev ProofOrRefutation : Type := (Γ : NSeq) → K Γ ⊕ Refutation Γ

    structure Refutation (Γ : NSeq) where
      tree : Tree
      refutes : ¬ treeModel.sat tree Γ.form

    inductive Tree where
      | node (val : List Nat) (kids : List Tree)

    def treeModel : Model where
      W := Tree
      R t u := u ∈ t.kids
      V p t := p ∈ t.val

with, of our own, that this model is one `Valid` speaks of:

    def TreeModelTwoValued : Prop := treeModel.TwoValued

Source: Theorem 2.23, pp. 17–19 (`t:completeness`), at `X = ∅`. The
countermodel is a finite tree, as data; it is a state of the model of
all finite trees, whose set of states is not finite. A model with
finitely many states is not stated here (goal 9, second line). The route
proposed is not the source's: see `gates.md`, the fifth entry. Screened:
the empty sequent, `[∅]` and six sequents that are not derivable have
each a refutation of depth at most 2; four derivable ones have none
among 28 564 trees. Status: **PROVED**, both: the function is
`BrunnlerK.proofOrRefutation` (it is `BrunnlerK.search`, in
`BrunnlerK/Search.lean`), and `BrunnlerK.treeModel_twoValued`; within
`[propext, Quot.sound]`. The search: at the root, the rules `∧`, `∨`,
`□` while one applies; then the axiom; then, for each box, the search of
that box with the formulas under the root's diamonds added. A proof of
one box is carried to the whole by `◇k_c` and `Fam.lift`; refutations of
all the boxes are the children of a refutation of the whole
(`NSeq.not_sat_saturated`). Tested (`BrunnlerK/Test/Search.lean`): the
eleven sequents of the exercises file and seven boundary cases.

### Goal 9. Completeness, the finite model property, decidability

    Valid Γ  →  K ⊢ Γ
    if Γ is not valid in some two-valued model, it is not valid in a finite one
    Valid Γ is decidable

In Lean (`BrunnlerK/Semantics.lean`), the first and the third:

    def Completeness : Prop := ∀ Γ : NSeq, Valid Γ → Nonempty (K Γ)

    abbrev ValidDecidable : Type := (Γ : NSeq) → Decidable (Valid Γ)

Source: Theorem 2.23 (i); Corollary 2.24, p. 19; Corollary 2.25, p. 19
(no labels). Status of the first: **PROVED**, `BrunnlerK.completeness`,
with the proof as data (`BrunnlerK.complete : Valid Γ → K Γ`). Status of
the third: **PROVED**, the function `BrunnlerK.validDecidable`. Both in
`BrunnlerK/Completeness.lean`, within `[propext, Quot.sound]`. With goal
1: `Valid Γ ↔ Nonempty (K Γ)` (`valid_iff_derivable`). The decision
reduces in the kernel: `example : ¬ Valid Γ := by decide +kernel` for
the sequents tried. The second, in Lean (`BrunnlerK/FiniteModel.lean`):

    def FiniteModelProperty : Prop :=
      ∀ Γ : NSeq, ¬ Valid Γ →
        ∃ M : Model, M.TwoValued ∧ M.Finite ∧ ∃ s : M.W, ¬ M.sat s Γ.form

    def Model.Finite (M : Model) : Prop := ∃ l : List M.W, ∀ s : M.W, s ∈ l

Status: **PROVED**, `BrunnlerK.finiteModelProperty`, within `[propext,
Quot.sound]`. The model is the refuting tree of goal 8 cut at the modal
depth of `Γ_F`: a state is a level and a tree of that level
(`Tree.model`). It is two-valued (`Tree.model_twoValued`) and its states
are listed (`Tree.model_finite`).

### Goal 10. Cut elimination

    K + cut ⊢ Γ  →  K ⊢ Γ

In Lean (`BrunnlerK/Semantics.lean`):

    def CutElimination : Prop := ∀ Γ : NSeq, Kcut Γ → Nonempty (K Γ)

Source: Theorem 2.35, p. 27 (`t:ce`), at `X = ∅`; and p. 19, "cut
admissibility is an easy corollary of the completeness theorem". The
form is "the rule is admissible", by the short route: from
`SoundnessCut` and `Completeness`. It is not a procedure that removes
cuts from a proof step by step; whether the procedure of §2.1.4 is a
further goal is put for decision in `report-2-2026-11-23.md`. Status:
**PROVED**: `BrunnlerK.cutElimination`, in `BrunnlerK/Completeness.lean`,
within `[propext, Quot.sound]`, with the proof as data
(`BrunnlerK.cutElim : Kcut Γ → K Γ`). The proof it gives is the
search's: the proof with cuts is used only to know that the sequent is
valid.

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
| goal 6, K° into K (Lemma 2.14), and goal 7, termination of the source's search (Lemma 2.22) | no longer on the way to completeness, which is proved by another search; the reviewer's word "Yes continue" to the operator's recommendation (the entry "which goals stay, and the gates lifted") |
| deduction theorems, normalisation, the Church-Rosser property, the disjunction and existence properties | do not apply to this system (the plan's Q2; the third entry) |

## Summary

| | PROVED | REFUTED | OPEN |
|---|---|---|---|
| of the goals from the standing list (cut elimination, 10; the finite model property, in 9) | 2 | 0 | 0 |
| of the other goals (1 to 8, and the rest of 9) | 7 (1, 2, 3, 4, 5, 8, the rest of 9); 6 and 7 set aside | 0 | 0 |
| of our own (S1, S2, S3; `SoundnessCut`, `TreeModelTwoValued`) | 5 | 0 | 0 |
