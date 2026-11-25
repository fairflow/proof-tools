# GLS: the statements

Started in Adopt (S1 and S2), filled in Prove. Every statement the
campaign will cite, displayed as Lean, with its status. A statement is
entered here, OPEN, and screened before its proof is begun; the
statement of a goal is also read back (`reference/adopt.md` §5 and §7 of
the skill). Nothing is removed: a refuted statement stays, with its
countermodel. Lemmas on the way are not entered.

Status is exactly one of:

* **PROVED**: checked by the kernel, no `sorry`, within the bound of its
  file;
* **REFUTED**: its negation is proved, or a countermodel is checked by the
  kernel; named here;
* **OPEN**: everything else. An OPEN statement is in Lean as a named
  proposition or type, not as a theorem with `sorry`.

The axiom policy of the development: every theory file within
`[propext, Quot.sound]` (the plan).

## Definitions the statements are about

Read these first: no tool checks that they say what the source means.
"Read back" is the cold reader's reading of 2026-11-25 (below).

| definition | Lean name, file | the source's item | read back |
|---|---|---|---|
| formulas | `GLS.Form`, `GLS/Form.lean` | `MPropF`, the Coq file l. 41 | agrees: "A ::= pₙ \| ⊥ \| A → B \| □A" |
| sequents | `GLS.Seq`, `GLS/Form.lean` | `rel (list (MPropF V))` | agrees: "a pair of lists … Lists, not multisets or sets" |
| the boxed part of an antecedent | `GLS.xbox`, `GLS.Form.xb`, `GLS/Form.lean` | `XBoxed_list (top_boxes Γ)`, l. 154, 161 | agrees: "deletes every non-boxed formula and replaces each occurrence of □B by the two formulas B, □B (in that order, in place, multiplicities kept)" |
| the family of rules of GLS | `GLS.Fam`, `GLS/System.lean` | `GLS_rules`, l. 306 | the second transcription, in the rule table: no difference. The reading back drew the five rules as the table has them |
| the family of rules of PSGLS | `GLS.PSFam`, `GLS/System.lean` | `PSGLS_rules`, l. 314 | the same; "The → rules have no such restriction" |
| the height of a derivation | `GLS.Fam.height`, `GLS/System.lean` | `derrec_height`, `general/dd_fc.v` l. 131 | agrees: "a rule with no premises … gets 1, not 0" |
| what holds: the family | `GLS.Fam` | | |
| the models, and truth in a model | `GLS.Model`, `Model.sat`, `Model.GL`, `Model.TwoValued`, `Model.Finite`, `Model.satSeq`, `GLS/Semantics.lean` | **none in the source's Coq files**; the operator's, the usual semantics of GL | agrees with what was meant, clause by clause; `GL`: "R is transitive, and the converse of R is well-founded in Lean's accessibility sense … constructively stronger than 'no infinite chain'"; a model may be empty |
| validity | `GLS.Valid`, `GLS/Semantics.lean` | none in the source | agrees, and the reader names the restriction: "Valid quantifies only over GL models in which every formula is true-or-not at every world. With excluded middle every model is TwoValued … Without excluded middle … T1 (soundness) is a weaker claim than the textbook one and T3 (completeness) a stronger one". This is the choice of `decisions.md`, "what valid means" |
| a finite model as data | `GLS.Tree`, `Tree.desc`, `treeModel`, `subModel`, `Form.holds`, `Seq.refutedAt`, `Refutation`, `GLS/Semantics.lean` | none in the source | agrees: "W = the type of all finite trees; R t u iff … u is equal as a tree to some proper subtree of t … Worlds are trees up to structural equality, not node positions"; `Refutation`: "the negation of the implication … not … 'all of Γ true and all of Δ false'" (the two are proved to agree: `refutedAt_of_not_satSeq`, `not_satSeq_of_refutedAt`, `GLS/TreeModel.lean`) |
| the premise relation of PSGLS | `GLS.PSPrem`, `GLS/Semantics.lean` | the premises of `PSGLS_rules` | agrees: "p is a premise of some instance of a premise-bearing rule of Fam2 with conclusion c" |

**The reading back** (`reference/adopt.md` §7 of the skill). Made on
2026-11-25 by a fresh agent given one file: an extract of
`GLS/Form.lean`, `GLS/System.lean` and `GLS/Semantics.lean` with every
comment taken out and the seventeen statements renamed `T1` to `T17`
(`PSFam` renamed `Fam2`, `PSPrem` renamed `Prem2`); it opened nothing
else. Its reading of each statement is quoted in the entry. It differed
from what was meant **nowhere**. It raised fourteen points; those that
bear on a statement are in its entry, and three are answered here:

* *"T4 and T5 have content only if they are proved without classical
  choice"*: so they are; the file `GLS/Completeness.lean` ends with the
  bound `[propext, Quot.sound]`, and the kernel evaluates
  `validDecidable` (`GLS/SearchTest.lean`).
* *"Nothing in T1–T17 states that treeModel is GL or TwoValued, that
  Form.holds agrees with treeModel's truth, or that a Refutation of s
  implies ¬Valid(s) or gives a finite countermodel"*: true of the
  seventeen. They are theorems of `GLS/TreeModel.lean`, entered below as
  S20, since the closing page cites them.
* *The identification*: the reader named the calculus (GLS, with PSGLS
  "of Goré, Ramanayake and Shillito") from the rules alone, "from
  memory, not from the file".

**When the entries were written.** The statements were in Lean as named
propositions and types, the screens had run, and the reading back had
been started, before any proof of a goal was begun. The entries S3 to
S10 of this document were written after their proofs were checked, and
the reading back came in while the proofs of goals 1 and 2 were being
written: for those entries this is a record written afterwards. It
found no difference, so nothing was built again.

**The screens** are in `GLS/Screen.lean`, a module that fails the build
if one fails: an untrusted bounded search (`within n s`: a derivation of
height at most `n`, every rule tried), 1 024 small sequents (`seqsSmall`:
both sides of at most two of `p, q, ⊥` or one of nineteen formulas of
at most two connectives), 12 321 smaller ones (`seqs1`), and 964 worlds
(the subtrees of trees of depth at most 2 over `p`, `q`). Of the 1 024,
the search derives 385 within height 8. One control: the comparison of
least heights says no where it should.

## The statements

### S1. The soundness of the moves

    S.SoundT Fam
      :=  ∀ m j ps, S.step m j = .ok ps → Each Fam ps → Fam j

`step_sound`, `GLS/Proof.lean`. Source: none; it joins `step` to what
holds. With the family into `Type` it is a definition. Status:
**PROVED** (the file builds within `[propext, Quot.sound]`). This is not
the source's soundness theorem.

### S2. Every derivation of the family is a derivation of the proof system

    Fam j → Nonempty (Der S j)

`FamToDer`, proved as `famToDer`, `GLS/Proof.lean`. Source: none. Status:
**PROVED**, within `[propext, Quot.sound]`: a node for each constructor.
So `step` refuses no instance of a rule of `Fam`.

### S3. Soundness (goal 1)

    ∀ s : Seq,  Fam s → Valid s

`Soundness`, proved as `soundness`, `GLS/Soundness.lean`. Source: not in
the source's Coq files; literature, Sambin and Valentini 1982 (not
read). Screened: rule by rule, on `seqs1` and `seqsSmall`, no world of
the 964 refutes a conclusion while refuting no premise (for GLR: while
no descendant refutes the premise); on the whole, no sequent of the
1 024 that the bounded search derives is refuted at a world. Read back:
agrees ("∀ s. if there is a Fam-derivation of s then Valid(s)").
Status: **PROVED**, within `[propext, Quot.sound]`. The case of ImpR is
the one that uses that the model is two-valued.

### S4. Completeness, as data (goal 2)

    (s : Seq) → Fam s ⊕ Refutation s

`ProofOrRefutation`, defined as `proofOrRefutation`, `GLS/Search.lean`.
Source: none in the Coq files; the construction of the countermodel is
this campaign's (the plan, Q3). Screened: every sequent of the 1 024
that the bounded search does not derive within height 8 is refuted at
one of the 964 worlds; the plan's five non-theorems are refuted, its
three theorems derived. Read back: agrees ("a function taking a sequent
s and returning either a Fam-derivation of s or a Refutation of s … The
sum is not stated to be exclusive": it is exclusive by S3 and S20).
Status: **PROVED**, within `[propext, Quot.sound]`. It is `search` at a
number of steps computed from the sequent (`fuel`), by structural
recursion: the kernel evaluates it (`GLS/SearchTest.lean`).

### S5. Completeness (goal 2)

    ∀ s : Seq,  Valid s → Nonempty (Fam s)

`Completeness`, proved as `completeness`, `GLS/Completeness.lean`.
Screened and read back with S4 ("∀ s. Valid(s) → there exists a
Fam-derivation of s"). Status: **PROVED**, within `[propext,
Quot.sound]`.

### S6. Decidability (goal 2)

    (s : Seq) → Decidable (Valid s)
    (s : Seq) → Decidable (Nonempty (Fam s))

`ValidDecidable`, `DerivableDecidable`, defined as `validDecidable`,
`derivableDecidable`, `GLS/Completeness.lean`. Read back: agrees, with
the caution above. Status: **PROVED**, within `[propext, Quot.sound]`.

### S7. The finite model property (goal 2; entry 2 of the standing list)

    ∀ s : Seq,  (∀ M : Model, M.GL → M.TwoValued → M.Finite → ∀ w : M.W, M.satSeq w s) → Valid s

`FiniteModelProperty`, proved as `finiteModelProperty`,
`GLS/Completeness.lean`. Source: holds of the logic, proved elsewhere
(Segerberg 1971, as reported; not read). Read back: agrees ("the
positive form of the finite model property … not 'every non-valid
sequent has a finite countermodel'; classically the same"). The other
form is proved beside it: `finite_countermodel`, a sequent that GLS does
not derive is false at a world of a finite two-valued model of GL.
Status: **PROVED**, within `[propext, Quot.sound]`.

### S8. The identity on every formula (goal 2, on the way)

    (A : Form) → {Γ Δ : List Form} → A ∈ Γ → A ∈ Δ → Fam (Γ ⇒ Δ)

`Identity`, defined as `Fam.id`, `GLS/Identity.lean`. Source:
`Id_all_form`, the Coq file l. 331. Screened: each of the nineteen small
formulas on both sides is derived by the bounded search. Read back:
agrees ("general identity / identity expansion"). Status: **PROVED**,
within `[propext, Quot.sound]`, by the source's recursion on the
formula.

### S9. The termination of proof search in PSGLS (goal 2, on the way)

    WellFounded PSPrem

`PSTermination`, proved as `psTermination`, `GLS/Measure.lean`. Source:
`PSGLS_termin` and `RA_mhd_decreases`, `PSGLS_termination.v` l. 1563,
1605, **in another form**: the source shows that every sequent has an
unfinished PSGLS derivation of maximal height, and that this height
falls from conclusion to premise; here the premise relation is
well-founded. The source's measure is used (the usable boxes, then the
implications), joined in one number relative to a list of boxed
formulas (`weight`, `PSPrem.step`). Read back: agrees ("every sequent is
accessible, i.e. there is no infinite sequence c₀, c₁, c₂, … with each
cᵢ₊₁ a Fam2-premise of cᵢ … termination of every backward path, not of
one strategy"). Status: **PROVED**, within `[propext, Quot.sound]`.
`mhd` itself is not defined: "Not goals", below.

### S10. Cut admissibility (goal 3; entry 1 of the standing list)

    (A : Form) → (Γ0 Γ1 Δ0 Δ1 : List Form) →
      Fam (Γ0 ++ Γ1 ⇒ Δ0 ++ A :: Δ1) → Fam (Γ0 ++ A :: Γ1 ⇒ Δ0 ++ Δ1) →
      Fam (Γ0 ++ Γ1 ⇒ Δ0 ++ Δ1)

`CutAdmissible`, defined as `cutAdmissible`, `GLS/Completeness.lean`.
Source: `GLS_cut_adm`, `GLS_additive_cut.v` l. 692, of which this is the
statement letter for letter. Screened: for 16 antecedents, 15
succedents and the nineteen small formulas as cut formula, wherever the
bounded search derives both premises within height 7 it derives the
conclusion within 9. Read back: agrees ("admissibility of cut,
context-sharing form … Its type does not distinguish a syntactic
cut-elimination argument from one going through T1 and T2"). Status:
**PROVED**, within `[propext, Quot.sound]`, **by the semantic route**:
the two premises are valid (S3), so the conclusion is, so the search
(S4) returns a derivation of it. That derivation is not made from the
two given ones. The source's construction is S19.

### S11 to S18. The source's structural theorems, with heights (goal 4)

Each is a function that returns a derivation no higher than the one it
is given. Source: the Coq files named. Screened, each on `seqsSmall` by
least heights up to 7 (and the inversions also on 300 of `seqs1`): no
failure. Read back: each agrees; the reader's names are quoted.

    S11  Exchange        (d : Fam (Γ ⇒ Δ)) → Γ.Perm Γ' → Δ.Perm Δ' → { d' : Fam (Γ' ⇒ Δ') // d'.height ≤ d.height }
    S12  WeakeningL      (A) → (d : Fam (Γ0 ++ Γ1 ⇒ Δ)) → { d' : Fam (Γ0 ++ A :: Γ1 ⇒ Δ) // d'.height ≤ d.height }
    S13  WeakeningR      (A) → (d : Fam (Γ ⇒ Δ0 ++ Δ1)) → { d' : Fam (Γ ⇒ Δ0 ++ A :: Δ1) // d'.height ≤ d.height }
    S14  InversionImpR   (A B) → (d : Fam (Γ ⇒ Δ)) → A ⟶ B ∈ Δ → { d' : Fam (A :: Γ ⇒ B :: Δ.erase (A ⟶ B)) // d'.height ≤ d.height }
    S15  InversionImpL   (A B) → (d : Fam (Γ ⇒ Δ)) → A ⟶ B ∈ Γ →
                           { d' : Fam (Γ.erase (A ⟶ B) ⇒ A :: Δ) // d'.height ≤ d.height } ×
                           { d' : Fam (B :: Γ.erase (A ⟶ B) ⇒ Δ) // d'.height ≤ d.height }
    S16  ContractionL    (A) → (d : Fam (Γ0 ++ A :: Γ1 ++ A :: Γ2 ⇒ Δ)) → { d' : Fam (Γ0 ++ A :: Γ1 ++ Γ2 ⇒ Δ) // d'.height ≤ d.height }
    S17  ContractionR    (A) → (d : Fam (Γ ⇒ Δ0 ++ A :: Δ1 ++ A :: Δ2)) → { d' : Fam (Γ ⇒ Δ0 ++ A :: Δ1 ++ Δ2) // d'.height ≤ d.height }

Sources: S11 `GLS_hpadm_list_exch_L`, `_R` (`GLS_exch.v` l. 2124, 2038),
there for two blocks of a list exchanged, here for any permutation; S12,
S13 `GLS_wkn_L`, `GLS_wkn_R` (`GLS_wkn.v` l. 226, 374), letter for
letter; S14, S15 `ImpR_ImpL_hpinv` (`GLS_inv_ImpR_ImpL.v` l. 63), with
the premises in this family's form; S16, S17 `GLS_hpadm_ctr_L`, `_R`
(`GLS_ctr.v` l. 1051, 1064), letter for letter ("the later occurrence is
the one removed", the reader). Names in Lean, all in
`GLS/Semantics.lean`: `Exchange`, `WeakeningL`, `WeakeningR`,
`InversionImpR`, `InversionImpL`, `ContractionL`, `ContractionR`.
Status: **OPEN**, each.

### S18. The two systems derive the same sequents (goal 5)

    (s : Seq) → (Fam s → PSFam s) × (PSFam s → Fam s)

`PSEquivalent`, `GLS/Semantics.lean`. Source: none found in the Coq
files as a theorem (IdB is derived there by `Id_all_form`); the
statement is the operator's. Read back: agrees ("No claim that they are
mutually inverse, and no height relation"). Status: **OPEN**.

### S19. Cut admissibility, by the source's induction (goal 6)

The type of S10. A second definition of that type, which makes its
derivation from the two given ones, by induction on the size of the cut
formula and then on the termination measure. Source:
`GLS_cut_adm_main`, `GLS_additive_cut.v` l. 32. Status: **OPEN** (no
such definition yet).

### S20. A refutation is a finite countermodel (our own)

    treeModel.GL        treeModel.TwoValued
    ∀ A t,  A.holds t = true ↔ treeModel.sat t A
    Refutation s → ¬ Valid s
    Refutation s → ∃ M : Model, M.GL ∧ M.TwoValued ∧ M.Finite ∧ ∃ w : M.W, ¬ M.satSeq w s

`treeModel_GL`, `treeModel_twoValued`, `holds_iff`,
`Refutation.not_valid`, `Refutation.finite`, `GLS/TreeModel.lean`.
Source: none. They say that the trees of S4 are countermodels in the
sense of `Valid`. Not read back as statements (their definitions were).
Status: **PROVED**, within `[propext, Quot.sound]`.

### S21. The certifiers against validity and against derivability (stage 3; our own)

Entered before their proofs (rule R10 of `lean-certify`: statements
first). No item of the source, so not read back.

    Spec  := Seq            Cert := Tree (a finite tree, as data)
    check s t := s.refutedAt t
    Holds s := Valid s → False                        (noValid)
    Holds s := Nonempty (Fam s) → False               (noDerivable)
    sound : ∀ s t, s.refutedAt t = true → Valid s → False
    sound : ∀ s t, s.refutedAt t = true → Nonempty (Fam s) → False

`noValid`, `noDerivable`, `GLS/Run.lean`. No budget in `Holds`. Screened
(`GLS/Screen.lean`): no sequent of the 1 024 that the bounded search
derives is accepted with any of the 964 trees; the plan's five
non-theorems are each accepted with one. Status: OPEN until
`GLS/Run.lean` builds.

### S22. One side always answers (stage 3, level 3; our own)

    ∀ s : Seq,  (∃ c, treeCert.check s c = true) ∨ (∃ t, noValid.check s t = true)

`decided`, `GLS/Run.lean`; and that the engine's producer answers `pass`
for every derivable sequent (`Certify.Engine.Complete`). Status: OPEN
until `GLS/Run.lean` builds.

### S23. Trees of moves over sets, checked for derivability (stage 3; our own)

Entered before its proof (R10). Why it is wanted: `decisions.md`,
"Stage 3: a certifier over sets". No item of the source, so not read
back.

    Spec := Seq        Cert := Cert SS  (a tree of moves, as for S)
    SS   := the proof system of GLS's moves in which each premise has its
            repeated formulas removed:
            stepSet m j := if (m.rule j).ok then .ok ((m.rule j).prems.map Seq.dedup) else .error …
    Holds s := Nonempty (Fam s)
    the one obligation:   SS.Sound Derivable
      :=  ∀ m j ps, SS.step m j = .ok ps → (∀ p ∈ ps, Derivable p) → Derivable j
    sound : ∀ s c, Cert.check (S := SS) s c = true → Nonempty (Fam s)

and, of the type of S6, a second decision of derivability:

    (s : Seq) → Decidable (Nonempty (Fam s))

by a search over sets whose answer is checked (by this certifier, or by
`noDerivable`), with the procedure of S6 where a check fails.
`stepSet_sound`, `setCert`, `derivableDecidableFast`, `GLS/SetSearch.lean`.
No budget in `Holds`. The obligation rests on weakening (S12, S13, in
the general form `Fam.wk`): a derivation of a sequent less its repeated
formulas gives one of the sequent. Screened (`GLS/SetSearchTest.lean`):
on the 1 024 small sequents, for each move that applies, if the bounded
search derives every premise with its repetitions removed then it
derives the conclusion. Status: OPEN until `GLS/SetSearch.lean` builds.

## Refuted

None.

## Not goals, and set aside

| result | not a goal (the plan's reason), or set aside |
|---|---|
| `mhd`, the maximal height of an unfinished PSGLS derivation (`PSGLS_termination.v` l. 1598) | not a goal: a lemma on the source's route; termination is S9, and the induction of S19 can be on the measure itself. Decided again if S19 needs it |
| the decidability of the applicability of each rule (`GLS_PSGLS_dec.v`) | not a goal of Prove: it is `step`, with S1 and S2 |
| a cut-elimination procedure for a calculus with a cut rule | not a goal: a second family; the source's Coq files state admissibility. To be looked at again when the prose is read |
| interpolation; arithmetical completeness; a Hilbert system for GL | not goals: about other systems |

## Summary

| | PROVED | REFUTED | OPEN |
|---|---|---|---|
| of the goals from the standing list (S7, S10) | 2 | 0 | 0 |
| of the other goals (S3 to S6, S8, S9; S11 to S19) | 6 | 0 | 9 |
| of our own (S1, S2, S20) | 3 | 0 | 0 |
