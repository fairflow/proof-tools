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
| formulas | `GLS.Form`, `GLS/Form.lean` | `MPropF`, the Coq file l. 41; the thesis, "connectives {⊥, →, □}", p. 168 | agrees: "A ::= pₙ \| ⊥ \| A → B \| □A" |
| sequents | `GLS.Seq`, `GLS/Form.lean` | `rel (list (MPropF V))` | agrees: "a pair of lists … Lists, not multisets or sets" |
| the boxed part of an antecedent | `GLS.xbox`, `GLS.Form.xb`, `GLS/Form.lean` | `XBoxed_list (top_boxes Γ)`, l. 154, 161 | agrees: "deletes every non-boxed formula and replaces each occurrence of □B by the two formulas B, □B (in that order, in place, multiplicities kept)" |
| the family of rules of GLS | `GLS.Fam`, `GLS/System.lean` | `GLS_rules`, l. 306; the thesis, Figure 12.1, p. 171 | the two second transcriptions, in the rule table: no difference. The reading back drew the five rules as the table has them |
| the family of rules of PSGLS | `GLS.PSFam`, `GLS/System.lean` | `PSGLS_rules`, l. 314; the thesis, (IdentBox) and (NoInit), p. 178 | the same; "The → rules have no such restriction" |
| the height of a derivation | `GLS.Fam.height`, `GLS/System.lean` | `derrec_height`, `general/dd_fc.v` l. 131 | agrees: "a rule with no premises … gets 1, not 0" |
| what holds: the family | `GLS.Fam` | | |
| the models, and truth in a model | `GLS.Model`, `Model.sat`, `Model.GL`, `Model.TwoValued`, `Model.Finite`, `Model.satSeq`, `GLS/Semantics.lean` | none in the source's Coq files; **the thesis, Definitions 12.2.2 and 12.2.3, p. 168** (found after they were written: `decisions.md`, 13:21). `TwoValued`, `Finite` and `satSeq` are the operator's | agrees with what was meant, clause by clause; `GL`: "R is transitive, and the converse of R is well-founded in Lean's accessibility sense … constructively stronger than 'no infinite chain'"; a model may be empty |
| validity | `GLS.Valid`, `GLS/Semantics.lean` | none in the source for a sequent (the thesis has local consequence `Γ ⊨ ϕ` over GL-models, p. 169, which is this for one formula on the right) | agrees, and the reader names the restriction: "Valid quantifies only over GL models in which every formula is true-or-not at every world. With excluded middle every model is TwoValued … Without excluded middle … T1 (soundness) is a weaker claim than the textbook one and T3 (completeness) a stronger one". This is the choice of `decisions.md`, "what valid means" |
| a finite model as data | `GLS.Tree`, `Tree.desc`, `treeModel`, `subModel`, `Form.holds`, `Seq.refutedAt`, `Refutation`, `GLS/Semantics.lean` | none in the source | agrees: "W = the type of all finite trees; R t u iff … u is equal as a tree to some proper subtree of t … Worlds are trees up to structural equality, not node positions"; `Refutation`: "the negation of the implication … not … 'all of Γ true and all of Δ false'" (the two are proved to agree: `refutedAt_of_not_satSeq`, `not_satSeq_of_refutedAt`, `GLS/TreeModel.lean`) |
| GLS + (cut) | `GLS.FamCut`, `GLS/CutRule.lean` | the thesis, the rule (cut), p. 171, and `GLS_cut_rules`, p. 186 | agrees (the reading back of S24) |
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

`Soundness`, proved as `soundness`, `GLS/Soundness.lean`. Source: none
for GLS; the thesis has soundness for the Hilbert calculus GLH (Theorem
12.2.1, p. 169) and cites Sambin and Valentini 1982 for the sequent
calculus with cut (Theorem 12.4.1, p. 171; neither read). Screened: rule by rule, on `seqs1` and `seqsSmall`, no world of
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
`derivableDecidable`, `GLS/Completeness.lean`. Source, for the second:
the thesis, Corollary 12.6.1, p. 182, "Provability in GLS is
decidable" (proved there from `mhd`; here from the search). Read back: agrees, with
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
1605 (the thesis, Theorem 12.6.1 and Lemma 12.6.3, pp. 180-181; the
step `PSPrem.step` is its Lemma 12.6.1, p. 179), **in another form**: the source shows that every sequent has an
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
Source: `GLS_cut_adm`, `GLS_additive_cut.v` l. 692 (the thesis, Theorem
12.7.1, p. 182), of which this is the statement letter for letter. Screened: for 16 antecedents, 15
succedents and the nineteen small formulas as cut formula, wherever the
bounded search derives both premises within height 7 it derives the
conclusion within 9. Read back: agrees ("admissibility of cut,
context-sharing form … Its type does not distinguish a syntactic
cut-elimination argument from one going through T1 and T2"). Status:
**PROVED**, within `[propext, Quot.sound]`, **by the semantic route**:
the two premises are valid (S3), so the conclusion is, so the search
(S4) returns a derivation of it. That derivation is not made from the
two given ones. The source's construction is S19, a second definition
of this type: both are PROVED.

### S11 to S17. The source's structural theorems, with heights (goal 4)

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
`InversionImpR`, `InversionImpL`, `ContractionL`, `ContractionR`. In the
thesis: Lemma 12.5.1 (p. 172, with no height), Lemma 12.5.3 (p. 172),
Lemma 12.5.4 (p. 174), Lemma 12.5.5 (p. 176).

Status: **PROVED**, each, within `[propext, Quot.sound]`: `exchange`,
`weakeningL`, `weakeningR` (`GLS/Structural.lean`), `inversionImpR`,
`inversionImpL` (`GLS/Invert.lean`), `contractionL`, `contractionR`
(`GLS/Contract.lean`). By the agent of `brief-2-1.md`; built and run by
the operator (`GLS/CutTest.lean`). The route: one function `Fam.wk`,
which carries a derivation of `Γ ⇒ Δ` to one no higher of any `Γ' ⇒ Δ'`
with `Γ'` a permutation of `Γ ++ Ξ` and `Δ'` of `Δ ++ Ξ'`, gives
exchange and both weakenings; the inversions are stated up to a
permutation (`Fam.invR`, `Fam.invL`); contraction is on the left and the
right together, by recursion on a bound of the height, with the
inversions. Every permutation is proved by counting occurrences.

### S18. The two systems derive the same sequents (goal 5)

    (s : Seq) → (Fam s → PSFam s) × (PSFam s → Fam s)

`PSEquivalent`, defined as `psEquivalent`, `GLS/PS.lean`. Source: the
thesis, Proposition 12.6.1, p. 181 ("Γ ⇒ Δ has a proof in PSGLS iff
Γ ⇒ Δ has a proof in GLS"; found after the statement was written, which
was the operator's). Read back: agrees ("No claim that they are
mutually inverse, and no height relation"). Status: **PROVED**, within
`[propext, Quot.sound]`, by the thesis's argument: at a GLR whose
conclusion is an axiom of PSGLS, that axiom; IdB by the identity.

### S19. Cut admissibility, by the source's induction (goal 6)

The type of S10. A second definition of that type, which makes its
derivation from the two given ones, by induction on the size of the cut
formula and then on the termination measure. Source:
`GLS_cut_adm_main`, `GLS_additive_cut.v` l. 32 (the proof of the
thesis's Theorem 12.7.1, pp. 182-185). Status: **PROVED**:
`cutBySource`, `GLS/Cut.lean`, within `[propext, Quot.sound]`. It uses
no model, no search, no soundness and no completeness (the file imports
`GLS/Contract.lean` and `GLS/Search.lean`, and of the second only
`classify` and the finders). The secondary induction is on `weight U`
of the conclusion, where the source's is on `mhd`: both fall along the
premises of PSGLS. The kernel evaluates it (`GLS/CutTest.lean`: a cut
on `□p`, principal on both sides, by `decide +kernel`). On the
tutorial's cut both functions return a derivation of height 4.

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

Since 2026-11-27 the check of both is `s.refutedM t` (S30; for some
hours `s.refutedT t`, S26), which is `s.refutedAt t` computed one
subformula at a time over all the worlds; the statements above are
theorems still (`noValid_check`, with S30).

`noValid`, `noDerivable`, `GLS/Run.lean`. No budget in `Holds`. Screened
(`GLS/Screen.lean`): no sequent of the 1 024 that the bounded search
derives is accepted with any of the 964 trees; the plan's five
non-theorems are each accepted with one. Status: **PROVED**,
within `[propext, Quot.sound]` (`GLS/Run.lean`); negative tests:
`GLS/RunTest.lean`.

### S22. One side always answers (stage 3, level 3; our own)

    ∀ s : Seq,  (∃ c, treeCert.check s c = true) ∨ (∃ t, noValid.check s t = true)

(Since 2026-11-27 `treeCert.check` is the replay by counts, S27, and
`noValid.check` truth by the marks, S30; the statement is as it was.)
`decided`, `GLS/Run.lean`; and that the engine's producer answers `pass`
for every derivable sequent (`glsEngine_complete :
glsEngine.Complete`). Status: **PROVED**, within `[propext,
Quot.sound]`.

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
derives the conclusion; a control shows the screen able to say no.
Status: **PROVED**, within `[propext, Quot.sound]`; negative tests and
the agreement of the two searches on the 1 024 small sequents and the
corpus: `GLS/SetSearchTest.lean`.

### S24. Cut elimination (the standing list's entry 1, in the source's second form)

    (s : Seq) → FamCut s → Fam s

`CutElimination`, `GLS/CutRule.lean`, with `FamCut` the family of GLS +
(cut). Source: the thesis, Theorem 12.7.2, p. 186: "The additive cut
rule is eliminable from GLS + (cut)", in Coq `forall s, (GLS_cut_prv s)
-> (GLS_prv s)`. Entered on 2026-11-25 at 13:20, when the thesis was
read, and proved in the same step (`decisions.md`). Screened: on a
derivation with two cuts, one above the other, both definitions return
a derivation of GLS, of height 4 (`GLS/CutTest.lean`). Read back, after
the proof: agrees ("Fam3 = Fam plus r6, nothing else changed … the cut
rule, in its additive (context-sharing) form … every derivation of
Γ ⇒ Δ with cut yields a cut-free derivation"; "the type demands no
relation between input and output derivation beyond the shared end
sequent"). Status: **PROVED**, twice, within `[propext, Quot.sound]`:
`cutElimination` (each cut removed by `cutBySource`, S19: the source's
proof) and `cutEliminationBySearch` (each cut removed by S10).

### S25. Truth by the marks is truth (after the campaign, 2026-11-27; our own)

Why it is wanted: `decisions.md`, 2026-11-27. `Form.holds`, run as it
is written, asks for `A` at every world below a world for each `□A` and
keeps nothing: `2ⁿ` calls on a chain of `n` worlds and `n` nested boxes.
The marks of a formula on a tree are a tree of the same shape with two
bits at each world (true there; true there and at every world below),
computed for `A ⟶ B` from the marks of `A` and of `B`, and for `□A` from
those of `A` (`GLS/Table.lean`).

    Form.holdsT A t := (A.marks t).here
    ∀ (A : Form) (t : Tree),  A.holdsT t = A.holds t

`Form.holdsT_eq`, `GLS/Table.lean`; on the way, `Form.marks_eq : A.marks
t = Marks.of (fun u => A.holds u) t`. No item of the source, so not read
back. Screened (`GLS/CheckTest.lean`): equal on the 19 formulas of the
screens at 200 worlds. **The proof was written with the definitions and
passed at once, so the screen was run after it, not before** (the order
asked for was the other one). Status: **PROVED**, within `[propext,
Quot.sound]`.

### S26. The two checks of a countermodel are one function (2026-11-27; our own)

    Seq.refutedT s t := s.ant.all (·.holdsT t) && s.suc.all (!·.holdsT t)
    ∀ (s : Seq) (t : Tree),  s.refutedT t = s.refutedAt t

`Seq.refutedT_eq`, `GLS/Table.lean`. `Seq.refutedT` was, until S30 the
same day, the check of
`noValid` and `noDerivable` (S21), compiled and in the kernel. Screened
(`GLS/CheckTest.lean`): equal on the 1 024 small sequents at 200
worlds, where both answers occur; on the trees the search returns for
the corpus and for `consis 3, 8, 12`, `binTree 2, 3`, accepted by both;
a tree too short refused by both. As for S25, the screen was run after
the proof. Status: **PROVED**, within `[propext, Quot.sound]`.

### S27. The replay by counts is the replay (2026-11-27; our own)

Why it is wanted: `Cert.check` runs `step`, which writes each premise
out as a pair of lists, and the premise of GLR has `B, □B` for each `□B`
of the antecedent: `2ⁿ` formulas after `n` nested GLR. No rule of GLS
looks at more than how often a formula occurs (the source: "based on
multisets"). A side by counts is a list of formulas each with a number;
`countStep` reads the side conditions and the premises of `Move.rule`
on the counts (`GLS/Counts.lean`). The entries are kept in order of the
size of the formula and the premise of GLR is made by one merge; the
order is not part of the statement, nor of its proof (a count is the
sum over the entries of a formula, wherever they are).

    Seq.countCheck s c := countCheck (CSeq.of s) c
    ∀ (s : Seq) (c : Cert S),  s.countCheck c = Cert.check s c

`countCheck_eq`, `GLS/Counts.lean`. On the way: `count_xbox` (how often
a formula occurs in `xbox Γ`: once for each `□B` of `Γ`, and, if it is
boxed, once for each occurrence of it), and `countStep_rep` (at the
counts of a sequent, `countStep` applies where the move does, and its
premises are the counts of the move's premises). `Seq.countCheck` is the
check of `treeCert`, compiled and in the kernel; its verdict is the
derivation that `Cert.check` gives, as before. Entered and **screened
before its proof** (`GLS/CheckTest.lean`): the two replays agree on the
385 trees of moves that the search over sets returns for the 1 024 small
sequents, each at its own sequent (all accepted), at its sequent with
each side written twice, and at 40 other sequents (both answers occur);
on the trees of the proved search; on the corpus and `boxChain 3, 8,
12`, `kChain 4, 8`; and a formula used once more than it occurs is
refused by both. No disagreement was found. The definitions of the
replay were changed twice after the first proof, for the kernel's time
(`decisions.md`); the statement is the same, the screens are run on the
form kept at every build, and the proof is of that form. Status:
**PROVED**, within `[propext, Quot.sound]`.

### S28. For every sequent, a tree of moves that replays or a tree that refutes, with no sequent written out (2026-11-27; our own)

Why it is wanted: `decisions.md`, 2026-11-27, the second entry. S4 gives
a derivation of GLS as a term, which holds every sequent of the
derivation, `2ⁿ` formulas after `n` nested GLR; the search that returns
it builds them (Table 1: cut off at 28 boxes). This is level 3 over the
checks that the certifiers run, as a function:

    certOrRef : (s : Seq) → { c : Cert S // Cert.check s c = true } ⊕ { t : Tree // s.refutedAt t = true }

`certOrRef`, `GLS/Decide.lean`; with S27 and S30 the two sides are
`s.countCheck c = true` and `s.refutedM t = true`, the certifiers'
checks (`decided`, S22, is now read off it). The search is S4's, made at
sequents without repeated formulas: each premise has its repetitions
removed before the search goes on. The lemma under it:

    Yes q := { c : Cert S // ∀ q', q.Sub q' → Cert.check q' c = true }

a tree of moves found for `q` replays at every sequent `q'` that has the
formulas of `q` on each side; from a `Yes` for each premise of a move
less its repetitions, a `Yes` for the conclusion, **if no formula of the
conclusion is repeated** (`Yes.impR`, `Yes.impL`, `Yes.glr`). The
hypothesis is needed: with `A → B` twice in a succedent, the premise of
ImpR at the sequent with it once has lost it and the premise at the
other has not. The steps are enough by the measure of S9, which removing
repetitions does not raise (`weight_dedup_le`). No item of the source
(the source's PSGLS is on multisets), so not read back.
**Screened before its proof**, with the search over sets that was not
proved (kept as guards in `GLS/CheckTest.lean`): on the 1 024 small
sequents one side answers and its certificate passes the certifier's
check; each of the 385 trees of moves replays at four sequents with the
formulas of its own and more; for 300 sequents, the tree of the sequent
less its repetitions replays at the sequent written twice; a control (a
tree at a sequent that lacks a formula) is refused. Status: **PROVED**,
within `[propext, Quot.sound]`. The search that was not proved
(`searchSet`) is gone: `produceSet` is this function without its proof.

### S29. The replay of a script by counts is the library's (2026-11-27; our own)

Why it is wanted: the library's `derives` runs a script on an attempt, a
partial derivation that holds every open goal written out; S27 repaired
the replay of a tree of moves and left this one.

    Seq.scriptCheck s ls := goalsDone countStep [CSeq.of s] ls
    ∀ (s : Seq) (ls : Script S),  s.scriptCheck ls = derives S s ls

`scriptCheck_eq`, `GLS/Scripts.lean`. `goalsDone step gs ls` runs the
script on a bare list of goals: a line replaces the goal it names by the
premises of its move, and the script must end with no goal. On the way,
for every proof system and not only this one:

    ∀ (S : ProofSystem) (j : S.Judg) (ls : Script S),  derives S j ls = goalsDone (stepOpt S) [j] ls

(`derives_eq_goalsDone`, from the library's `Att.moveAt_ok`,
`Att.moveAt_error`, `Att.moveAt_inr`); then `goalsDone_rep`, by S27's
`countStep_rep`. `Seq.scriptCheck` is the check of `scriptCert` and of
the engine's yes side, compiled and in the kernel. **The proof was
written with the definitions and passed; the screen was run after it**
(`GLS/CheckTest.lean`): the two replays agree on the script of each of
the 385 trees at its own sequent (accepted), at the sequent written
twice and at 40 others (both answers occur); a script cut short, with a
line too many, and with every goal number one too high are refused by
both; lines in another order (the second premise first) are accepted by
both. Status: **PROVED**, within `[propext, Quot.sound]`.

### S30. The check with a table over the different subformulas is the definition (2026-11-27; our own)

Why it is wanted: Table 5 of `measurements.md` found the check of S26
slower compiled than in the kernel on `binTree 12` (7.7 s against
2.0 s). S25's marks are computed for each occurrence of a subformula;
`binForm n` has a subformula twice at each level. The marks of a
subformula are now kept in a table once computed and looked up before
the subformula is entered, with one table for the whole sequent
(`GLS/Table.lean`).

    Seq.refutedM s t := the antecedent's formulas all true at the root and the succedent's none,
                        by Form.marksM, the table handed from formula to formula
    ∀ (s : Seq) (t : Tree),  s.refutedM t = s.refutedAt t

`Seq.refutedM_eq`, `GLS/Table.lean`; on the way `Form.marksM_spec`: from
a table every entry of which has the marks of its formula, the marks
returned are `A.marks t` and the table returned is such a table. The
order of the table and the sizes kept in it are not part of what is
proved. `Seq.refutedM` is the check of `noValid` and `noDerivable`,
compiled and in the kernel, in place of S26's. **Screened before its
proof** (kept as guards, `GLS/CheckTest.lean`): equal to the definition
on the 1 024 small sequents at 200 worlds, both answers occurring; on
380 sequents whose formulas share subformulas and repeat on both sides,
at 100 worlds; on `binTree 1` to `5` at every world of the refuting
tree; a tree too short refused. No disagreement was found. Status:
**PROVED**, within `[propext, Quot.sound]`.

### S31, S32. Uniform interpolation, the condition on variables (after the campaign, 2026-11-27; our own)

Why they are wanted: uniform interpolation for GL was proved on
2026-11-26 by another session (`GLS/Interpolation.lean`; the row under
"Not goals, and set aside" below). Its statement, `UIFor p A`, says that
`∃p.A` and `∀p.A` do not contain `p`. The usual statement of uniform
interpolation says more: every variable of `∃p.A` is a variable of `A`.
With that clause missing, the Lean statement was not the theorem of the
literature as it is written, though on paper it implies it (substitute
`⊥` for the other variables; substitution is not in this development).

    S31   UiSeqVars :=
            ∀ (p q : Nat) (Γ Δ : List Form),
              (∀ A ∈ Γ ++ Δ, A.occ q = false) → (uiSeq p Γ Δ).occ q = false

    S32   UniformInterpolationVars :=
            (p : Nat) → (A : Form) →
              { u : UIFor p A //
                ∀ q, (u.ex.occ q = true → A.occ q = true) ∧ (u.all.occ q = true → A.occ q = true) }

`UiSeqVars`, proved as `uiSeq_vars`; `UniformInterpolationVars`, defined
as `uniformInterpolationVars`; both in `GLS/InterpolationVars.lean`, the
two types committed before their proofs (`34bb4ff`). S32 is the whole
statement for formulas: `u : UIFor p A` holds the two formulas, that
neither contains `p`, and the four derivations (those of
`uniformInterpolation`, which S32's proof uses unchanged); the new
clause is the one on variables. **Screened before the proofs** (kept as
guards, `GLS/InterpolationTest.lean`): on the 624 formulas of at most
two layers over three variables, for each of the three variables and
both quantifiers, by a second definition of the variables of a formula;
no failure. Both pinned by `#statement` there. Status: **PROVED**,
within `[propext, Quot.sound]`.

## Refuted

None.

## Not goals, and set aside

| result | not a goal (the plan's reason), or set aside |
|---|---|
| `mhd`, the maximal height of an unfinished PSGLS derivation (`PSGLS_termination.v` l. 1598) | not a goal: a lemma on the source's route; termination is S9, and the induction of S19 can be on the measure itself. Decided again if S19 needs it |
| the decidability of the applicability of each rule (`GLS_PSGLS_dec.v`) | not a goal of Prove: it is `step`, with S1 and S2 |
| a cut-elimination procedure for a calculus with a cut rule | **a goal after all**, since the thesis states it (Theorem 12.7.2): S24, PROVED |
| interpolation | not a goal of the campaign (the plan: about other systems). **Uniform interpolation for GL was PROVED after the campaign**, on 2026-11-26, by another session at the reviewer's word: `GLS.uniformInterpolation` (formulas), `GLS.uniformInterpolationSeq` (sequents), `GLS.uiSeq_iff`, `GLS.uiSeq_free`, `GLS.uiSeqRaw_mdepth`, in `GLS/Interpolation.lean`, each pinned by `#statement` in `GLS/InterpolationTest.lean` as PROVED within `[propext, Quot.sound]`; checked again on 2026-11-27 (the file elaborated afresh, no `sorry`, the axioms printed). Those statements say the interpolant has no `p`; that its variables are variables of the formula is S31 and S32 above. The statements, the proof and what is OPEN (a size bound, not attempted) are in [2026-11-26-ui.md](2026-11-26-ui.md); the entries of 2026-11-26 09:46 and 2026-11-27 14:31 in [decisions.md](decisions.md) have the reviewer's words. The statements of 2026-11-26 have no number here and are not counted in the summary below |
| arithmetical completeness; a Hilbert system for GL | not goals: about other systems |

## Summary

| | PROVED | REFUTED | OPEN |
|---|---|---|---|
| of the goals from the standing list (S7; S10 with S19; S24) | 3 | 0 | 0 |
| of the other goals (S3 to S6, S8, S9; S11 to S18) | 14 | 0 | 0 |
| of our own (S1, S2, S20 to S23, S25 to S32) | 14 | 0 | 0 |

Counted by entry, with S11 to S17 seven entries and S19 counted with
S10 (one statement, two definitions).
