# GLS: the source's results

**Written by hand from the authors' Coq files**, not from the paper or
the thesis, which had not been read when this was written (2026-11-25
09:07 GMT; `decisions.md`, "Stops"). So the items have a Coq name, a
file and a line, and **no printed number**: the numbers of the paper's
or the thesis's theorems are added when the prose is read. The files
are those of `github.com/ianshil/CE_GLS` at commit `3dd8619`, folder
`GL/`. In every statement "derivable" is `derrec GLS_rules (fun _ =>
False)`, and a height is `derrec_height` (`general/dd_fc.v`, l. 131).

| # | Coq name | file, line | statement, in words |
|---|---|---|---|
| 1 | `MPropF` | `GLS_PSGLS_calcs.v`, 41 | the formulas: `# P`, `⊥`, `A → B`, `Box A` |
| 2 | `XBoxed_list`, `top_boxes` | the same, 154, 161 | `B, Box B` for each member `Box B`; the boxed members of a list |
| 3 | `IdPRule`, `IdBRule`, `BotLRule`, `ImpRRule`, `ImpLRule`, `GLRRule` | the same, 264-300 | the six rule schemes |
| 4 | `GLS_rules` | the same, 306 | GLS: IdP, BotL, ImpR, ImpL, GLR |
| 5 | `PSGLS_rules` | the same, 314 | PSGLS: IdP, IdB, BotL, ImpR, ImpL, and GLR where the conclusion is no instance of IdP, IdB, BotL |
| 6 | `Id_all_form` | the same, 331 | for every formula `A`: `Γ0, A, Γ1 ⇒ Δ0, A, Δ1` is derivable in GLS |
| 7 | `dec_GLS_rules`, `dec_PSGLS_rules` | `GLS_PSGLS_dec.v`, 313, 335 | for every sequent it is decidable whether some rule of GLS (of PSGLS) has it as conclusion |
| 8 | `GLS_hpadm_list_exch_L`, `_R` | `GLS_exch.v`, 2124, 2038 | exchange of two blocks of the antecedent (succedent) is admissible in GLS, with a derivation no higher |
| 9 | `GLS_wkn_L`, `GLS_wkn_R` | `GLS_wkn.v`, 226, 374 | weakening by a formula at any place of the antecedent (succedent) is admissible in GLS, with a derivation no higher |
| 10 | `ImpR_ImpL_hpinv`; `ImpR_inv`, `ImpL_inv` | `GLS_inv_ImpR_ImpL.v`, 63; 687, 696 | if the conclusion of an instance of ImpR (of ImpL) is derivable in GLS then so is its premise (so are both), with derivations no higher |
| 11 | `GLS_hpadm_ctr_L`, `_R` | `GLS_ctr.v`, 1051, 1064 | contraction of two occurrences of a formula in the antecedent (succedent) is admissible in GLS, with a derivation no higher |
| 12 | `usable_boxes`, `n_imp_subformS`, `term_meas` | `PSGLS_termination_measure.v`, 486, 106, 542 | the measure of a sequent: the number of its boxed subformulas that are not boxed formulas of its antecedent, and the number of its occurrences of `→` |
| 13 | `GLR_applic_less_usable_boxes` | the same, 626 | at GLR, where the conclusion is no instance of IdB, the premise has fewer usable boxes |
| 14 | `ImpR_applic_less_Imp_same_usable_boxes`, `ImpL_…` | the same, 647, 701 | at ImpR and ImpL each premise has no more usable boxes and fewer implications |
| 15 | `PSGLS_termin` | `PSGLS_termination.v`, 1563 | every sequent has a PSGLS derivation with open leaves that is of maximal height among such |
| 16 | `mhd`; `RA_mhd_decreases` | the same, 1598, 1605 | `mhd s` is that maximal height; it is smaller at each premise of an instance of a PSGLS rule than at its conclusion |
| 17 | `GLS_cut_adm_main` | `GLS_additive_cut.v`, 32 | cut admissibility, by induction on the size of the cut formula and then on `mhd` of the conclusion |
| 18 | `GLS_cut_adm` | the same, 692 | if `Γ0, Γ1 ⇒ Δ0, A, Δ1` and `Γ0, A, Γ1 ⇒ Δ0, Δ1` are derivable in GLS then so is `Γ0, Γ1 ⇒ Δ0, Δ1` |

## The printed numbers (added 2026-11-25 13:21 GMT, from the thesis)

I. Shillito, PhD thesis (ANU, 2023), chapter 12. Read from the PDF; the
numbers are the thesis's, and those of the paper (TABLEAUX 2021) are
not known, since the paper was not got. The column "#" is the row of
the table above.

| the thesis's item | page | # | statement, in words |
|---|---|---|---|
| Definition 12.2.1 | 168 | 1 | the size of a formula |
| Definition 12.2.2 | 168 | | a GL-Kripke frame: transitive, and converse well-founded ("no infinite ascending sequences") |
| Definition 12.2.3 | 168 | | forcing: `p` by the interpretation, `⊥` never, `→` by implication, `□ϕ` at every `v` with `wRv` |
| Theorem 12.2.1 | 169 | | the Hilbert calculus GLH is sound for local consequence over GL-models |
| Theorem 12.2.3 | 169 | | `∅ ⊢ ϕ` in GLH iff `ϕ` is valid on GL-models (Segerberg, cited) |
| Figure 12.1 | 171 | 3, 4 | the sequent calculus GLS: (IdP), (⊥L), (→L), (→R), (GLR) |
| Examples 12.4.1, 12.4.2 | 171 | | four worked derivations; the second example is a loop of naive backward search |
| the rule (cut) | 171 | | additive: from `Γ ⇒ Δ, ϕ` and `ϕ, Γ ⇒ Δ` to `Γ ⇒ Δ` |
| Theorem 12.4.1 | 171 | | `(Γ, ϕ) ∈ GLL` iff some finite `Γ' ⊆ Γ` has `Γ' ⇒ ϕ` provable in GLS + (cut) (cited, not proved) |
| Lemma 12.5.1 | 172 | 8 | exchange is admissible in GLS |
| Lemma 12.5.2 | 172 | 6 | every `ϕ, Γ ⇒ Δ, ϕ` has a proof |
| Lemma 12.5.3 | 172 | 9 | weakening, height-preserving |
| Lemma 12.5.4 | 174 | 10 | the implication rules are invertible, height-preserving |
| Lemma 12.5.5 | 176 | 11 | contraction, height-preserving |
| (IdentBox), (NoInit) | 178 | 5 | PSGLS: GLS with (IdB), and (GLR) only where the conclusion is no instance of (IdP), (⊥L), (IdB) |
| Definition 12.6.1 | 178 | 12 | `imp`, the usable boxes `ub`, their number `β`, the measure `Θ = (β, imp)` |
| Lemma 12.6.1 | 179 | 13, 14 | `Θ` falls from the conclusion of a rule of PSGLS to each premise |
| Lemma 12.6.2 | 180 | | every sequent has a finite list of its PSGLS premises |
| Theorem 12.6.1 | 180 | 15 | every sequent has a PSGLS derivation of maximum height |
| Lemma 12.6.3 | 181 | 16 | `mhd` falls from conclusion to premise in PSGLS |
| Proposition 12.6.1 | 181 | | provable in PSGLS iff provable in GLS |
| Theorem 12.6.2, Corollary 12.6.1 | 182 | 7 (in part) | provability in PSGLS, and in GLS, is decidable |
| Theorem 12.7.1 | 182 | 17, 18 | the additive cut rule is admissible in GLS |
| Theorem 12.7.2 | 186 | | the additive cut rule is eliminable from GLS + (cut) |
