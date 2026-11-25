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
