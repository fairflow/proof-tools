# GLS: the rule table

This page lies beside the source for anyone who reads the transcription.
The "as printed" column is copied from the source, and the output of
`#rules` is pasted as Lean printed it.

Sources, two. **The authors' Coq file** `GL/GLS_PSGLS_calcs.v` of
`github.com/ianshil/CE_GLS`, commit `3dd8619`, by line: the table was
made from it, when neither the paper nor the thesis could be read
(`decisions.md`, 2026-11-25 09:07). **The thesis's figure**: I.
Shillito, PhD thesis (ANU, 2023), Figure 12.1, p. 171, and section 12.6,
p. 178, read on 2026-11-25 at 13:20 from the page's image: the
comparison with it is the section "The comparison with the figure in
prose", below. The paper's own figure (TABLEAUX 2021) has not been
seen.

The families: `GLS.Fam` (GLS) and `GLS.PSFam` (PSGLS), in
`GLS/System.lean`. The proof system: `GLS.S`, in `GLS/Proof.lean`; it is
for GLS only.

Checked: the source's worked derivations as terms: the four cases of
the Coq file's `Id_all_form` and one more that joins three; the thesis's
Examples 12.4.1 and 12.4.2 (three derivations with a rule in them), 3 of
3. The second transcription, run twice on 2026-11-25, by two cold
readers: on the Coq file, and on the thesis's pages; no difference in
any rule either time.

## Notation

| in the source (Coq) | in Lean | note |
|---|---|---|
| `# P`, with `P : V` | `Form.var p`, with `p : Nat` | the variables are numbered (D1); shown as `p q r s`, then `p4`, … |
| `⊥` (written `Bot V` in the rules) | `⊥`, `Form.bot` | |
| `A → B` | `A ⟶ B`, `Form.imp A B` | Lean reserves `→`; the printer of the explorer writes `→` |
| `Box A` | `□A`, `Form.box A` | the Coq file has no symbol for it |
| `(Γ, Δ)`, `pair Γ Δ` | `Γ ⇒ Δ`, `Seq.mk Γ Δ` | fields `ant`, `suc` |
| `Γ0 ++ A :: Γ1`, the formula `A` at a place of a list | `A ∈ Γ`, and in a premise `Γ.erase A` for "the rest" | D2 |
| `XBoxed_list BΓ` with `BΓ` the boxed formulas of `Γ0` | `xbox Γ` | D3; the definition is below |
| `Γ`, `Δ`, `A`, `B`, `P` | the same letters; `p` for the number of a variable | the encoding adds no letter. The source's `Γ0, Γ1`, `Δ0, Δ1`, `BΓ` have no counterpart: D2, D3 |

## The rules of GLS

`GLS_rules`, l. 306-312. Five rules. In the column "as printed" the
Coq constructor is copied.

| # | rule | as printed, and where | the constructor | agrees with `#rules` below? | the move, and what `step` asks and leaves |
|---|---|---|---|---|---|
| 1 | IdP | `IdPRule [] (pair (Γ0 ++ # P :: Γ1) (Δ0 ++ # P :: Δ1))`, l. 265-266 | `Fam.idP` | yes, with D2: "at a place" is membership | `idP p`; asks `var p ∈ Γ` and `var p ∈ Δ`; leaves nothing |
| 2 | BotL | `BotLRule [] (pair (Γ0 ++ (Bot V) :: Γ1) Δ)`, l. 275-276 | `Fam.botL` | yes, with D2 | `botL`; asks `⊥ ∈ Γ`; leaves nothing |
| 3 | ImpR | `ImpRRule [(pair (Γ0 ++ A :: Γ1) (Δ0 ++ B :: Δ1))] (pair (Γ0 ++ Γ1) (Δ0 ++ (A → B) :: Δ1))`, l. 280-282 | `Fam.impR` | yes, with D2: `B :: Δ.erase (A ⟶ B)` for `Δ0 ++ B :: Δ1`, and `A :: Γ` for `Γ0 ++ A :: Γ1` | `impR A B`; asks `A ⟶ B ∈ Δ`; leaves `A :: Γ ⇒ B :: Δ.erase (A ⟶ B)` |
| 4 | ImpL | `ImpLRule ((pair (Γ0 ++ Γ1) (Δ0 ++ A :: Δ1)) :: [(pair (Γ0 ++ B :: Γ1) (Δ0 ++ Δ1))]) (pair (Γ0 ++ (A → B) :: Γ1) (Δ0 ++ Δ1))`, l. 286-289 | `Fam.impL` | yes, with D2; the premise with `A` on the right is the first, as in the source | `impL A B`; asks `A ⟶ B ∈ Γ`; leaves `Γ.erase (A ⟶ B) ⇒ A :: Δ` and `B :: Γ.erase (A ⟶ B) ⇒ Δ` |
| 5 | GLR | `(is_Boxed_list BΓ) -> (nobox_gen_ext BΓ Γ0) -> GLRRule [(pair ((XBoxed_list BΓ) ++ [Box A]) [A])] (pair Γ0 (Δ0 ++ Box A :: Δ1))`, l. 298-301 | `Fam.glr` | yes, with D2 and D3: `xbox Γ` for `XBoxed_list BΓ` under the two side conditions | `glr A`; asks `□A ∈ Δ`; leaves `xbox Γ ++ [□A] ⇒ [A]` |

## The rules of PSGLS

`PSGLS_rules`, l. 314-327. Six rules. No move: the explorer's proof
system is GLS.

| # | rule | as printed, and where | the constructor | agrees with `#rules` below? |
|---|---|---|---|---|
| 1 | PSIdP | `IdPRule ps c -> PSGLS_rules ps c`, l. 315 | `PSFam.idP` | yes, as GLS 1 |
| 2 | PSIdB | `IdBRule ps c -> PSGLS_rules ps c`, l. 316, with `IdBRule [] (pair (Γ0 ++ Box A :: Γ1) (Δ0 ++ Box A :: Δ1))`, l. 270-271 | `PSFam.idB` | yes, with D2 |
| 3 | PSBotL | `BotLRule ps c -> PSGLS_rules ps c`, l. 317 | `PSFam.botL` | yes, as GLS 2 |
| 4 | PSImpR | `ImpRRule ps c -> PSGLS_rules ps c`, l. 318-319 | `PSFam.impR` | yes, as GLS 3 |
| 5 | PSImpL | `ImpLRule ps c -> PSGLS_rules ps c`, l. 320-321 | `PSFam.impL` | yes, as GLS 4 |
| 6 | PSGLR | `(IdPRule [] c -> False) -> (IdBRule [] c -> False) -> (BotLRule [] c -> False) -> GLRRule ps c -> PSGLS_rules ps c`, l. 322-326 | `PSFam.glr` | yes, with D4: the three conditions are `¬ IsIdP`, `¬ IsIdB`, `¬ IsBotL` of the conclusion |

The output of `#rules GLS.Fam` and `#rules GLS.PSFam`, pasted whole:

```
GLS.Fam — 5 rules
idP
    ─────────────
    Fam (Γ ⇒ Δ)
    for  p : Nat
    if   Form.var p ∈ Γ
         Form.var p ∈ Δ

botL
    ─────────────
    Fam (Γ ⇒ Δ)
    if   ⊥ ∈ Γ

impR
    Fam (A :: Γ ⇒ B :: Δ.erase (A ⟶ B))
    ─────────────────────────────────────
    Fam (Γ ⇒ Δ)
    for  A : Form,  B : Form
    if   A ⟶ B ∈ Δ

impL
    Fam (Γ.erase (A ⟶ B) ⇒ A :: Δ)      Fam (B :: Γ.erase (A ⟶ B) ⇒ Δ)
    ────────────────────────────────────────────────────────────────────
    Fam (Γ ⇒ Δ)
    for  A : Form,  B : Form
    if   A ⟶ B ∈ Γ

glr
    Fam (xbox Γ ++ [□A] ⇒ [A])
    ────────────────────────────
    Fam (Γ ⇒ Δ)
    for  A : Form
    if   □A ∈ Δ
GLS.PSFam — 6 rules
idP
    ───────────────
    PSFam (Γ ⇒ Δ)
    for  p : Nat
    if   Form.var p ∈ Γ
         Form.var p ∈ Δ

idB
    ───────────────
    PSFam (Γ ⇒ Δ)
    for  A : Form
    if   □A ∈ Γ
         □A ∈ Δ

botL
    ───────────────
    PSFam (Γ ⇒ Δ)
    if   ⊥ ∈ Γ

impR
    PSFam (A :: Γ ⇒ B :: Δ.erase (A ⟶ B))
    ───────────────────────────────────────
    PSFam (Γ ⇒ Δ)
    for  A : Form,  B : Form
    if   A ⟶ B ∈ Δ

impL
    PSFam (Γ.erase (A ⟶ B) ⇒ A :: Δ)      PSFam (B :: Γ.erase (A ⟶ B) ⇒ Δ)
    ────────────────────────────────────────────────────────────────────────
    PSFam (Γ ⇒ Δ)
    for  A : Form,  B : Form
    if   A ⟶ B ∈ Γ

glr
    PSFam (xbox Γ ++ [□A] ⇒ [A])
    ──────────────────────────────
    PSFam (Γ ⇒ Δ)
    for  A : Form
    if   ¬(Γ ⇒ Δ).IsIdP
         ¬(Γ ⇒ Δ).IsIdB
         ¬(Γ ⇒ Δ).IsBotL
         □A ∈ Δ
```

## The functions the rules use

`#rules` prints a definition by its name. These are the definitions,
from `GLS/Form.lean` and `GLS/System.lean`, copied by `sed`, not retyped:

```lean
def Form.xb : Form → List Form
  | □B => [B, □B]
  | _ => []

def xbox (Γ : List Form) : List Form := Γ.flatMap Form.xb

def Seq.IsIdP (s : Seq) : Prop := ∃ p, Form.var p ∈ s.ant ∧ Form.var p ∈ s.suc

def Seq.IsIdB (s : Seq) : Prop := ∃ A, □A ∈ s.ant ∧ □A ∈ s.suc

def Seq.IsBotL (s : Seq) : Prop := ⊥ ∈ s.ant
```

`List.erase` is core Lean's: it removes the first occurrence that is
equal to its argument, and nothing where there is none.

## The rule (cut), and GLS + (cut)

The family `GLS.FamCut`, in `GLS/CutRule.lean`: the five constructors of
`Fam` again, and one more. Source: the thesis, p. 171 ("the additive cut
rule") and p. 186 (`GLS_cut_rules`: "GLS_rules enhanced with (cut)").

| # | rule | as printed, and where | the constructor | agrees with `#rules` below? |
|---|---|---|---|---|
| 6 | (cut) | premises `Γ ⇒ Δ, ϕ` and `ϕ, Γ ⇒ Δ`; conclusion `Γ ⇒ Δ`; no side condition; p. 171. In Coq, p. 186: `(Γ0++Γ1,∆0++ϕ::∆1)` and `(Γ0++ϕ::Γ1,∆0++∆1)` over `(Γ0++Γ1,∆0++∆1)` | `FamCut.cut` | yes, with D2: the cut formula is put at the head of each premise |

What `#rules GLS.FamCut` prints for it, pasted (its other five rules
print as those of `Fam`):

```
cut
    FamCut (Γ ⇒ A :: Δ)      FamCut (A :: Γ ⇒ Δ)
    ──────────────────────────────────────────────
    FamCut (Γ ⇒ Δ)
    for  A : Form
GLS.FamCut — 1 indices, 6 constructors, 0 carrying green slime

  clean: idP, botL, impR, impL, glr, cut
```

## In the Lean and not in the source

| what | why it is there |
|---|---|
| `Fam.height` | the height of a derivation, as `derrec_height` of `general/dd_fc.v`, l. 131: 1 for an instance with no premise. The source's theorems about heights are stated with it |
| `CleanControl`, `SlimedControl` | the two controls of `#slime` |

## Side conditions

| condition | where in the source | which rules | how it is encoded |
|---|---|---|---|
| `BΓ` is a list of boxed formulas | l. 298 | GLR | with the next, it says `BΓ = top_boxes Γ0`; `xbox` computes `XBoxed_list (top_boxes Γ)` (D3) |
| `Γ0` is `BΓ` with formulas put in, none of them boxed | l. 299 | GLR | the same |
| the conclusion is no instance of IdP, of IdB, of BotL | l. 322-324 | PSGLR | three fields, `¬ (Γ ⇒ Δ).IsIdP`, `¬ (Γ ⇒ Δ).IsIdB`, `¬ (Γ ⇒ Δ).IsBotL` (D4) |

## The checks

* `#rules GLS.Fam`: 5 rules printed; `GLS_rules` has 5. `#rules
  GLS.PSFam`: 6 printed; `PSGLS_rules` has 6.
* `#slime` on the two controls, and on the two families, pasted:

```
GLS.CleanControl — 1 indices, 2 constructors, 0 carrying green slime

  clean: nil, cons
GLS.SlimedControl — 1 indices, 2 constructors, 1 carrying green slime

  app
    index 1  ms ++ ns
              ↳ computed by  HAppend.hAppend

  clean: nil
GLS.Fam — 1 indices, 5 constructors, 0 carrying green slime

  clean: idP, botL, impR, impL, glr
GLS.PSFam — 1 indices, 6 constructors, 0 carrying green slime

  clean: idP, idB, botL, impR, impL, glr
```

* The source's worked derivation, as terms of the family
  (`GLS/Source.lean`, which imports the theory file only): the four
  cases of `Id_all_form` (l. 331-363), `idVar` (l. 343), `idBot`
  (l. 346), `idImp` (l. 349: ImpR, then ImpL), `idBox` (l. 362: GLR);
  and `idBoxImp`, GLR and then the case of an implication, of height 4
  by `rfl`. Also there, by `rfl`: `xbox` on an antecedent that mixes
  boxed formulas and others, with one twice.
* The thesis's worked derivations (p. 171), as terms of the family, in
  the same file: Example 12.4.1, the second (`ex1241b`: (→R) from
  `p, q ⇒ r, □r` to `p ⇒ q → r, □r`) and the third (`ex1241c`, a proof:
  (GLR) from `□p, p, □p ⇒ p` to `□p ⇒ □p, q`; the family's premise is
  `p, □p, □p ⇒ p`, the same multiset); Example 12.4.2 at `ϕ := p`
  (`ex1242`: (→L), then (GLR) on `□p`), with the premise of its GLR
  computed by `rfl` and compared with the printed one as a multiset
  (`List.isPerm`, by `decide`): `□p → p, □(□p → p), p, p, □p, □p, □p ⇒ p`.
  The first derivation of Example 12.4.1 is a single sequent with no
  rule.
* The cold reader's instance of GLR (below) run through `step`, in
  scratch: the conclusion `□p, q, p → q, □q, □p ⇒ q, □q, ⊥` with `A = q`
  gave the premise `p, □p, q, □q, p, □p, □q ⇒ q`, which is the reader's.

## The second transcription

Made on 2026-11-25 by a cold reader: a fresh agent (general-purpose,
not a fork), given `GLS_PSGLS_calcs.v` and `univ_gen_ext.v` and told to
open nothing else and to write no Lean (`reference/adopt.md` §7). **Given
the Coq file and not a figure in prose**, because no prose could be read
(`decisions.md`). Its table is compared with what `#rules` prints.

| # | rule | the second reading: premises / conclusion / side condition | agrees with what `#rules` prints for the constructor? | settled from the source at | what was changed here |
|---|---|---|---|---|---|
| 1 | IdP | none / `Γ0, #P, Γ1 ⇒ Δ0, #P, Δ1` / "some propositional variable occurs in both"; variables only | yes | | nothing |
| 2 | BotL | none / `Γ0, ⊥, Γ1 ⇒ Δ` / `⊥` somewhere in the antecedent | yes | | nothing |
| 3 | ImpR | `Γ0, A, Γ1 ⇒ Δ0, B, Δ1` / `Γ0, Γ1 ⇒ Δ0, A→B, Δ1` / none. "`B` replaces `A→B` in place. `A` is inserted … at the split point, and that split … is free" | yes, as multisets: the constructor puts `A` and `B` at the head (D2) | | nothing |
| 4 | ImpL | `Γ0, Γ1 ⇒ Δ0, A, Δ1`; `Γ0, B, Γ1 ⇒ Δ0, Δ1` / `Γ0, A→B, Γ1 ⇒ Δ0, Δ1` / none; the premise with `A` on the right first | yes, as multisets (D2); the order of the premises is the same | | nothing |
| 5 | GLR | `B1, □B1, …, Bn, □Bn, □A ⇒ A` / `Γ0 ⇒ Δ0, □A, Δ1` / "`BΓ` is exactly the list of boxed formulas of `Γ0`, in the order and with the multiplicity they have in `Γ0`"; `□A` last in the antecedent; the succedent the one-element list | yes: `xbox Γ ++ [□A] ⇒ [A]` | l. 127-140, 232-254 (the reader cites the file's own lemmas for "determined") | nothing |
| P2 | PSIdB | none / `Γ0, □A, Γ1 ⇒ Δ0, □A, Δ1` / none; "not a rule of GLS" | yes | | nothing |
| P6 | PSGLR | as GLR / as GLR / "no propositional variable occurs both in `Γ0` and in `Δ0, □A, Δ1`; no boxed formula occurs both …; `⊥` does not occur in `Γ0`" | yes: the three fields, unfolded | l. 266, 271, 276 | nothing |
| P1, P3, P4, P5 | | as IdP, BotL, ImpR, ImpL, "no extra restriction" | yes | | nothing |

The number of rules: 5 and 6 in both readings.

Ambiguities that one reader found and the other did not. The cold
reader's, each settled:

* *`XBoxed_list` on a formula that is not boxed duplicates it*
  (`unBox_formula` is the identity there, l. 145-152), so the function
  "as defined is not 'unbox and keep'". Here `xbox` gives nothing for
  such a formula. The two agree wherever the rule uses them, since `BΓ`
  is boxed: D3 says so now.
* *The comment "arbitrary weakening" (l. 294) overstates*: boxed
  formulas of the antecedent cannot be weakened away in GLR. Agreed,
  and the family has it so: `xbox Γ` keeps every boxed formula of `Γ`.
* *A comment (l. 262) lists `IdBRule` among "rules common to both
  calculi"*, and `GLS_rules` does not have it. The definition rules:
  `Fam` has no `idB`.
* *PSGLS restricts GLR only*; its implication rules may be applied to an
  axiom. So here.
* *The file neither states nor proves that derivability is invariant
  under permutation*, and the exact notion of derivation is in files
  the reader was not given. The operator read them (`GLS_exch.v`,
  `general/ddT.v`, `general/dd_fc.v`): the plan, Q1.

The operator's, which the reader did not raise: none beyond D1 to D4.

## The second transcription, from the prose

Made on 2026-11-25 at 13:20 by a second cold reader: a fresh agent given
the thesis's PDF and eight of its pages (printed 168-171, 178-179,
185-186), read as images, and told to open nothing else and to write no
Lean. It had not seen the Coq file, the first reader's table, or this
one.

| # | rule | the reading from the prose: premises / conclusion / side condition | agrees with what `#rules` prints for the constructor? | what was changed here |
|---|---|---|---|---|
| 1 | (IdP) | none / `p, Γ ⇒ Δ, p` / "the identity formula is written p (an atom)" | yes | nothing |
| 2 | (⊥L) | none / `⊥, Γ ⇒ Δ` / none | yes | nothing |
| 3 | (→R) | `ϕ, Γ ⇒ Δ, ψ` / `Γ ⇒ Δ, ϕ → ψ` / none | yes: `A :: Γ ⇒ B :: Δ.erase (A ⟶ B)`, where the thesis's `Δ` is the succedent less the principal formula | nothing |
| 4 | (→L) | `Γ ⇒ Δ, ϕ` and `ψ, Γ ⇒ Δ` / `ϕ → ψ, Γ ⇒ Δ` / none; "contexts shared" | yes; the premises in the same order | nothing |
| 5 | (GLR) | `⊠Γ, □ψ ⇒ ψ` / `Φ, □Γ ⇒ □ψ, □Δ, Ψ` / "Φ and Ψ do not contain any boxed formulas"; so "□Γ = all boxed formulas of the antecedent (every occurrence)", the premise is unique for a diagonal formula, and "⊠ acts per occurrence; nothing is contracted" (from Example 12.4.2) | yes: `xbox Γ ++ [□A] ⇒ [A]` | nothing |
| P | (IdB) | none / `□ϕ, Γ ⇒ Δ, □ϕ` / a rule of PSGLS only | yes | nothing |
| P | (GLR) of PSGLS | as (GLR), with (NoInit): the conclusion is no instance of (IdP), (⊥L), (IdB); "a condition on the whole conclusion, context included" | yes: the three fields | nothing |
| 6 | (cut) | `Γ ⇒ Δ, ϕ` and `ϕ, Γ ⇒ Δ` / `Γ ⇒ Δ` / none | yes | nothing |

The number of rules: 5, 6, and (cut), in this reading as in the first.

What this reader raised, each settled:

* *`⊠Γ` is defined "for a set Γ" (p. 168) and used on multisets*; that it
  acts on each occurrence is shown only by Example 12.4.2. So here:
  `xbox` keeps multiplicities, and the Coq `XBoxed_list` does (the first
  reader's point 3).
* *Example 12.4.2 is printed for any `ϕ`, and its (GLR) step is an
  instance of the rule only for a `ϕ` that is not boxed* (`ϕ` is in `Φ`
  and in `Ψ`). The term `ex1242` takes `ϕ := p`.
* *"PSGLS restricts the rules of GLS", yet of its two items one adds a
  rule*, and nothing restricts (→L) and (→R). So here, and in the Coq
  file.
* *Example 12.4.1's third derivation, a proof in GLS, is not a
  derivation of PSGLS* (its conclusion is an instance of (IdB)). So
  here: `PSFam.glr` asks `¬ IsIdB`.
* *A misprint*, Definition 12.6.1 (2), p. 178: "ub(Γ ⇒ χ) of Γ ⇒ Δ".
* *Not on those pages*: the grammar of formulas and what a variable is
  (section 2.1), sequents, derivations and heights (section 4.2), models
  (section 5.1). The Coq files have each (`MPropF`, `rel (list …)`,
  `derrec`, `derrec_height`); the thesis's sections were not read.

## The comparison with the figure in prose

Made on 2026-11-25 at 13:20 by the operator, from the image of p. 171
and the text of p. 178, after the reviewer allowed the download.

| the thesis | the Coq file | the family | differs? |
|---|---|---|---|
| sequents "based on finite multisets"; "in our formalisation … on lists"; exchange admissible, Lemma 12.5.1 | lists, with the principal formula at any place | lists, with membership and `erase` (D2) | no: all three are the multiset calculus |
| (IdP) `p, Γ ⇒ Δ, p` | `IdPRule` | `idP` | no |
| (⊥L) `⊥, Γ ⇒ Δ` | `BotLRule` | `botL` | no |
| (→L): `Γ ⇒ Δ, ϕ` and `ψ, Γ ⇒ Δ` over `ϕ → ψ, Γ ⇒ Δ` | `ImpLRule`, the same order of premises | `impL` | no |
| (→R): `ϕ, Γ ⇒ Δ, ψ` over `Γ ⇒ Δ, ϕ → ψ` | `ImpRRule` | `impR` | no |
| (GLR): `⊠Γ, □ψ ⇒ ψ` over `Φ, □Γ ⇒ □ψ, □Δ, Ψ`, "Φ and Ψ do not contain any boxed formulas"; `⊠Γ = {ϕ₁, □ϕ₁, …, ϕₙ, □ϕₙ}` (p. 168) | `GLRRule`: `XBoxed_list BΓ ++ [Box A] ⇒ [A]` over `Γ0 ⇒ Δ0 ++ Box A :: Δ1`, `BΓ` boxed, `Γ0` being `BΓ` and formulas that are not boxed | `glr`: `xbox Γ ++ [□A] ⇒ [A]` over `Γ ⇒ Δ` with `□A ∈ Δ` | no. The thesis splits the succedent into `□ψ`, the other boxed formulas `□Δ` and the rest `Ψ`; every succedent with `□ψ` in it is of that form, so this is a way of writing it and no condition. The condition on `Φ` is the Coq file's second side condition (D3) |
| PSGLS: (IdentBox), (NoInit), p. 178 | `PSGLS_rules`: `PSIdB`, and three conditions on `PSGLR` | `PSFam.idB`, and three fields of `PSFam.glr` (D4) | no |
| the height `h(p)` of a proof (section 4.2, not read) | `derrec_height`: 1 for an instance with no premise | `Fam.height`, the same | not compared with the thesis's definition; the same as the Coq one |

**No difference** was found. Nothing was changed in the family.

## Divergences

| # | kind | the source's item | what the source says | what is done here | why | date |
|---|---|---|---|---|---|---|
| D1 | U | l. 23, 25 | the variables are the members of a set `V` with decidable equality, a parameter | `Nat` | a concrete type is needed for data, printing and the kernel's evaluation; any countable `V` is this up to a renaming | 2026-11-25 |
| D2 | R | l. 264-290, and l. 32 ("based on multisets") | a sequent is a pair of lists; the principal formula of a rule stands at a place, `Γ0 ++ A :: Γ1`; ImpR and ImpL put what they add at the place of the principal formula (`B`) or at a free place (`A`); exchange is proved admissible (`GLS_exch.v`) | a sequent is a pair of lists read as multisets: the conclusion of every rule is `Γ ⇒ Δ` for two variables; the principal formula is asked for by membership; a premise removes one occurrence of it (`List.erase`, the first) and puts what the rule adds at the head | no computed index in a conclusion (`reference/adopt.md` §3); every instance of the source's rule is an instance here up to a permutation of the premises' lists, and exchange is to be a theorem here too (goal 4 of the plan) | 2026-11-25 |
| D3 | R | l. 297-301 | GLR takes a list `BΓ` with two side conditions: every member of `BΓ` is boxed, and `Γ0` is `BΓ` with formulas put in that are not boxed. The premise is `XBoxed_list BΓ ++ [Box A] ⇒ [A]` | the premise is `xbox Γ ++ [□A] ⇒ [A]`, where `xbox Γ` is `B, □B` for each boxed `□B` of `Γ`, in order, and nothing for the other formulas | the two side conditions determine `BΓ` as the boxed formulas of `Γ0`, in order (the file's `nobox_gen_ext_injective`, l. 127, with `nobox_gen_ext_top_boxes`, l. 245), so `XBoxed_list BΓ = xbox Γ0`; one function in a premise instead of an existential and two conditions. `xbox` differs from `XBoxed_list` on a list that has formulas that are not boxed; the rule never applies it to one | 2026-11-25 |
| D4 | R | l. 322-324 | PSGLR asks `IdPRule [] c -> False`, `IdBRule [] c -> False`, `BotLRule [] c -> False` | `¬ (Γ ⇒ Δ).IsIdP`, `¬ (Γ ⇒ Δ).IsIdB`, `¬ (Γ ⇒ Δ).IsBotL`, with `IsIdP s` "some variable is in both lists" and so on | the same conditions with D2 applied to the three axioms | 2026-11-25 |

## What the table rests on

The transcription, row by row, and the choices D1 to D4, of which D2 is
the one to read: where a rule puts what it adds (the head), and which
occurrence it removes (the first). `decisions.md`, "Stage 0: the
encoding".

## Errors of transcription

None found: by `#rules`, by the worked derivations as terms, by the two
second transcriptions, by the comparison with the thesis's figure, or by
soundness and completeness.

| what | found by | repaired in (commit) | what was built again |
|---|---|---|---|
