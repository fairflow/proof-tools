# DILL: a tutorial, with graded exercises

<!-- lean-pins: module DILL.TutorialPins; import DILL.Goals DILL.Invert DILL.Translate DILL.Tactic DILL.Engine; open DILL -->

DILL is dual intuitionistic linear logic: intuitionistic linear logic
with the connectives ⊗, 1, ⊸ (the multiplicatives), &, ⊤, ⊕, 0 (the
additives) and the exponential `!`, in a sequent calculus whose sequents
have two zones of hypotheses,

    Γ ; Δ ⟹ C

the zone `Γ` of hypotheses that may be used any number of times, the
zone `Δ` of hypotheses that are each used exactly once, and one
conclusion. This page teaches the calculus through twenty-seven
exercises, and explains what has been proved about it in Lean: the
structural properties of the two zones, the admissibility of the two
cuts and cut elimination, the invertible rules and the rules that are
not, identity expansion, the subformula property, consistency and the
disjunction property, the translation to and from the one-zone calculus,
soundness and completeness for the intuitionistic phase semantics, and
what can be run: a search, a decision for the fragment without `!`, and
two certificates that the kernel checks.

The calculus is that of B.-Y. E. Chang, K. Chaudhuri and F. Pfenning, *A
judgmental analysis of linear logic*, technical report CMU-CS-03-131R
(Carnegie Mellon University, revised December 2003), Figure 2, for the
connectives above; it is cited below as CCP. The name and the two zones
are A. Barber's (*Dual intuitionistic linear logic*, report
ECS-LFCS-96-347, Edinburgh 1996), whose system is natural deduction for
⊗, 1, ⊸ and `!`. The semantics is that of M. Kanovich, M. Okada and
K. Terui, *Intuitionistic phase semantics is almost classical*, Math.
Struct. in Comp. Science (2006), Section 2, cited as KOT. The Lean
development is `calculi/DILL/` of
[fairflow/proof-tools](https://github.com/fairflow/proof-tools/tree/main/calculi/DILL).

**What is checked.** Every derivation, height, message and verdict
quoted on this page is pinned in
[`DILL/TutorialTest.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/TutorialTest.lean),
which the build compiles. Every displayed statement with a line *Lean:*
under it is printed by Lean from the declaration it names, not typed;
the status on that line, PROVED or OPEN, and the axioms are computed by
Lean, and
[`DILL/TutorialPins.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/TutorialPins.lean)
fails the build if the page and the library ever differ. A line *Lean,
in paraphrase:* marks a statement written in the usual notation: its
declarations and their status are checked, its wording is not. Names
linked into the source are checked to exist. The prose that describes
how a proof goes is a reading of the Lean files and is not itself
checked.

Eight statements on this page are REFUTED (sections 4.3 and 5.4). The
script that writes the captions knows only PROVED and OPEN, so under a
refuted statement the caption names the theorem that is its negation,
and the PROVED there is of the negation.

Lean prints a formula `!A` and a formula `A ⊕ B` without the parentheses
that it needs to read them back (section 0): a statement displayed here
is what Lean prints, and is not always what one types.

## 0. Before you start

To build, and to open the file of exercises:

    (cd ~/Lean/Sources/proof-tools && git pull --ff-only)
    (cd ~/Lean/Sources/proof-tools/calculi/DILL && lake build)

then open
[`Play/DILLExercises.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/Play/DILLExercises.lean)
in the editor, with the infoview. Parts A and B can also be done on
paper: the solutions at the end give each derivation as a list of rule
applications. A tour of the tactic with every step explained is
[`Play/DILLTutorial.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/Play/DILLTutorial.lean).

**How a move is typed.** A goal is a sequent still to be derived. The
tactic `dillmove`, followed by the name of a rule and its principal
formula, applies the rule at the first goal, read upwards: the premises
of the rule are the new goals.

    dillmove bangL p              the rule !L on !p
    dillmove tensorR p q [p]      ⊗R at the conclusion p ⊗ q; the hypothesis p goes to the first premise
    dillmove                      asks which moves apply; none is made

**Two notation traps.** Lean has its own meaning for two of the signs.

* `!` is Lean's negation of a Boolean, and takes everything that
  follows. `!p` alone, `!(p ⊸ q)` and `[!p, q]` are read as formulas.
  But `!p ⊗ q` is read as `!(p ⊗ q)` with Lean's `!`, and is an error
  that names `Bool`. Write `(!p) ⊗ q`, `(!p) ⊸ q`, `(!A) :: Δ`: a `!`
  formula inside another formula, or before `::`, goes in parentheses.
* `⊕` is Lean's sum of two types, and binds loosely. Inside `[…]` and as
  the argument of a move, `p ⊕ q` is the formula. Before `::` or `∈` it
  is not: write `(A ⊕ B) :: Δ`. The error, when it comes, names `Sum`.

And one sign is new: the two zones are separated by `⨾`, because Lean's
`;` separates tactics. The page writes `Γ ; Δ ⟹ C`, as the source does
and as Lean prints a goal; what is typed is `Γ ⨾ Δ ⟹ C`, with each zone
a list: `[] ⨾ [!p] ⟹ (!p) ⊗ (!p)`. In the editor `⟹` is `\==>`; `⨾` has
no abbreviation there, so copy it from a line of the file. The
exercises have every sequent written out, and a move never needs the
sign.

The grades:

| grade | what it asks |
|---|---|
| ★ | a move or two; reading a rule |
| ★★ | a short derivation, or a small countermodel |
| ★★★ | wants an idea |
| ★★★★ | a proof or a program in Lean |

## 1. The logic, and where the calculus comes from

**Formulas.** A propositional letter `p, q, r, …`, one of the constants
`1`, `⊤`, `0`, or one of

    A ⊗ B   "tensor"      A ⊸ B   "lolli"      A & B   "with"      A ⊕ B   "plus"      !A   "bang"

In Lean, [`Form`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Form.lean#L15-L36 "DILL.Form") has nine constructors. The constants
are typed `𝟏 ⊤ 𝟎` and printed `1 ⊤ 0`. There is no negation, no `⊥` and
no `?`: the fragment is the one in which a sequent has exactly one
conclusion.

**How a formula is read.** A linear hypothesis is a resource that a
derivation uses exactly once. `A ⊗ B` is both `A` and `B`, side by
side. `A ⊸ B` gives `B` for one `A`, once. `A & B` is a choice of one of
the two, made by whoever uses it. `A ⊕ B` is one of the two, chosen by
whoever provides it. `!A` is `A` as often as it is wanted, zero times
included.

**Two zones.** In Girard's one-zone calculus, `!A` is governed by four
rules: dereliction, weakening, contraction and promotion (section 6 has
them). Barber's observation is that the three structural ones can be
built into the form of the sequent. A sequent

    A₁, …, Aⱼ ; B₁, …, Bₖ ⟹ C

has a zone of **valid** (or unrestricted) hypotheses `Aᵢ`, each usable
any number of times, and a zone of **linear** hypotheses `Bᵢ`, each used
exactly once. It says what the one-zone sequent
`!A₁, …, !Aⱼ, B₁, …, Bₖ ⊢ C` says (section 6 proves it). Weakening and
contraction then belong to the zone, not to a connective, and `!` is the
connective that moves a formula between the zones.

**Where it is used.** The same two zones are the typing context of a
linear type system: the valid hypotheses are the variables that may be
used freely, the linear ones those that must be used exactly once, and a
derivation is a term (Barber's report gives the terms). The ordinary
function type is `!A ⊸ B`: a function that may use its argument any
number of times (CCP write it `A ⊃ B`, p. 9; exercise A9 derives the S
combinator in this form). L. Caires and F. Pfenning read the same
sequents as session types: a linear hypothesis is a channel used
according to its type, `!A` a server that can be called repeatedly, and
cut the composition of two processes (*Session types as intuitionistic
linear propositions*, CONCUR 2010; their Figure 3 is this calculus with
process terms, for ⊸, ⊗, 1, &, ⊕ and `!`). This page does not go
further into either reading.

**The source's figure, and one misprint.** CCP's Figure 2 (p. 12) is the
calculus for a larger logic, with a second judgment and the connective
`?`; the fragment here is the figure without the rules for those. The
figure prints the conclusions of its rules ⊕R₁ and ⊕R₂ as `A & B`. That
is a misprint: the rules are named for ⊕ and stand beside ⊕L; as
printed, ⊕ would have no right rule and `· ; A ⟹ A & B` would be
derivable; and Pfenning's lecture notes print `A ⊕ B`. The Lean has
`A ⊕ B`. A reader given only the page images of the figure found the
same misprint, unprompted. The campaign's
[rule table](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/campaign/rule-table.md)
has each rule beside its source, and this divergence as W1.

## 2. The calculus

There are eighteen rules, and two cuts.

     ──────────── init                 Γ, A ; Δ, A ⟹ C
      Γ ; A ⟹ A                       ───────────────── copy
                                        Γ, A ; Δ ⟹ C

      Γ ; Δ, A, B ⟹ C                  Γ ; Δ ⟹ A     Γ ; Δ′ ⟹ B
     ────────────────── ⊗L            ──────────────────────────── ⊗R
      Γ ; Δ, A ⊗ B ⟹ C                    Γ ; Δ, Δ′ ⟹ A ⊗ B

      Γ ; Δ ⟹ C
     ──────────────── 1L              ──────────── 1R
      Γ ; Δ, 1 ⟹ C                     Γ ; · ⟹ 1

      Γ ; Δ ⟹ A     Γ ; Δ′, B ⟹ C      Γ ; Δ, A ⟹ B
     ────────────────────────────── ⊸L ──────────────── ⊸R
         Γ ; Δ, Δ′, A ⊸ B ⟹ C          Γ ; Δ ⟹ A ⊸ B

      Γ ; Δ, A ⟹ C                     Γ ; Δ, B ⟹ C
     ────────────────── &L₁           ────────────────── &L₂
      Γ ; Δ, A & B ⟹ C                 Γ ; Δ, A & B ⟹ C

      Γ ; Δ ⟹ A     Γ ; Δ ⟹ B
     ───────────────────────── &R     ──────────── ⊤R        (no rule ⊤L)
          Γ ; Δ ⟹ A & B                Γ ; Δ ⟹ ⊤

      Γ ; Δ, A ⟹ C     Γ ; Δ, B ⟹ C
     ─────────────────────────────── ⊕L    ─────────────── 0L     (no rule 0R)
           Γ ; Δ, A ⊕ B ⟹ C                 Γ ; Δ, 0 ⟹ C

      Γ ; Δ ⟹ A                        Γ ; Δ ⟹ B
     ──────────────── ⊕R₁             ──────────────── ⊕R₂
      Γ ; Δ ⟹ A ⊕ B                    Γ ; Δ ⟹ A ⊕ B

      Γ, A ; Δ ⟹ C                     Γ ; · ⟹ A
     ──────────────── !L              ───────────── !R
      Γ ; Δ, !A ⟹ C                    Γ ; · ⟹ !A

      Γ ; Δ ⟹ A     Γ ; Δ′, A ⟹ C      Γ ; · ⟹ A     Γ, A ; Δ ⟹ C
     ────────────────────────────── cut ──────────────────────────── cut!
            Γ ; Δ, Δ′ ⟹ C                      Γ ; Δ ⟹ C

`·` is an empty zone. Six things to notice.

* **The linear zone has no weakening and no contraction.** init is
  `Γ ; A ⟹ A` with nothing else in the linear zone, and 1R asks that the
  linear zone be empty: a linear hypothesis that is not used cannot be
  dropped. Both structural rules fail as admissible rules too (section
  4.3).
* **The unrestricted zone has both, built in.** Every rule with no
  premise accepts any `Γ`, and every rule with two premises gives the
  whole of `Γ` to both.
* **copy is how a valid hypothesis is used.** It puts a copy of `A` in
  the linear zone and keeps `A` in `Γ`. Read upwards it always applies
  when `Γ` is not empty: a search that tries it has no bound (section
  8).
* **!L moves a formula into `Γ`; !R asks an empty linear zone.** To
  derive `!A` one may use valid hypotheses only: what is derived from
  linear ones cannot be had twice. So !L comes before !R (the second
  worked derivation below).
* **⊗R, ⊸L and cut divide the linear zone; &R and ⊕L share it.** Read
  upwards, a rule that divides asks which hypotheses go to which
  premise, and each goes to one.
* **Seven rules lose nothing, read upwards**: ⊗L, 1L, ⊸R, &R, ⊕L, !L,
  and !R where it applies (section 5.3). Each can be applied as soon as
  its formula is there. The others ask for a choice, and a wrong choice
  loses the derivation (exercises A7, B4).

**Exchange is not a rule.** In Lean the linear zone is a list read as a
multiset: a rule that takes a formula out of the linear zone concludes
any permutation of the zone the figure writes. The unrestricted zone is
a list read through membership: copy asks that `A` be a member of `Γ`.
So exchange in both zones, and weakening and contraction of `Γ`, are
functions on derivations and not constructors (section 4).

In Lean the calculus is an inductive family
[`Fam`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/System.lean#L35-L100 "DILL.Fam") `c : Seq → Type`, with one constructor for each
rule. `Fam true` has the two cuts; `Fam false`, also written
[`CF`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/System.lean#L102-L103 "DILL.CF"), is the figure as it stands. A term of `Fam c j` is
a derivation, as data: it can be measured, transformed and printed.
[`Derivable`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/System.lean#L120-L121 "DILL.Derivable") `j` says that `Fam true j` has an
element. A sequent is a [`Seq`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Form.lean#L82-L94 "DILL.Seq"): two lists and a formula.

### A worked derivation: `· ; !p ⟹ !p ⊗ !p`

A formula under `!` can be had twice. Read from the root upwards. Each
line is a sequent and the rule that concludes it; the premises of the
rule are the lines one step in, below it.

    · ; !p ⟹ !p ⊗ !p   by !L !p
      p ; · ⟹ !p ⊗ !p   by ⊗R !p ⊗ !p []
        p ; · ⟹ !p   by !R !p
          p ; · ⟹ p   by copy p
            p ; p ⟹ p   by init
        p ; · ⟹ !p   by !R !p
          p ; · ⟹ p   by copy p
            p ; p ⟹ p   by init

!L moves `p` to the unrestricted zone, and the linear zone is now empty.
⊗R divides it: the list in brackets is the part that goes to the first
premise, here nothing, and nothing is left for the second. Both premises
have the valid `p`. In each, !R applies because the linear zone is
empty, and copy brings a `p` into the linear zone for init. The
derivation has height 5 (a rule with no premise has height 1).

In the editor the same derivation is eight lines:

    def bangContract : Der S ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) := by
      dillmove bangL p
      dillmove tensorR (!p) (!p) []
      dillmove bangR p
      dillmove copy p
      dillmove init
      dillmove bangR p
      dillmove copy p
      dillmove init

| line | what it does |
|---|---|
| `dillmove` | lists the moves that apply at the first goal; none is made |
| `dillmove bangL` | makes the move if only one !L applies; otherwise offers each |
| `dillmove bangL p` | !L on `!p`: the argument is the formula under the `!` |
| `dillmove tensorR (!p) (!p) []` | ⊗R at the conclusion `!p ⊗ !p`; `[]` is the linear zone of the first premise, and the rest goes to the second |
| `dillmove lolliL p q [r]` | ⊸L on `p ⊸ q`; `[r]` goes to the premise that derives `p`, the rest stays with `q` |
| `dillmove cut A [Δ]`, `dillmove cutU A` | cut on `A`, with `Δ` for the premise that derives `A`; cut! on `A` |
| `dillmove init`, `dillmove oneR`, `dillmove topR`, `dillmove zeroL`, `dillmove oneL` | the rules that name nothing |
| `dillmove where` | draws the attempt so far |
| `#eval IO.println bangContract.render` | draws a finished derivation, as above |

A query lists the rules that lose nothing first, then the choices, then
a copy of each valid hypothesis; for ⊗R and ⊸L it lists every division
of the linear zone, and it lists no cut: the cut formula is yours to
choose. At the root of the worked derivation it says

    dillmove: at goal 0, 3 moves apply; no move is made. Try these:
      [apply] dillmove bangL p
      [apply] dillmove tensorR (!p) (!p) []
      [apply] dillmove tensorR (!p) (!p) [!p]

Either ⊗R, tried here, loses the derivation: `!p` goes to one premise,
and the other is `· ; · ⟹ !p`.

### A second worked derivation: `· ; !p, !(p ⊸ q) ⟹ !q`

`!` is a functor: from `!p` and `!(p ⊸ q)`, `!q`.

    · ; !p, !(p ⊸ q) ⟹ !q   by !L !p
      p ; !(p ⊸ q) ⟹ !q   by !L !(p ⊸ q)
        p ⊸ q, p ; · ⟹ !q   by !R !q
          p ⊸ q, p ; · ⟹ q   by copy (p ⊸ q)
            p ⊸ q, p ; p ⊸ q ⟹ q   by ⊸L p ⊸ q []
              p ⊸ q, p ; · ⟹ p   by copy p
                p ⊸ q, p ; p ⟹ p   by init
              p ⊸ q, p ; q ⟹ q   by init

At the root !R does not apply: the tactic answers
`the move does not apply to goal 0: !R: the linear zone is not empty`.
Both !L come first, and they lose nothing. Then !R, and the two valid
hypotheses are copied where they are wanted. ⊸L divides an empty rest:
its first premise derives `p` from the valid `p`, its second has `q`.
The height is 7.

What `dillmove` builds is a derivation of the explorer's proof system
[`S`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Proof.lean#L137-L141 "DILL.S"), whose moves are the twenty rules;
[`famOfDer`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Proof.lean#L212-L214 "DILL.famOfDer") carries it to a derivation in
`Fam true`, which is what the theorems are about.

<!-- lean: DILL.step_sound DILL.famToDer -->

    def DILL.step_sound : S.SoundT (Fam true)
      where ProofTools.Explore.ProofSystem.SoundT :=
        fun (S : ProofTools.Explore.ProofSystem) (T : S.Judg → Sort u) =>
          (m : S.Move) → (j : S.Judg) → (ps : List S.Judg) → S.step m j = Except.ok ps → ProofTools.Explore.Each T ps → T j

    theorem DILL.famToDer : FamToDer
      where DILL.FamToDer :=
        ∀ (j : DILL.Seq) (a : Fam true j), Nonempty (ProofTools.Explore.Der S j)

*Lean:* [`DILL.step_sound`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Proof.lean#L156-L210) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.famToDer`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Proof.lean#L348-L349) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED. The first says that each move that applies is a rule of
the calculus, applied to derivations of its premises: a derivation
built with the tactic is a derivation of the calculus. The second is
the converse: every instance of every rule is a move that the function
[`step`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Proof.lean#L132-L135 "DILL.step") allows, so nothing derivable is out of the
tactic's reach. The campaign's
[user's guide](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/campaign/users-guide.md)
has every line of the tactic and every message.

## 3. Exercises A and B: derivations, and resources

**Part A, derivations.**

* **A1** ★ Derive `· ; p ⟹ p`, then `· ; · ⟹ 1`, then `· ; p, q ⟹ ⊤`,
  then `· ; 0, p ⟹ q`: the four rules with no premise. Which two of
  them accept other linear hypotheses?
* **A2** ★ Derive `· ; p, p ⊸ q ⟹ q` (CCP, p. 16) and `· ; p & q ⟹ p`
  (p. 17). In the first the tactic offers two divisions: what does the
  other one leave?
* **A3** ★ Derive `p ; · ⟹ p` (CCP, p. 16), then `p ; · ⟹ p ⊗ p`. In
  the second, copy can come before ⊗R or after it. Which is the lower
  derivation?
* **A4** ★★ Three laws of `!`. Derive `· ; !p ⟹ p`, `· ; !p ⟹ 1` and
  `· ; !p ⟹ !!p`. In which is `p` never copied?
* **A5** ★★ Derive `· ; !(p & q) ⟹ !p ⊗ !q`, and its converse
  `· ; !p ⊗ !q ⟹ !(p & q)`. In the converse, how many rules come before
  !R can apply?
* **A6** ★★ Currying. Derive `· ; (p ⊗ q) ⊸ r ⟹ p ⊸ (q ⊸ r)` and
  `· ; p ⊸ (q ⊸ r) ⟹ (p ⊗ q) ⊸ r`. In the first, after ⊸R twice, ⊸L is
  offered with four divisions. Which one begins a derivation?
* **A7** ★★★ Derive `· ; (p ⊸ q) & (p ⊸ r) ⟹ p ⊸ (q & r)`. Three moves
  apply at the root. What happens if the first is &L₁?
* **A8** ★★ Derive `· ; p, q ⟹ q ⊗ p` with a cut on `p ⊗ q` as the
  last rule: the premises are `· ; p, q ⟹ p ⊗ q` and
  `· ; p ⊗ q ⟹ q ⊗ p`. Then derive it without cut, and compare the
  heights. Then derive `· ; · ⟹ (p ⊸ p) ⊗ (p ⊸ p)` with a cut! on
  `p ⊸ p` as the last rule: the lemma is derived once and used twice.
* **A9** ★★★ With `!A ⊸ B` for the type of functions, the S combinator
  is the sequent `· ; !(!p ⊸ (!q ⊸ r)), !(!p ⊸ q), !p ⟹ r`. Derive it.
  How many times is `p` copied, and where is `!q` made?

**Part B, resources.** What fails without weakening and contraction in
the linear zone, and what copy gives back.

* **B1** ★ `· ; p ⟹ 1` is not derivable. Which moves does the tactic
  offer? What does `dillmove oneR` say? Then derive `p ; · ⟹ 1`.
* **B2** ★★ `· ; p ⟹ p ⊗ p`. How many divisions are there, and what
  does each leave? Then derive `· ; !p ⟹ p ⊗ p`.
* **B3** ★★ `· ; p ⟹ !p` is not derivable: which moves are offered, and
  what does !R say? Derive `· ; !p ⟹ !p` in two ways. Then try
  `· ; !p, q ⟹ !(p ⊗ q)`: which move is offered after !L, and after
  that?
* **B4** ★★ `· ; p ⊸ (q ⊗ r) ⟹ (p ⊸ q) ⊗ (p ⊸ r)` is not derivable
  (Pfenning's lecture notes, p. 60). Three moves apply. Follow each, and
  say what it leaves that cannot be derived. Then put & for the ⊗ on
  both sides, and derive `· ; p ⊸ (q & r) ⟹ (p ⊸ q) & (p ⊸ r)`.
* **B5** ★★★ At `p ; · ⟹ q` one move is offered, and after it one move,
  and so on. An attempt that does not end is no proof that the sequent
  has no derivation. Give one. (Section 7 has a way.)

## 4. The structural properties

Each statement below is about the family `Fam c`, for both values of
`c`, or about `CF`. Where the Lean is a `def`, the statement is a
function on derivations: it takes derivations and returns one. The
goals were written as named types before any was proved, in
[`DILL/Statements.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/Statements.lean);
the campaign's
[`statements.md`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/campaign/statements.md)
has each with its source.

### 4.1 Exchange

<!-- lean: DILL.exchangeKeepsHeight DILL.exchangeUKeepsHeight -->

    theorem DILL.exchangeKeepsHeight : ExchangeKeepsHeight
      where DILL.ExchangeKeepsHeight :=
        ∀ (c : Bool) (Γ Δ Δ' : List Form) (C : Form) (e : Δ.Perm Δ') (d : Fam c (Γ ⨾ Δ ⟹ C)),
          (Fam.exch e d).height = d.height

    theorem DILL.exchangeUKeepsHeight : ExchangeUKeepsHeight
      where DILL.ExchangeUKeepsHeight :=
        ∀ (c : Bool) (Γ Γ' Δ : List Form) (C : Form),
          Γ.Perm Γ' → ∀ (d : Fam c (Γ ⨾ Δ ⟹ C)), ∃ (d' : Fam c (Γ' ⨾ Δ ⟹ C)), d'.height = d.height

*Lean:* [`DILL.exchangeKeepsHeight`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Results.lean#L32-L33) · PROVED · axioms: `propext`; [`DILL.exchangeUKeepsHeight`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Results.lean#L35-L37) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED. `Δ.Perm Δ'` says that `Δ'` is a permutation of `Δ`.
Exchange in the linear zone is the function
[`Fam.exch`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/System.lean#L155-L159 "DILL.Fam.exch"). A rule that takes its principal
formula out of the linear zone carries a proof that the zone of its
conclusion is a permutation of the zone the figure writes, and exchange
changes that proof and nothing above it; a rule that passes the whole
zone to its premises (copy, ⊸R, &R, the two ⊕R, cut!) passes the
exchange on. So the result has the same rules in the same places, and
the same height. Exchange in the unrestricted zone is an instance of
the next function.

### 4.2 Weakening and contraction of the unrestricted zone

<!-- lean: DILL.weakeningU DILL.contractionU -->

    def DILL.weakeningU : WeakeningU
      where DILL.WeakeningU :=
        (c : Bool) → (Γ Δ : List Form) → (A C : Form) → Fam c (Γ ⨾ Δ ⟹ C) → Fam c (A :: Γ ⨾ Δ ⟹ C)

    def DILL.contractionU : ContractionU
      where DILL.ContractionU :=
        (c : Bool) → (Γ Δ : List Form) → (A C : Form) → Fam c (A :: A :: Γ ⨾ Δ ⟹ C) → Fam c (A :: Γ ⨾ Δ ⟹ C)

*Lean:* [`DILL.weakeningU`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Results.lean#L26-L27) · PROVED · axioms: none; [`DILL.contractionU`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Results.lean#L29-L30) · PROVED · axioms: none

Both PROVED (CCP, Theorem 2). Both are instances of one function,
[`Fam.mono`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/System.lean#L198-L204 "DILL.Fam.mono"): a derivation at the unrestricted zone
`Γ` is a derivation at every `Γ′` that has the members of `Γ`. The
function is by recursion on the derivation. Only copy looks at `Γ`, and
it asks for membership, which `Γ′` still gives; at !L and at cut!, which
add a formula to the zone of a premise, the same formula is added on
both sides. Nothing else changes, so the height is kept. Weakening is
the case `Γ′ = A, Γ`; contraction is the case of `A, A, Γ` and `A, Γ`,
which have the same members.

### 4.3 Weakening and contraction of the linear zone: REFUTED

<!-- lean: DILL.not_weakeningL paraphrase -->

    weakening:      for every Γ, Δ, A and C,   if Γ ; Δ ⟹ C  then  Γ ; Δ, A ⟹ C
    refuted by:     · ; · ⟹ 1  is derivable,   · ; p ⟹ 1  is not

*Lean, in paraphrase:* [`DILL.not_weakeningL`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L34-L36) · PROVED · axioms: `Quot.sound`, `propext`

**REFUTED.** The statement is the proposition
[`WeakeningL`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Statements.lean#L53-L56 "DILL.WeakeningL"); the theorem in the caption is its
negation.

<!-- lean: DILL.not_contractionL paraphrase -->

    contraction:    for every Γ, Δ, A and C,   if Γ ; Δ, A, A ⟹ C  then  Γ ; Δ, A ⟹ C
    refuted by:     · ; p, p ⟹ p ⊗ p  is derivable,   · ; p ⟹ p ⊗ p  is not

*Lean, in paraphrase:* [`DILL.not_contractionL`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L38-L40) · PROVED · axioms: `Quot.sound`, `propext`

**REFUTED.** The statement is
[`ContractionL`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Statements.lean#L58-L61 "DILL.ContractionL"); the theorem in the caption is
its negation.

The source forbids both rules (CCP, p. 2). These two theorems say more:
neither is admissible. That `· ; p ⟹ 1` has no derivation without cut
is a case analysis on the last rule
([`not_cf_weak`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Results.lean#L307-L314 "DILL.not_cf_weak")): 1R asks an empty linear zone,
and every other rule asks for a conclusion or a hypothesis that is not
there. For `· ; p ⟹ p ⊗ p` the last rule can only be ⊗R, and one of its
two premises is `· ; · ⟹ p`
([`not_cf_contr`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Results.lean#L316-L334 "DILL.not_cf_contr")). Cut elimination (section
5.2) then carries each to the calculus with cut. Exercises B1 and B2 are
the two pairs, and exercise C7 refutes both sequents in a phase model.

## 5. Cut, and what follows from it

### 5.1 The two cuts, and cut elimination

There are two cuts because there are two kinds of hypothesis. The cut
on a linear hypothesis divides the linear zone, as ⊗R does. The cut on a
valid hypothesis, cut!, derives its formula from valid hypotheses alone,
as !R does, and its second premise may then use the formula any number
of times (CCP, Principle 7, items 2 and 1).

<!-- lean: DILL.cutAdmissible DILL.cutUAdmissible DILL.cutElimination -->

    def DILL.cutAdmissible : CutAdmissible
      where DILL.CutAdmissible :=
        (Γ Δ Δ' : List Form) → (A C : Form) → CF (Γ ⨾ Δ ⟹ A) → CF (Γ ⨾ A :: Δ' ⟹ C) → CF (Γ ⨾ Δ ++ Δ' ⟹ C)

    def DILL.cutUAdmissible : CutUAdmissible
      where DILL.CutUAdmissible :=
        (Γ Δ' : List Form) → (A C : Form) → CF (Γ ⨾ [] ⟹ A) → CF (A :: Γ ⨾ Δ' ⟹ C) → CF (Γ ⨾ Δ' ⟹ C)

    def DILL.cutElimination : CutElimination
      where DILL.CutElimination :=
        (j : DILL.Seq) → Fam true j → CF j

*Lean:* [`DILL.cutAdmissible`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Cut.lean#L354-L357) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.cutUAdmissible`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Cut.lean#L359-L362) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.cutElimination`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Cut.lean#L364-L389) · PROVED · axioms: `Quot.sound`, `propext`

All three PROVED, as functions
([`DILL/Cut.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/Cut.lean);
CCP, Theorem 3; Pfenning's notes, Theorems 3.8 and 3.9).
`cutElimination` is by recursion on the derivation: every rule but the
cuts is kept, on the results for its premises, and at a cut the
admissible cut is applied to the two results.

**The measure.** The two admissible cuts are proved together, by an
induction on three things in lexicographic order:

1. the size of the cut formula `A`;
2. at one formula, the kind of cut: the linear cut on `A` comes before
   the cut! on `A`;
3. the derivations of the premises.

In Lean each level is a structural recursion.
[`cutN`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Cut.lean#L342-L350 "DILL.Cut.cutN") is by recursion on a bound of the size of
`A`, and gives both cuts on `A` from both cuts on every smaller formula.

**The linear cut**, on `Γ ; Δ ⟹ A` and `Γ ; Δ′, A ⟹ C`. The function
[`pushR`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Cut.lean#L177-L292 "DILL.Cut.pushR") takes the cut up the right premise, the
one that has `A` as a hypothesis. Where the last rule there acts on
another formula, `A` is in the linear zone of one premise (⊗R, ⊸L), or
of both (&R, ⊕L), or of the one premise: the cut goes to the premises
that have `A`, and the same rule is applied below. Where the last rule
is a left rule on `A` itself, [`pushL`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Cut.lean#L98-L173 "DILL.Cut.pushL") takes over
and takes the cut up the left premise, past its left rules and copies,
to the right rule that introduced `A`. There the two rules meet, and
the cut is replaced by cuts on the immediate subformulas, which are
smaller:

    ⊗R against ⊗L     from  Γ ; Δ₁ ⟹ A₁,   Γ ; Δ₂ ⟹ A₂   and   Γ ; Δ′, A₁, A₂ ⟹ C:
                      a cut on A₁, then a cut on A₂
    ⊸R against ⊸L     from  Γ ; Δ, A₁ ⟹ A₂   and   Γ ; Δ₁ ⟹ A₁,   Γ ; Δ₂, A₂ ⟹ C:
                      a cut on A₁ gives  Γ ; Δ₁, Δ ⟹ A₂;  then a cut on A₂
    &R against &L₁    a cut on A₁;  the premise for A₂ is dropped
    ⊕R₁ against ⊕L    a cut on A₁, with the first premise of ⊕L
    1R against 1L     the premise of 1L is the result
    !R against !L     from  Γ ; · ⟹ A₁   and   Γ, A₁ ; Δ′ ⟹ C:
                      a cut! on A₁
    init              on either side:  the other derivation is the result

No rule introduces ⊤ on the left or 0 on the right, so those two have no
such case. The case of `!` is where the linear cut needs the other cut,
at a smaller formula.

**The cut on a valid hypothesis, and why it has an induction of its
own.** In `Γ ; · ⟹ A` and `Γ, A ; Δ ⟹ C`, the second premise may copy
`A` any number of times, in any of its branches, so one linear cut
cannot replace the cut!. The function [`pushU`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Cut.lean#L296-L331 "DILL.Cut.pushU") is
by recursion on the right premise, with the left premise fixed. Every
rule is applied again on the results for its premises. At a copy of `A`
the premise is `Γ, A ; Δ, A ⟹ C`: the recursion first removes the valid
`A` from it, giving `Γ ; Δ, A ⟹ C`, and the linear `A` that the copy
made is then cut against `Γ ; · ⟹ A` by the linear cut. That linear cut
is on `A` itself, not on a smaller formula, and there is one for each
copy. This is why the linear cut on `A` must be had before the cut! on
`A` (level 2 of the measure), and why the derivation of `Γ ; · ⟹ A` is
used once for every copy: the result can be much larger than the two
premises (exercise C2).

**Three zones.** Inside the recursion the two premises and the
conclusion have unrestricted zones of their own, `Γ₁`, `Γ₂` and `Γ′`,
with every member of `Γ₁` and of `Γ₂` a member of `Γ′`
([`CutLAt`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Cut.lean#L44-L49 "DILL.Cut.CutLAt")). When a cut passes !L, which adds a
formula to the zone of one premise, the zone of the conclusion grows and
the other premise is left as it is. With one shared `Γ` the other
premise would have to be weakened first, and the recursion would no
longer be on a part of what it was given.

**It computes.** The kernel evaluates the function. For the derivation
[`exBang`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Cut.lean#L414-L427 "DILL.Cut.exBang"), a cut on `!(p & p)` between
`· ; !p ⟹ !(p & p)` and `· ; !(p & p) ⟹ p ⊗ p`, in which the right
premise copies `p & p` twice:

    example : (cutElimination _ Cut.exBang).height = 4 := by decide +kernel

and the result has the rules `!L(⊗R(copy(init), copy(init)))`.

### 5.2 Cut elimination again, through the semantics

<!-- lean: DILL.cutEliminationProp -->

    theorem DILL.cutEliminationProp : CutEliminationProp
      where DILL.CutEliminationProp :=
        ∀ (j : DILL.Seq), Derivable j → Nonempty (CF j)

*Lean:* [`DILL.cutEliminationProp`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L309-L311) · PROVED · axioms: `Quot.sound`, `propext`

PROVED, in one line: a derivable sequent is valid (soundness, 7.2), and
a valid sequent has a derivation without cut (completeness, 7.3). This
proof gives no way to compute the derivation from the one it is given.
It does not depend on section 5.1, and the theorems below that carry a
fact from `CF` to the calculus with cut use it.

### 5.3 The invertible rules, and the two deduction theorems

<!-- lean: DILL.tensorLInv DILL.oneLInv DILL.lolliRInv DILL.withRInv DILL.plusLInv DILL.bangLInv DILL.bangRInv -->

    def DILL.tensorLInv : TensorLInv
      where DILL.TensorLInv :=
        (Γ Δ : List Form) → (A B C : Form) → CF (Γ ⨾ A ⊗ B :: Δ ⟹ C) → CF (Γ ⨾ A :: B :: Δ ⟹ C)

    def DILL.oneLInv : OneLInv
      where DILL.OneLInv :=
        (Γ Δ : List Form) → (C : Form) → CF (Γ ⨾ 𝟏 :: Δ ⟹ C) → CF (Γ ⨾ Δ ⟹ C)

    def DILL.lolliRInv : LolliRInv
      where DILL.LolliRInv :=
        (Γ Δ : List Form) → (A B : Form) → CF (Γ ⨾ Δ ⟹ A ⊸ B) → CF (Γ ⨾ A :: Δ ⟹ B)

    def DILL.withRInv : WithRInv
      where DILL.WithRInv :=
        (Γ Δ : List Form) → (A B : Form) → CF (Γ ⨾ Δ ⟹ A & B) → CF (Γ ⨾ Δ ⟹ A) × CF (Γ ⨾ Δ ⟹ B)

    def DILL.plusLInv : PlusLInv
      where DILL.PlusLInv :=
        (Γ Δ : List Form) → (A B C : Form) → CF (Γ ⨾ A ⊕ B :: Δ ⟹ C) → CF (Γ ⨾ A :: Δ ⟹ C) × CF (Γ ⨾ B :: Δ ⟹ C)

    def DILL.bangLInv : BangLInv
      where DILL.BangLInv :=
        (Γ Δ : List Form) → (A C : Form) → CF (Γ ⨾ !A :: Δ ⟹ C) → CF (A :: Γ ⨾ Δ ⟹ C)

    def DILL.bangRInv : BangRInv
      where DILL.BangRInv :=
        (Γ : List Form) → (A : Form) → CF (Γ ⨾ [] ⟹ !A) → CF (Γ ⨾ [] ⟹ A)

*Lean:* [`DILL.tensorLInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Invert.lean#L24-L26) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.oneLInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Invert.lean#L28-L30) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.lolliRInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Invert.lean#L33-L36) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.withRInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Invert.lean#L39-L45) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.plusLInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Invert.lean#L48-L52) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.bangLInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Invert.lean#L55-L59) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.bangRInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Invert.lean#L62-L66) · PROVED · axioms: `Quot.sound`, `propext`

All seven PROVED (CCP, Lemma 6), each by one admissible cut against a
small derivation, as the source proves them
([`DILL/Invert.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/Invert.lean)):

    ⊗L    against   Γ ; A, B ⟹ A ⊗ B
    1L    against   Γ ; · ⟹ 1
    ⊸R    against   Γ ; A ⊸ B, A ⟹ B
    &R    against   Γ ; A & B ⟹ A   and   Γ ; A & B ⟹ B
    ⊕L    against   Γ ; A ⟹ A ⊕ B   and   Γ ; B ⟹ A ⊕ B
    !L    after weakening by A, against   Γ, A ; · ⟹ !A
    !R    against   Γ ; !A ⟹ A

!R is inverted where the linear zone is empty, which is where the rule
applies. In what Lean prints above, `!A :: Δ` and `A ⊕ B :: Δ` are the
zones `(!A) :: Δ` and `(A ⊕ B) :: Δ`.

<!-- lean: DILL.deductionLinear DILL.deductionUnrestricted -->

    theorem DILL.deductionLinear : DeductionLinear
      where DILL.DeductionLinear :=
        ∀ (Γ Δ : List Form) (A B : Form), Derivable (Γ ⨾ A :: Δ ⟹ B) ↔ Derivable (Γ ⨾ Δ ⟹ A ⊸ B)

    theorem DILL.deductionUnrestricted : DeductionUnrestricted
      where DILL.DeductionUnrestricted :=
        ∀ (Γ Δ : List Form) (A C : Form), Derivable (A :: Γ ⨾ Δ ⟹ C) ↔ Derivable (Γ ⨾ !A :: Δ ⟹ C)

*Lean:* [`DILL.deductionLinear`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Invert.lean#L68-L72) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.deductionUnrestricted`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Invert.lean#L74-L78) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED. A linear hypothesis is discharged by ⊸, and a valid one by
`!` on the left: in each, one direction is the rule (⊸R, !L) and the
other its inversion, after cut elimination. Together they say that
`A₁, …, Aⱼ ; B₁, …, Bₖ ⟹ C` is derivable exactly when
`· ; · ⟹ !A₁ ⊸ … ⊸ !Aⱼ ⊸ B₁ ⊸ … ⊸ Bₖ ⊸ C` is.

### 5.4 The six rules that are not invertible: REFUTED

For each of the other six rules with a premise, the statement that the
rule is invertible is refuted by a sequent with the same connective on
both sides, as the source says (CCP, Lemma 6, and p. 18 for ⊸L).

<!-- lean: DILL.not_tensorRInv DILL.not_lolliLInv paraphrase -->

    ⊗R invertible:   if Γ ; Δ, Δ′ ⟹ A ⊗ B  then  Γ ; Δ ⟹ A  and  Γ ; Δ′ ⟹ B
    refuted by:      · ; p ⊗ q ⟹ p ⊗ q  is derivable;   with Δ = p ⊗ q and Δ′ empty,  · ; · ⟹ q  is not

    ⊸L invertible:   if Γ ; Δ, Δ′, A ⊸ B ⟹ C  then  Γ ; Δ ⟹ A  and  Γ ; Δ′, B ⟹ C
    refuted by:      · ; p ⊸ q ⟹ p ⊸ q  is derivable,   · ; · ⟹ p  is not

*Lean, in paraphrase:* [`DILL.not_tensorRInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L52-L57) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.not_lolliLInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L59-L65) · PROVED · axioms: `Quot.sound`, `propext`

<!-- lean: DILL.not_withL₁Inv DILL.not_withL₂Inv paraphrase -->

    &L₁ invertible:  if Γ ; Δ, A & B ⟹ C  then  Γ ; Δ, A ⟹ C
    refuted by:      · ; p & q ⟹ p & q  is derivable,   · ; p ⟹ p & q  is not

    &L₂ invertible:  if Γ ; Δ, A & B ⟹ C  then  Γ ; Δ, B ⟹ C
    refuted by:      · ; p & q ⟹ p & q  is derivable,   · ; q ⟹ p & q  is not

*Lean, in paraphrase:* [`DILL.not_withL₁Inv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L67-L71) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.not_withL₂Inv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L73-L77) · PROVED · axioms: `Quot.sound`, `propext`

<!-- lean: DILL.not_plusR₁Inv DILL.not_plusR₂Inv paraphrase -->

    ⊕R₁ invertible:  if Γ ; Δ ⟹ A ⊕ B  then  Γ ; Δ ⟹ A
    refuted by:      · ; p ⊕ q ⟹ p ⊕ q  is derivable,   · ; p ⊕ q ⟹ p  is not

    ⊕R₂ invertible:  if Γ ; Δ ⟹ A ⊕ B  then  Γ ; Δ ⟹ B
    refuted by:      · ; p ⊕ q ⟹ p ⊕ q  is derivable,   · ; p ⊕ q ⟹ q  is not

*Lean, in paraphrase:* [`DILL.not_plusR₁Inv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L79-L83) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.not_plusR₂Inv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L85-L89) · PROVED · axioms: `Quot.sound`, `propext`

**All six REFUTED.** The statements are the propositions
[`TensorRInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Statements.lean#L125-L128 "DILL.TensorRInv"),
[`LolliLInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Statements.lean#L130-L134 "DILL.LolliLInv"),
[`WithL₁Inv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Statements.lean#L136-L139 "DILL.WithL₁Inv"),
[`WithL₂Inv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Statements.lean#L141-L144 "DILL.WithL₂Inv"),
[`PlusR₁Inv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Statements.lean#L146-L148 "DILL.PlusR₁Inv") and
[`PlusR₂Inv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Statements.lean#L150-L152 "DILL.PlusR₂Inv"); each theorem in a caption is the
negation of one. Each fact about a particular sequent is decided by the
kernel, which runs the search of section 8.2: the sequents have no `!`
and an empty unrestricted zone. Cut elimination as a proposition carries
"no derivation without cut" to "no derivation".

### 5.5 init, from init at letters

<!-- lean: DILL.identityExpansion -->

    def DILL.identityExpansion : IdentityExpansion
      where DILL.IdentityExpansion :=
        (j : DILL.Seq) → CF j → { d : CF j // Fam.Atomic d }

*Lean:* [`DILL.identityExpansion`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Results.lean#L123-L124) · PROVED · axioms: `Quot.sound`, `propext`

PROVED. [`Fam.Atomic`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Statements.lean#L156-L177 "DILL.Fam.Atomic") `d` says that every
instance of init in `d` is at a letter. The function replaces each init
at `A` by the derivation [`idExp`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Results.lean#L43-L60 "DILL.Res.idExp") `A` of
`Γ ; A ⟹ A`, which is by recursion on `A`: the left rule of the
connective below its right rule, or the other way where the right rule
is the invertible one. For `A ⊗ B` it is ⊗L, then ⊗R with `A` to the
first premise; for `A ⊸ B` it is ⊸R, then ⊸L; for `A & B` it is &R, then
&L₁ in one premise and &L₂ in the other; for `1` it is 1L, then 1R; for
`⊤` and `0` one rule. For `!A` it is !L, then !R, then copy, and the
recursion goes on at the zone `Γ, A`: the unrestricted zone is a
parameter of the recursion for this case (exercise C1). The statement
says that a derivation with init at letters exists and is computed; it
does not relate it to the derivation given.

### 5.6 The subformula property

<!-- lean: DILL.subformulaProperty -->

    theorem DILL.subformulaProperty : SubformulaProperty
      where DILL.SubformulaProperty :=
        ∀ (j : DILL.Seq) (d : CF j),
          Fam.All (fun (j' : DILL.Seq) => ∀ (C : Form), C ∈ j'.forms → ∃ (D : Form), D ∈ j.forms ∧ C.IsSub D) d

*Lean:* [`DILL.subformulaProperty`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Results.lean#L240-L246) · PROVED · axioms: `Quot.sound`, `propext`

PROVED. [`Fam.All`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Statements.lean#L201-L225 "DILL.Fam.All") `P d` says that `P` holds of
every sequent of the derivation `d`; `j.forms` is the conclusion of `j`
with both its zones; and [`C.IsSub D`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Statements.lean#L185-L196 "DILL.Form.IsSub") says that
`C` is a subformula of `D`. The proof is by recursion on the derivation
without cut: read upwards, every rule of the figure replaces a formula
by its immediate subformulas, or copies one (copy), or moves one (!L).
The zones are pooled: the statement does not say in which zone, or on
which side, a subformula occurs.

### 5.7 Consistency, and the disjunction property

<!-- lean: DILL.consistency DILL.disjunctionProperty -->

    theorem DILL.consistency : Consistency
      where DILL.Consistency :=
        ¬Derivable ([] ⨾ [] ⟹ 𝟎)

    theorem DILL.disjunctionProperty : DisjunctionProperty
      where DILL.DisjunctionProperty :=
        ∀ (A B : Form), Derivable ([] ⨾ [] ⟹ A ⊕ B) → Derivable ([] ⨾ [] ⟹ A) ∨ Derivable ([] ⨾ [] ⟹ B)

*Lean:* [`DILL.consistency`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L20-L21) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.disjunctionProperty`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L23-L24) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED (Pfenning's notes, 3.11 and 3.12, stated there for natural
deduction). No rule of the figure concludes `· ; · ⟹ 0`: init and every
left rule ask for a linear hypothesis, copy for a valid one, and `0` has
no right rule ([`consistencyCF`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Results.lean#L268-L275 "DILL.consistencyCF")). A
derivation without cut of `· ; · ⟹ A ⊕ B` can end only with ⊕R₁ or
⊕R₂, for the same reasons
([`disjunctionCF`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Results.lean#L277-L292 "DILL.disjunctionCF"), a function: it returns the
derivation of `A` or that of `B`). Cut elimination supplies the
derivation without cut. With a hypothesis in either zone the disjunction
property fails (exercise C5).

## 6. The one-zone calculus, and the translation

One-zone intuitionistic linear logic is the family
[`ILL`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/ILL.lean#L24-L81 "DILL.ILL"): KOT's Figure 1, without the constant `⊥`. Its
sequents `Θ ⊢ C` have one multiset of hypotheses. Its rules for ⊗, 1,
⊸, &, ⊤, ⊕ and 0 are those of section 2 with the zone `Γ` removed, and
`!` has four rules:

      A, Θ ⊢ C              Θ ⊢ C              !A, !A, Θ ⊢ C          !Θ ⊢ A
     ─────────── !D        ─────────── !W      ─────────────── !C     ────────── !r
      !A, Θ ⊢ C             !A, Θ ⊢ C            !A, Θ ⊢ C            !Θ ⊢ !A

dereliction, weakening, contraction and promotion; in !r every
hypothesis is a `!` formula.

<!-- lean: DILL.toILL DILL.ofILL DILL.illEquivalence -->

    def DILL.toILL : ToILL
      where DILL.ToILL :=
        (c : Bool) → (Γ Δ : List Form) → (C : Form) → Fam c (Γ ⨾ Δ ⟹ C) → ILL c (List.map Form.bang Γ ++ Δ) C

    def DILL.ofILL : OfILL
      where DILL.OfILL :=
        (Γ Δ : List Form) → (C : Form) → ILL true (List.map Form.bang Γ ++ Δ) C → Fam true (Γ ⨾ Δ ⟹ C)

    theorem DILL.illEquivalence : ILLEquivalence
      where DILL.ILLEquivalence :=
        ∀ (Γ Δ : List Form) (C : Form), Derivable (Γ ⨾ Δ ⟹ C) ↔ ILLDerivable (List.map Form.bang Γ ++ Δ) C

*Lean:* [`DILL.toILL`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Translate.lean#L204-L205) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.ofILL`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Translate.lean#L207-L209) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.illEquivalence`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Translate.lean#L211-L213) · PROVED · axioms: `Quot.sound`, `propext`

All three PROVED (CCP, Theorem 7, items 3 and 1;
[`DILL/Translate.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/Translate.lean)).
`List.map Form.bang Γ ++ Δ` is the multiset `!Γ, Δ`. So

    Γ ; Δ ⟹ C   is derivable exactly when   !Γ, Δ ⊢ C   is.

**From two zones to one** ([`toILLAux`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Translate.lean#L79-L130 "DILL.Tr.toILLAux")), by
recursion on the derivation, for the calculus with cut and for the
calculus without: a derivation without cut is sent to one without Cut.

* A rule with no premise weakens every formula of `!Γ` (!W) below it.
* copy of `A` is !D on `!A`, then !C: the copy is derelicted and the
  original is kept.
* A rule with two premises gives `Γ` to both, so in the one-zone
  derivation `!Γ` arrives twice, and every formula of it is contracted
  below the rule.
* !L changes nothing: `!A` in the linear zone and `A` in the
  unrestricted zone are the same formula `!A` of the one zone.
* !R is !r. The cut is Cut. cut! is !r on its first premise, then Cut.

For example `p ; · ⟹ p ⊗ p`, by ⊗R above a copy and an init in each
premise, becomes the derivation of `!p ⊢ p ⊗ p` with the rules

    !C(⊗r(!C(!D(!W(id))), !C(!D(!W(id)))))

read from the last rule up: in each premise init weakens `!p`, copy
derelicts and contracts, and below ⊗r the two `!p` are contracted.

**From one zone to two**, in two steps. First a one-zone derivation of
`Θ ⊢ C` is read as a two-zone derivation of `· ; Θ ⟹ C`
([`ofILL0`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Translate.lean#L167-L198 "DILL.Tr.ofILL0")): !D is read as !L with copy as the
rule above it, and !W as !L alone; !C and !r use the inversion of !L,
which moves a `!A` of the linear zone into the unrestricted zone. Then the formulas `!Γ` of the linear zone
are moved into the unrestricted zone, again by the inversion of !L
([`unbangAll`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Translate.lean#L141-L146 "DILL.Tr.unbangAll")). The inversion used here
([`Tr.bangLInv`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Translate.lean#L134-L139 "DILL.Tr.bangLInv")) is a cut against
`Γ ; · ⟹ !A`, so this direction is stated for the calculi with cut.

One sequent of the one-zone calculus is several sequents here:
`!p ⊢ p ⊗ p` is `p ; · ⟹ p ⊗ p` and it is `· ; !p ⟹ p ⊗ p` (exercise
C6).

## 7. The phase semantics

Phase semantics is a semantics of provability: it interprets a formula
as a set of elements of a commutative monoid, and says which sequents
are derivable, and nothing about the derivations.

### 7.1 Phase spaces and models

An **intuitionistic phase space** (KOT, Definition 2.2;
[`PhaseSpace`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Semantics.lean#L16-L45 "DILL.PhaseSpace")) is a commutative monoid
`(M, ·, ε)`, whose elements are the phases, with a closure operator `Cl`
on sets of phases:

    X ⊆ Cl(X)        Cl(Cl(X)) ⊆ Cl(X)        X ⊆ Y  implies  Cl(X) ⊆ Cl(Y)
    Cl(X) · Cl(Y) ⊆ Cl(X · Y)                 where  X · Y = { x·y  :  x ∈ X, y ∈ Y }

A set is closed if it is its own closure. Two sets are fixed by the
space: `1 = Cl({ε})`, and `I`, the set of the idempotents of `1`, the
`x ∈ 1` with `x·x = x`.

A **phase model** ([`PhaseModel`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Semantics.lean#L68-L77 "DILL.PhaseModel"), KOT,
Definition 2.6) is a phase space with a closed set for each letter. It
gives every formula a closed set
([`interp`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Semantics.lean#L83-L97 "DILL.PhaseModel.interp")):

    ⟦p⟧      the set of p                ⟦1⟧      = Cl({ε})
    ⟦A ⊗ B⟧  = Cl(⟦A⟧ · ⟦B⟧)             ⟦A ⊸ B⟧  = { z  :  x·z ∈ ⟦B⟧  for every x ∈ ⟦A⟧ }
    ⟦A & B⟧  = ⟦A⟧ ∩ ⟦B⟧                 ⟦⊤⟧      = M
    ⟦A ⊕ B⟧  = Cl(⟦A⟧ ∪ ⟦B⟧)             ⟦0⟧      = Cl(∅)
    ⟦!A⟧     = Cl(⟦A⟧ ∩ I)

A sequent `G₁, …, Gₙ ; D₁, …, Dₘ ⟹ C` is read as the formula

    (!G₁ ⊗ … ⊗ !Gₙ ⊗ D₁ ⊗ … ⊗ Dₘ ⊗ 1) ⊸ C

([`Seq.form`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Semantics.lean#L106-L110 "DILL.Seq.form"); this reading of a two-zone sequent
is the campaign's, since KOT satisfy formulas only). It is **satisfied
in the model** if `ε` is in the interpretation of that formula
([`Sat`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Semantics.lean#L112-L115 "DILL.PhaseModel.Sat")), and **valid** if it is satisfied in
every model ([`Valid`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Semantics.lean#L117-L118 "DILL.Valid")). In Lean a set of phases is a
predicate, nothing asks that membership be decidable, and the theorems
below are proved with no excluded middle.

**The counting model.** Take the natural numbers under addition, with
every set closed. Then `1 = {0}`, and `I = {0}`: 0 is the one
idempotent. The product of two sets is the set of sums, `⟦!A⟧` is
`⟦A⟧ ∩ {0}`, and `z ∈ ⟦A ⊸ B⟧` when `x + z ∈ ⟦B⟧` for every `x ∈ ⟦A⟧`.
Give each letter one phase, its weight. With `⟦p⟧ = {1}`:

    ⟦p ⊗ 1⟧ = {1}        ⟦p ⊗ p⟧ = {2}        ⟦(p ⊗ 1) ⊸ (p ⊗ p)⟧ = { z : 1 + z = 2 } = {1}

and 0 is not in `{1}`: the sequent `· ; p ⟹ p ⊗ p` is not satisfied.
By soundness it has no derivation. The model counts: the hypotheses
weigh 1 and the conclusion 2. Exercise C7 goes on from here, to
sequents with `!`.

### 7.2 Soundness

<!-- lean: DILL.soundness -->

    theorem DILL.soundness : Soundness
      where DILL.Soundness :=
        ∀ (j : DILL.Seq), Derivable j → Valid j

*Lean:* [`DILL.soundness`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Soundness.lean#L335-L340) · PROVED · axioms: `Quot.sound`, `propext`

PROVED (KOT, Theorem 2.9, one half, there for the one-zone calculus),
for the calculus with both cuts, by induction on the derivation
([`DILL/Soundness.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/Soundness.lean)).
The proof first takes the formula of a sequent apart
([`sat_iff_holds`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Soundness.lean#L232-L234 "DILL.Sem.sat_iff_holds")): the sequent is
satisfied exactly when

    g·m ∈ ⟦C⟧     for every  g = g₁·…·gₙ  with  gᵢ ∈ ⟦Gᵢ⟧ ∩ I     and every  m = d₁·…·dₘ  with  dⱼ ∈ ⟦Dⱼ⟧

([`Holds`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Soundness.lean#L171-L175 "DILL.Sem.Holds")). The phase `g` of the unrestricted
zone is then an idempotent of `1`, and the twenty cases
([`holds_of_fam`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Soundness.lean#L238-L331 "DILL.Sem.holds_of_fam")) use that in three ways.

* `g ∈ 1`, and `1 · Y ⊆ Y` for a closed `Y`: so `g` may be dropped, as
  at init, where `g·a ∈ ⟦A⟧` for `a ∈ ⟦A⟧`. This is weakening of `Γ`.
* `g·g = g`: so `g·(m₁·m₂) = (g·m₁)·(g·m₂)`, and at ⊗R the two premises
  each have the whole of `g`. This is contraction of `Γ`, and why a rule
  with two premises may give `Γ` to both.
* `g` absorbs a phase of each of its formulas: for `A` in `Γ` there is
  `a ∈ ⟦A⟧` with `g·a = g`, namely the factor of `g` for `A`. So at copy
  the premise, applied to `g` and `a·m`, gives `g·a·m = g·m`.

At !R the linear zone is empty, so by induction `g ∈ ⟦A⟧`, and `g ∈ I`:
so `g ∈ ⟦A⟧ ∩ I ⊆ ⟦!A⟧`. At !L a phase of `⟦!A⟧` may be taken in
`⟦A⟧ ∩ I`, because `⟦C⟧` is closed, and it joins `g`.

### 7.3 Completeness, without cut

<!-- lean: DILL.completeness -->

    theorem DILL.completeness : Completeness
      where DILL.Completeness :=
        ∀ (j : DILL.Seq), Valid j → Nonempty (CF j)

*Lean:* [`DILL.completeness`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L303-L307) · PROVED · axioms: `Quot.sound`, `propext`

PROVED (KOT, Theorem 2.9 with Remark 2.11, there for the one-zone
calculus;
[`DILL/Completeness.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/Completeness.lean)).
The proof builds one model, the **canonical model**
([`synModel`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L143-L148 "DILL.Sem.synModel")), on the two-zone calculus
itself. No source read by the campaign builds it from two zones: the
construction follows KOT's for one zone.

* **The phases** are the pairs `(Γ, Δ)` of an unrestricted zone and a
  linear zone, where two pairs are the same phase if their first parts
  have the same members and their second parts are permutations of each
  other: a pair of a finite set and a finite multiset. The product puts
  two pairs side by side, and `ε` is `(·, ·)`.
* **The closed sets.** For a sequent `Γ′ ; Δ′ ⟹ C`, let
  `⟦Γ′ ; Δ′ ⟹ C⟧` be the set of the phases `(Γ, Δ)` such that
  `Γ, Γ′ ; Δ, Δ′ ⟹ C` has a derivation without cut
  ([`inF`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L74-L84 "DILL.Sem.inF")). The closure of a set `X` is the
  intersection of the sets of this family that contain `X`
  ([`synCl`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L111-L113 "DILL.Sem.synCl")). The family is closed under
  `X ↦ {y} ⊸ X`, which gives the fourth law of a closure (KOT, Theorem
  2.8).
* **The letters.** `⟦p⟧ = ⟦· ; · ⟹ p⟧`: the contexts that derive `p`.

**Why the idempotents are the unrestricted contexts.** `(Γ, Δ)·(Γ, Δ)`
is `(Γ, (Δ, Δ))`, since a set joined to itself is itself. So a phase is
idempotent exactly when `Δ, Δ` is a permutation of `Δ`, that is, when
`Δ` is empty ([`lin_nil_of_idem`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L180-L190 "DILL.Sem.lin_nil_of_idem")). And
every `(Γ, ·)` is in `1`: a set of the family that has `ε` has `(Γ, ·)`,
by weakening of the unrestricted zone
([`idem_cls`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L158-L169 "DILL.Sem.idem_cls")). So `I` is the set of the phases
`(Γ, ·)`. The two structural rules that the first zone has are what
makes its phases the idempotents of `1`, and that is the set that
interprets `!`.

<!-- lean: DILL.Sem.okada -->

    theorem DILL.Sem.okada (B : Form) :
      Sem.synModel.interp B (Sem.cls [] [B]) ∧ ∀ (p : Sem.synModel.M), Sem.synModel.interp B p → Sem.inF ([] ⨾ [] ⟹ B) p

*Lean:* [`DILL.Sem.okada`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L192-L278) · PROVED · axioms: `Quot.sound`, `propext`

PROVED: the main lemma (KOT, Lemma 2.10, after Okada), by induction on
the formula `B`. `cls [] [B]` is the phase `(·, B)`. The statement has
two halves:

    (·, B) ∈ ⟦B⟧        and        if (Γ, Δ) ∈ ⟦B⟧  then  Γ ; Δ ⟹ B  has a derivation without cut

Each case uses the two rules of its connective and no cut: the left
rule for the first half, the right rule for the second. For `A ⊗ B`:
by induction `(·, A) ∈ ⟦A⟧` and `(·, B) ∈ ⟦B⟧`, so `(·, (A, B))` is in
the product; a set `⟦Γ′ ; Δ′ ⟹ C⟧` that contains the product then has
`Γ′ ; A, B, Δ′ ⟹ C` derivable, and ⊗L gives `(·, A ⊗ B)` in it. For the
second half, phases of `⟦A⟧` and `⟦B⟧` derive `A` and `B`, and ⊗R,
after weakening both to the union of their first parts, derives `A ⊗ B`
from their product. For `!B`: the phase `(B, ·)` is in `⟦B⟧` by copy
([`interp_copy`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L171-L178 "DILL.Sem.interp_copy")) and is an idempotent of
`1`, and !L gives the first half; a phase of `⟦B⟧ ∩ I` is some `(Γ, ·)`
that derives `B`, and !R, which asks exactly for an empty linear zone,
gives the second.

Completeness follows ([`cf_of_sat`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L292-L299 "DILL.Sem.cf_of_sat")). By the
first half of the lemma, `(Γ, ·)` is a product of idempotent phases of
the formulas of `Γ`, and `(·, Δ)` a product of phases of the formulas of
`Δ`. If `Γ ; Δ ⟹ C` is valid it is satisfied in the canonical model, so
`(Γ, Δ) ∈ ⟦C⟧`, and by the second half `Γ ; Δ ⟹ C` has a derivation
without cut.

### 7.4 Validity is derivability

<!-- lean: DILL.Sem.valid_iff_derivable DILL.valid_perm -->

    theorem DILL.Sem.valid_iff_derivable (j : DILL.Seq) : Valid j ↔ Derivable j

    theorem DILL.valid_perm {Γ Γ' Δ Δ' : List Form} {C : Form} (eΓ : Γ.Perm Γ') (eΔ : Δ.Perm Δ') :
      Valid (Γ ⨾ Δ ⟹ C) ↔ Valid (Γ' ⨾ Δ' ⟹ C)

*Lean:* [`DILL.Sem.valid_iff_derivable`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L313-L315) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.valid_perm`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L93-L100) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED. The first is soundness and completeness together. The
second is there because the formula of a sequent is written through an
order of its hypotheses, `G₁` first and `Dₘ` last: it says that the
order does not matter. It is proved from the first, by exchange in the
two zones, and not in the semantics.

Validity quantifies over every monoid and every closure on it, and with
`!` there is no procedure that decides it (section 8.4). A logic that is
not decidable cannot have the finite model property, which MALL has;
it was not a goal here. A countermodel still refutes a sequent, one at
a time: the counting model above does, where no search of section 8
can (exercises B5 and C7).

### Exercises C: the theorems, used

* **C1** ★★ `c1 : CF ([] ⨾ [(!p) ⊗ 𝟏] ⟹ (!p) ⊗ 𝟏)` is one init, of
  height 1. From the recursion of 5.5, predict the rules of
  `(identityExpansion _ c1).1` and its height, then evaluate.
* **C2** ★★ Apply `cutElimination` to your two derivations of A8 that
  end with a cut. Before you evaluate: which derivations will it
  return? For the cut!, follow the case of copy in 5.1.
* **C3** ★★★★ Modus ponens for ⊸ is a derived rule. Write

      def mp {Γ : List Form} {A B : Form} (d₁ : CF (Γ ⨾ [] ⟹ A ⊸ B)) (d₂ : CF (Γ ⨾ [] ⟹ A)) :
          CF (Γ ⨾ [] ⟹ B)

* **C4** ★★★ `!` is a functor. Write, with no cut,

      def bangFunctor {Γ : List Form} {A B : Form} (d : CF (Γ ⨾ [A] ⟹ B)) : CF (Γ ⨾ [!A] ⟹ !B)

  Which theorem of section 4 does it need?
* **C5** ★★★ State the disjunction property for a sequent with a linear
  hypothesis, and refute it.
* **C6** ★★ Prove that `p ; · ⟹ p ⊗ p` is derivable exactly when
  `· ; !p ⟹ p ⊗ p` is, from `illEquivalence` alone. Then predict the
  rules of the one-zone derivation that `toILL` makes of your derivation
  of `p ; · ⟹ p` (A3).
* **C7** ★★★ In the counting model of 7.1 with `⟦p⟧ = {1}`, show that
  `· ; p ⟹ 1` is not satisfied. Then choose weights for `p` and `q` so
  that `· ; !p, q ⟹ !(p ⊗ q)` (B3) is not satisfied, and weights that
  refute `p ; · ⟹ q` (B5). What can a formula `!A` weigh?
* **C8** ★★★ Validity is closed under the linear cut:

      theorem valid_cut (Γ Δ Δ' : List Form) (A C : Form) (h₁ : Valid (Γ ⨾ Δ ⟹ A))
          (h₂ : Valid (Γ ⨾ A :: Δ' ⟹ C)) : Valid (Γ ⨾ Δ ++ Δ' ⟹ C)

  Prove it from the theorems of sections 5 and 7. At which model does
  your proof use the hypotheses?

## 8. What runs

Three things can be asked of a sequent in Lean, and each answer is
checked by the kernel. Two of them are certificates in the sense of the
project's method: a producer that is not trusted computes some data,
and a checker that is proved sound certifies it. They are a tree of
moves, for a derivation (8.1), and a saturated set of sequents, against
one (8.3). The third is a decision procedure that the kernel runs, with
nothing written (8.2). At each one below, the page says which it is.

### 8.1 A derivation, as a tree of moves; and the search that finds one

The certificate for a derivation is a **tree of moves**: the rules of
the derivation, with their principal formulas and their divisions, and
nothing else. The check runs `step` at the root and then at each
premise.

<!-- lean: DILL.treeCert DILL.scriptCert -->

    def DILL.treeCert : Certify.Certifier DILL.Seq (ProofTools.Explore.Cert S) (Fam true)

    def DILL.scriptCert : Certify.Certifier DILL.Seq (ProofTools.Explore.Script S) (Fam true)

*Lean:* [`DILL.treeCert`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Run.lean#L36-L38) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.scriptCert`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Run.lean#L40-L42) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED: a certifier is a check together with the proof that what
it accepts is so, here that a tree (or a script, the same moves in the
order they were made) which checks at `j` gives a derivation of `j`
with the cuts allowed. The soundness is `step_sound` of section 2. The
tree of the first worked derivation, checked by the kernel:

    def bangContractByTree : Fam true ([] ⨾ [!p] ⟹ (!p) ⊗ (!p)) :=
      treeCert.verdict _
        (.mk (.bangL p) [.mk (.tensorR (!p) (!p) [])
          [.mk (.bangR p) [.mk (.copy p) [.mk .init []]],
           .mk (.bangR p) [.mk (.copy p) [.mk .init []]]]])

A tree with a wrong move, or one that stops early, is rejected.

**The search.** [`Run.proveLazy`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Run.lean#L53-L59 "DILL.Run.proveLazy") `j n` is a
producer of trees
([`DILL/Lazy.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/Lazy.lean)):
a search without cut that applies the rules that lose nothing first,
and at ⊗R and ⊸L does not enumerate the divisions: it gives the whole
linear zone to one premise, which hands on what it did not use (Hodas
and Miller, 1994; Cervesato, Hodas and Pfenning, 2000). It is code and
is not trusted: what it returns is checked as above.

copy is what makes a search endless, so the number `n` is a **budget**:
the uses of copy allowed along one branch. For the two worked
derivations and the S combinator of A9:

    · ; !p ⟹ !p ⊗ !p                        found at budget 1, not at 0
    · ; !p, !(p ⊸ q) ⟹ !q                   found at budget 2, not at 1
    · ; !(!p ⊸ (!q ⊸ r)), !(!p ⊸ q), !p ⟹ r   found at budget 3, not at 2

and the trees it finds for the first two are the trees of section 2.
Where it finds nothing it has shown nothing: at `p ; · ⟹ q` it finds
nothing at any budget tried, and that is the same answer it gives to
the second sequent at budget 1. Its answer is "a derivation, here it
is" or "none at this budget", never "no". The driver `dillrun` runs it
over a corpus (`lake build dillrun`, then
`.lake/build/bin/dillrun status 3`), and the campaign's
[measurements](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/campaign/measurements.md)
have its times.

### 8.2 The decision, where `!` does not occur

<!-- lean: DILL.decideCF DILL.bangFreeDecidable DILL.Dec.search_complete -->

    def DILL.decideCF (Δ : List Form) (C : Form) (hbf : ∀ (A : Form), A ∈ C :: Δ → A.bangFree = true) :
      Decidable (Nonempty (CF ([] ⨾ Δ ⟹ C)))

    def DILL.bangFreeDecidable : BangFreeDecidable
      where DILL.BangFreeDecidable :=
        (Δ : List Form) → (C : Form) → (∀ (A : Form), A ∈ C :: Δ → A.bangFree = true) → Decidable (Derivable ([] ⨾ Δ ⟹ C))

    theorem DILL.Dec.search_complete (n : Nat) (Δ : List Form) (C : Form) :
      ssize Δ + C.size ≤ n → Dec.LBF (C :: Δ) → Nonempty (CF ([] ⨾ Δ ⟹ C)) → Option.isSome (Dec.search n Δ C) = true

*Lean:* [`DILL.decideCF`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Decide.lean#L514-L518) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.bangFreeDecidable`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Goals.lean#L26-L30) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.Dec.search_complete`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Decide.lean#L476-L497) · PROVED · axioms: `Quot.sound`, `propext`

All PROVED
([`DILL/Decide.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/Decide.lean)).
This one is not a certificate: it is a decision procedure that the
kernel runs. In a sequent `· ; Δ ⟹ C` in which `!` does not occur, copy
does not apply, nor do !L and !R, and no other rule changes the
unrestricted zone or brings in a `!`. Read upwards, every other rule
removes a connective or a constant, so the size of the sequent bounds
the height of a derivation without cut.
[`search`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Decide.lean#L284-L297 "DILL.Dec.search") `n Δ C` tries init, then the right rule
of the conclusion, then each hypothesis in turn as the principal
formula of its left rule; ⊗R and ⊸L try every division. It returns a
derivation, so it is sound by its type, and `search_complete` says that
it finds one whenever there is one. With cut elimination this decides
`Derivable` on the fragment.

Both restrictions are needed: a formula of the unrestricted zone is
under an implicit `!`. A statement of the form `Decidable …` has a
classical proof that searches nothing; what this one says is in its
bound on axioms, which has no axiom of choice, and in that the kernel
evaluates it:

    open DILL.Dec in
    example : Nonempty (CF ([] ⨾ [(p ⊸ q) & (p ⊸ r)] ⟹ p ⊸ (q & r))) := by decide

    open DILL.Dec in
    example : ¬ Nonempty (CF ([] ⨾ [p ⊸ (q ⊗ r)] ⟹ (p ⊸ q) ⊗ (p ⊸ r))) := by decide

For `Derivable`, with the cuts, go through
[`Sem.derivable_iff_cf`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Completeness.lean#L317-L318 "DILL.Sem.derivable_iff_cf"). On a sequent
with `!`, or with a valid hypothesis, `decide` finds no instance and
says `failed to synthesize Decidable …`. The search tries every
division, so it is slow where ⊗R or ⊸L must divide a long zone.

### 8.3 A saturated set of sequents, against a derivation

A finite set `D` of sequents is **saturated**
([`saturated`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Saturated.lean#L161-L163 "DILL.Sat.saturated")) when

* no member is the conclusion of a rule with no premise: none is an
  instance of init, of 1R, of ⊤R or of 0L;
* for every instance of a rule of the figure whose conclusion is a
  member, a premise of that instance is a member: the premise of ⊸R, of
  ⊗L, of 1L, of !L, of !R, and of copy for each valid hypothesis; one of
  the two premises of &R and of ⊕L; the premise of ⊕R₁ and that of ⊕R₂,
  both, and likewise &L₁ and &L₂; and, for every division of the linear
  zone at ⊗R and of the rest at ⊸L, one of the two premises.

A member is counted up to a permutation of its linear zone and up to
the members of its unrestricted zone. A saturated set is the record of
a search that fails: whatever rule is tried at a member, something it
needs is again a member.

<!-- lean: DILL.not_cf_of_refutedBy DILL.noCFBySet DILL.noDerivableBySet -->

    theorem DILL.not_cf_of_refutedBy (D : List DILL.Seq) (j : DILL.Seq) : refutedBy D j = true → ¬Nonempty (CF j)

    def DILL.noCFBySet : Certify.Certifier DILL.Seq (List DILL.Seq) fun (j : DILL.Seq) => Nonempty (CF j) → False

    def DILL.noDerivableBySet : Certify.Certifier DILL.Seq (List DILL.Seq) fun (j : DILL.Seq) => Derivable j → False

*Lean:* [`DILL.not_cf_of_refutedBy`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Saturated.lean#L409-L416) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.noCFBySet`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/SatRun.lean#L27-L30) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.noDerivableBySet`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/SatRun.lean#L32-L36) · PROVED · axioms: `Quot.sound`, `propext`

All PROVED
([`DILL/Saturated.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/Saturated.lean),
[`DILL/SatRun.lean`](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/DILL/SatRun.lean)).
[`refutedBy`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Saturated.lean#L167-L169 "DILL.refutedBy") `D j` is the check: `j` is a member
of `D`, and `D` is saturated. This is the second certificate: a set of
sequents, written as data, against a derivation.

**Why a saturated set refutes, with no semantics.** Suppose a member of
`D` had a derivation without cut, and take one of least height. Its
last rule is an instance of a rule whose conclusion is that member. It
is not a rule with no premise, by the first condition. So by the second
condition one of its premises is a member of `D`, and that premise has
a derivation of smaller height. In Lean this is an induction on the
derivation, for every sequent that the rules do not tell apart from a
member. No model is built and no cut is used; the certifier for
`Derivable` adds cut elimination. (In the campaign for MALL the same
certificate was proved sound through a phase model. Here the proof is
from the rules alone, and the set presents no model.)

Two sets, checked by the kernel:

    theorem d4a : ¬ Derivable ([] ⨾ [p] ⟹ p ⊗ p) :=
      noDerivableBySet.verdict _ [[] ⨾ [p] ⟹ p ⊗ p, [] ⨾ [] ⟹ p]

    theorem no_bang_p : ¬ Derivable ([] ⨾ [] ⟹ !p) :=
      noDerivableBySet.verdict _ [[] ⨾ [] ⟹ !p, [] ⨾ [] ⟹ p]

In the first, each of the two divisions at ⊗R has `· ; · ⟹ p` as a
premise, and that sequent asks for nothing. Without it the check
rejects the set, and with `· ; p ⟹ p` added it rejects the set too: an
instance of init is a member.

**What it cannot refute.**

<!-- lean: DILL.Sat.unr_nil DILL.Sat.no_bang -->

    theorem DILL.Sat.unr_nil {D : List DILL.Seq} (hs : Sat.saturated D = true) {k : DILL.Seq} (hk : k ∈ D) : k.unr = []

    theorem DILL.Sat.no_bang {D : List DILL.Seq} (hs : Sat.saturated D = true) {k : DILL.Seq} (hk : k ∈ D) (A : Form) :
      ¬!A ∈ k.lin

*Lean:* [`DILL.Sat.unr_nil`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Saturated.lean#L382-L393) · PROVED · axioms: `Quot.sound`, `propext`; [`DILL.Sat.no_bang`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Saturated.lean#L395-L405) · PROVED · axioms: `Quot.sound`, `propext`

Both PROVED. A member with a formula `A` in its unrestricted zone asks
for the premise of copy, whose linear zone is longer by `A`, and that
member asks for the next: a finite set cannot have them all. So no
member of a saturated set has a valid hypothesis, and none has a `!A`
in its linear zone, since the premise of !L has `A` valid (`¬!A ∈ k.lin`
is Lean's printing of `(!A) ∉ k.lin`). The certificate is for the
sequents with an empty unrestricted zone whose failed search never
meets a `!` on the left. A `!` on the right is no obstacle.

The producer is [`refuteSet`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Refute.lean#L234-L241 "DILL.refuteSet"): a search that
remembers every sequent it settles, and returns those it answered "no"
of. It is not trusted, and that it finds a set wherever there is one is
not proved. For the sequent of B4 it returns eight sequents. The
kernel's check compares each premise with the whole set, and a set
grows quickly where ⊗R and ⊸L divide a long zone: the campaign's
[measurements](https://github.com/fairflow/proof-tools/blob/main/calculi/DILL/campaign/measurements-sat.md)
have the frontier, and on the family measured there the decision of 8.2
is the cheaper of the two.

### 8.4 Why there is no complete answer with `!`

Derivability in intuitionistic linear logic with `!` is undecidable:
P. Lincoln, J. Mitchell, A. Scedrov and N. Shankar, *Decision problems
for propositional linear logic*, Annals of Pure and Applied Logic 56
(1992), Corollary 3.8. It is cited here, not proved: the proof encodes
machines, and the corollary itself rests on a conservativity result that
the paper says it does not prove. As the campaign's survey reads the
encoding, its sequents use ⊸, ⊗, ⊕ and `!` on the left only, and by
section 6 they are sequents of this calculus.

So no pair of a sound check for derivations and a sound check against
them can have producers that between them always answer: that would be
a decision procedure. Here the search of 8.1 answers "yes" where it
finds a derivation within its budget, the saturated sets of 8.3 answer
"no" on part of the fragment where copy and !L are never met, and
between them is a region where neither answers. The two are joined in
one engine, [`dillEngine`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Engine.lean#L44-L47 "DILL.dillEngine"), whose producer
([`produce`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Engine.lean#L33-L42 "DILL.produce")) answers `pass` with a script, `fail`
with a saturated set, or `flag`:

    · ; !p ⟹ !p ⊗ !p              at budget 2:   pass
    · ; p ⟹ p ⊗ p                 at budget 2:   fail
    p ; · ⟹ q                      at budget 2:   flag
    · ; !p, q ⟹ !(p ⊗ q)          at budget 2:   flag
    · ; !p, !(p ⊸ q) ⟹ !q         at budget 1:   flag;   at budget 2:   pass

A `flag` is not "no". The two flagged sequents have no derivation, and
what shows it is a countermodel (section 7.1, exercise C7), written by
hand: the campaign has no producer of countermodels.

<!-- lean: DILL.decidedBangFree -->

    theorem DILL.decidedBangFree (Δ : List Form) (C : Form) (hb : ∀ (A : Form), A ∈ C :: Δ → A.bangFree = true) :
      (∃ (c : ProofTools.Explore.Cert S), treeCert.check ([] ⨾ Δ ⟹ C) c = true) ∨
        noDerivableDec.check ([] ⨾ Δ ⟹ C) () = true

*Lean:* [`DILL.decidedBangFree`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Engine.lean#L77-L97) · PROVED · axioms: `Quot.sound`, `propext`

PROVED: where `!` does not occur and the unrestricted zone is empty,
one side always answers. There the answer against a derivation is the
decision of 8.2 run by the kernel
([`noDerivableDec`](https://github.com/fairflow/proof-tools/blob/65cc6df/calculi/DILL/DILL/Engine.lean#L69-L75 "DILL.noDerivableDec")), with no certificate
written.

### Exercises D: what runs

* **D1** ★ State and prove by `decide` that one sequent of Part A has a
  derivation without cut, and that one of Part B has none. For which
  sequents of Parts A and B can this not be done?
* **D2** ★★ Write by hand the tree of moves of your derivation of
  `· ; !p ⟹ p ⊗ p` (B2), and have the kernel check it with
  `treeCert.verdict`. Then leave out the second copy: what does the
  check answer?
* **D3** ★★ Evaluate `(Run.proveLazy j n).isSome` on the second worked
  derivation of section 2 for `n` from 0 to 3. Why is the least budget
  2? Predict the least budget for the S combinator of A9, then
  evaluate. What does the answer at `p ; · ⟹ q` with budget 5 show?
* **D4** ★★ Write by hand a saturated set for `· ; p ⟹ p ⊗ p`, and one
  for `· ; · ⟹ !p`, and have the kernel check each with
  `noDerivableBySet.verdict`. In the first, why is the set of the one
  sequent rejected?
* **D5** ★★★ Why has `p ; · ⟹ q` no saturated set? Why has
  `· ; !p, q ⟹ !(p ⊗ q)`? What does `refuteSet` answer at each, and
  what does prove that they have no derivation?

## 9. What rests on what

| claim | what stands behind it |
|---|---|
| the theorems of sections 2 and 4 to 8 | the kernel, with no `sorry`, within `propext` and `Quot.sound`; each statement and status is printed by Lean and pinned in `DILL/TutorialPins.lean` |
| that the eight statements of 4.3 and 5.4 are REFUTED | the eight negations are theorems; the facts about the sequents are decided by the kernel running the proved search of 8.2, or by a case analysis, and cut elimination as a proposition carries them to the calculus with cut |
| that `Fam` is the calculus of the source | a reading of the Lean against CCP's Figure 2, made a second time by a reader given only page images of the figure; no difference was found, and the misprint of section 1 was found again. The rule table has both |
| that `Valid` is validity in intuitionistic phase semantics | the definitions of 7.1, read back once by a reader given only the definitions and the statements; and that soundness and completeness both hold for them. The formula of a two-zone sequent is the campaign's own reading, and `valid_perm` says that the order it fixes does not matter |
| that cut elimination computes | the function is by structural recursion, and the kernel evaluates it on derivations with a cut (5.1) |
| the completeness proof | the canonical model on two zones is the campaign's construction, after KOT's for one zone; what backs it is the kernel, not a source |
| undecidability with `!` | not proved here: Lincoln, Mitchell, Scedrov and Shankar, Corollary 3.8, cited (8.4) |
| the solutions below | each is compiled by the build; where a height, a message or a list of rules is quoted it is pinned by a test |

The record of the adoption, with every decision and its cost to
reverse, is in the campaign's
[folder](https://github.com/fairflow/proof-tools/tree/main/calculi/DILL/campaign).

## 10. Solutions

Derivations are given as the lines typed after `dillmove`.

### Part A

**A1.** `init`; `oneR`; `topR`; `zeroL`. ⊤R and 0L accept any other
linear hypotheses. init and 1R do not: at `· ; p, q ⟹ p` no move
applies, and init answers
`init: the linear zone is not exactly the conclusion`. All four accept
any unrestricted zone.

**A2.** `lolliL p q [p]`, `init`, `init`: the list `[p]` is the linear
zone of the premise that derives `p`, and nothing is left beside `q` in
the other. The other division, `lolliL p q []`, leaves `· ; · ⟹ p` and
`· ; q, p ⟹ q`, and neither is derivable. For the second: `withL₁ p q`,
`init`.

**A3.** `copy p`, `init`. For `p ; · ⟹ p ⊗ p`: `tensorR p p []`,
`copy p`, `init`, `copy p`, `init`, of height 3; or `copy p`, `copy p`,
`tensorR p p [p]`, `init`, `init`, of height 4. ⊗R first is lower: the
two copies are then side by side, in the two premises.

**A4.** `bangL p`, `copy p`, `init`. Then `bangL p`, `oneR`: the valid
`p` is not used, and 1R accepts any unrestricted zone. Then `bangL p`,
`bangR (!p)`, `bangR p`, `copy p`, `init`: after !L the linear zone is
empty, so !R applies, twice. In the second `p` is never copied.

**A5.** `bangL (p & q)`, `tensorR (!p) (!q) []`, `bangR p`,
`copy (p & q)`, `withL₁ p q`, `init`, `bangR q`, `copy (p & q)`,
`withL₂ p q`, `init`: the valid `p & q` is copied once in each premise,
and projected. For the converse: `tensorL (!p) (!q)`, `bangL p`,
`bangL q`, `bangR (p & q)`, `withR p q`, `copy p`, `init`, `copy q`,
`init`. Three rules come before !R: ⊗L, and !L twice. Until the linear
zone is empty !R is refused.

**A6.** `lolliR p (q ⊸ r)`, `lolliR q r`, `lolliL (p ⊗ q) r [q, p]`,
`tensorR p q [p]`, `init`, `init`, `init`. The four divisions offered
are `[]`, `[p]`, `[q]` and `[q, p]`; the premise that derives `p ⊗ q`
needs both hypotheses, so only `[q, p]` begins a derivation. For the
second: `lolliR (p ⊗ q) r`, `tensorL p q`, `lolliL p (q ⊸ r) [p]`,
`init`, `lolliL q r [q]`, `init`, `init`.

**A7.** `lolliR p (q & r)`, `withR q r`, `withL₁ (p ⊸ q) (p ⊸ r)`,
`lolliL p q [p]`, `init`, `init`, `withL₂ (p ⊸ q) (p ⊸ r)`,
`lolliL p r [p]`, `init`, `init`. Drawn:

    · ; (p ⊸ q) & (p ⊸ r) ⟹ p ⊸ (q & r)   by ⊸R p ⊸ (q & r)
      · ; p, (p ⊸ q) & (p ⊸ r) ⟹ q & r   by &R q & r
        · ; p, (p ⊸ q) & (p ⊸ r) ⟹ q   by &L₁ (p ⊸ q) & (p ⊸ r)
          · ; p ⊸ q, p ⟹ q   by ⊸L p ⊸ q [p]
            · ; p ⟹ p   by init
            · ; q ⟹ q   by init
        · ; p, (p ⊸ q) & (p ⊸ r) ⟹ r   by &L₂ (p ⊸ q) & (p ⊸ r)
          · ; p ⊸ r, p ⟹ r   by ⊸L p ⊸ r [p]
            · ; p ⟹ p   by init
            · ; r ⟹ r   by init

If &L₁ is the first move it leaves `· ; p ⊸ q ⟹ p ⊸ (q & r)`, which is
not derivable: the side of & was chosen before &R had said which of `q`
and `r` is wanted, and the two premises of &R want different sides. The
rules that lose nothing go first: the query lists them first.

**A8.** `cut (p ⊗ q) [p, q]`, `tensorR p q [p]`, `init`, `init`,
`tensorL p q`, `tensorR q p [q]`, `init`, `init`. Without cut:
`tensorR q p [q]`, `init`, `init`. The heights are 4 and 2. With cut!:
`cutU (p ⊸ p)`, `lolliR p p`, `init`, `tensorR (p ⊸ p) (p ⊸ p) []`,
`copy (p ⊸ p)`, `init`, `copy (p ⊸ p)`, `init`, of height 4.

**A9.** `bangL ((!p) ⊸ ((!q) ⊸ r))`, `bangL ((!p) ⊸ q)`, `bangL p`,
`copy ((!p) ⊸ ((!q) ⊸ r))`, `lolliL (!p) ((!q) ⊸ r) []`, `bangR p`,
`copy p`, `init`, `lolliL (!q) r []`, `bangR q`, `copy ((!p) ⊸ q)`,
`lolliL (!p) q []`, `bangR p`, `copy p`, `init`, `init`, `init`. The
height is 12. `p` is copied twice, once for each function that takes
it, and each time under a !R: an argument of type `!p` is made from the
valid `p`. `!q` is made by !R above the second ⊸L, from the valid
hypotheses alone, and that is why the three !L come first: every ⊸L
here divides an empty linear zone.

### Part B

**B1.** None: the query answers
`dillmove: no move applies at goal 0`, and `dillmove oneR` answers
`the move does not apply to goal 0: 1R: the linear zone is not empty`.
`p ; · ⟹ 1` is one move, `oneR`: a valid hypothesis need not be used.

**B2.** Two divisions, `[]` and `[p]`. Each leaves `· ; p ⟹ p` and
`· ; · ⟹ p`, in one order or the other: the one `p` goes to one side
only, and at `· ; · ⟹ p` no move applies. For `· ; !p ⟹ p ⊗ p`:
`bangL p`, `tensorR p p []`, `copy p`, `init`, `copy p`, `init`.

**B3.** None is offered, and `dillmove bangR p` answers
`the move does not apply to goal 0: !R: the linear zone is not empty`.
`· ; !p ⟹ !p` is `init`; or `bangL p`, `bangR p`, `copy p`, `init`. At
`· ; !p, q ⟹ !(p ⊗ q)` the one move offered is `bangL p`, and after it
the one move offered is `copy p`, and after that `copy p` again: copy
adds to the linear zone and nothing removes `q` from it, so !R never
applies. That is not yet a proof that the sequent has no derivation
(B5); C7 gives one.

**B4.** `tensorR (p ⊸ q) (p ⊸ r) []` leaves `· ; · ⟹ p ⊸ q` and
`· ; p ⊸ (q ⊗ r) ⟹ p ⊸ r`, and the first is not derivable. The other
division leaves `· ; · ⟹ p ⊸ r` as its second premise.
`lolliL p (q ⊗ r) []` leaves `· ; · ⟹ p`, where no move applies. The
one hypothesis can be used once, and the conclusion asks for it in both
factors. With &: `withR (p ⊸ q) (p ⊸ r)`, `lolliR p q`,
`lolliL p (q & r) [p]`, `init`, `withL₁ q r`, `init`, `lolliR p r`,
`lolliL p (q & r) [p]`, `init`, `withL₂ q r`, `init`: &R gives the
hypothesis to both premises.

**B5.** The move is `copy p`, at every step: the goals are
`p ; · ⟹ q`, `p ; p ⟹ q`, `p ; p, p ⟹ q`, and so on. A proof that there
is no derivation: the sequent is not satisfied in the counting model
with `p` of weight 0 and `q` of weight 1, where
`⟦(!p ⊗ 1) ⊸ q⟧ = {0} ⊸ {1} = {1}`, and soundness does the rest.

    theorem b5 : ¬ Derivable ([p] ⨾ [] ⟹ q) := fun h => b5_not_sat (soundness _ h _)

A syntactic proof is an induction on a derivation without cut, for all
the sequents `p ; p, …, p ⟹ q` at once; it is not written in the Lean.

### Part C

**C1.** `⊗L(⊗R(!L(!R(copy(init))), 1L(1R)))`, of height 6. The
expansion of init at `!p` is !L, !R, copy, init, of height 4; at `1` it
is 1L, 1R; at `!p ⊗ 1` it is ⊗L, then ⊗R above the two: two more than
the higher.

**C2.** For the cut on `p ⊗ q`: `⊗R(init, init)`, the derivation
without cut of A8, of height 2. The right premise ends with ⊗L on the
cut formula and the left premise with ⊗R, the two meet, and the cuts on
`p` and on `q` are each against an init. For the cut!:
`⊗R(⊸R(init), ⊸R(init))`, of height 3. The right premise is ⊗R above
two copies of `p ⊸ p`, each above an init; at each copy the linear cut
on `p ⊸ p` against an init returns the derivation of the lemma. The
lemma's derivation is there twice.

**C3.** Invert ⊸R in the first derivation to get `Γ ; A ⟹ B`; cut on
`A` with the second.

    def mp {Γ : List Form} {A B : Form} (d₁ : CF (Γ ⨾ [] ⟹ A ⊸ B)) (d₂ : CF (Γ ⨾ [] ⟹ A)) :
        CF (Γ ⨾ [] ⟹ B) :=
      cutAdmissible Γ [] [] A B d₂ (lolliRInv Γ [] A B d₁)

**C4.** !L, then !R, then copy: the given derivation is wanted at the
zone `A, Γ`, which is weakening of the unrestricted zone (4.2).

    def bangFunctor {Γ : List Form} {A B : Form} (d : CF (Γ ⨾ [A] ⟹ B)) : CF (Γ ⨾ [!A] ⟹ !B) :=
      .bangL A [] (.refl _) (.bangR (.refl _) (.copy A (.head _) (d.weakenU A)))

**C5.** With a linear zone `Δ` the statement would be: if
`· ; Δ ⟹ A ⊕ B` is derivable then `· ; Δ ⟹ A` or `· ; Δ ⟹ B` is. The
instance of 5.4 refutes it: `· ; p ⊕ q ⟹ p ⊕ q` is derivable and
neither `· ; p ⊕ q ⟹ p` nor `· ; p ⊕ q ⟹ q` is. ⊕L on the hypothesis
comes below the choice of a side.

    open DILL.Dec in
    theorem no_disjunction_in_context :
        ¬ ∀ (A B : Form) (Δ : List Form), Derivable ([] ⨾ Δ ⟹ A ⊕ B) →
          Derivable ([] ⨾ Δ ⟹ A) ∨ Derivable ([] ⨾ Δ ⟹ B) := fun h =>
      (h p q [p ⊕ q] ((Sem.derivable_iff_cf _).2 (by decide))).elim
        (fun h₁ => absurd ((Sem.derivable_iff_cf _).1 h₁) (by decide))
        (fun h₂ => absurd ((Sem.derivable_iff_cf _).1 h₂) (by decide))

**C6.** Both sequents are the one-zone sequent `!p ⊢ p ⊗ p`:

    theorem c6 : Derivable ([p] ⨾ [] ⟹ p ⊗ p) ↔ Derivable ([] ⨾ [!p] ⟹ p ⊗ p) :=
      (illEquivalence [p] [] (p ⊗ p)).trans (illEquivalence [] [!p] (p ⊗ p)).symm

The derivation of `p ; · ⟹ p`, copy above init, becomes
`!C(!D(!W(id)))`: init weakens `!p`, and copy derelicts the copy and
contracts it with the original.

**C7.** `⟦(p ⊗ 1) ⊸ 1⟧ = {1} ⊸ {0}`, the set of `z` with `1 + z = 0`,
which is empty: the hypothesis weighs 1 and the conclusion 0. For
`· ; !p, q ⟹ !(p ⊗ q)` take `p` of weight 0 and `q` of weight 1: then
`⟦!p⟧ = {0}`, the hypotheses have the phase 1, and
`⟦!(p ⊗ q)⟧ = {1} ∩ {0}` is empty. The same weights refute
`p ; · ⟹ q` (B5). A formula `!A` weighs 0 or its set is empty: its
phases are idempotent. So a letter under a `!` that is to be used must
weigh 0, and the model counts the linear hypotheses only.

    theorem c7c : ¬ (countModel w01).Sat ([] ⨾ [!p, q] ⟹ !(p ⊗ q))

with `countModel` the counting model as a `PhaseModel` (in
`DILL/TutorialTest.lean`); the three proofs are a few lines each.

**C8.** Completeness turns each hypothesis into a derivation without
cut; `cutAdmissible` joins them; soundness returns to validity.

    theorem valid_cut (Γ Δ Δ' : List Form) (A C : Form) (h₁ : Valid (Γ ⨾ Δ ⟹ A))
        (h₂ : Valid (Γ ⨾ A :: Δ' ⟹ C)) : Valid (Γ ⨾ Δ ++ Δ' ⟹ C) :=
      let ⟨d₁⟩ := completeness _ h₁
      let ⟨d₂⟩ := completeness _ h₂
      soundness _ ⟨(cutAdmissible Γ Δ Δ' A C d₁ d₂).lift⟩

The hypotheses are used at one model only, the canonical model of 7.3.
A direct proof, in an arbitrary model, is the case of cut in the proof
of soundness.

### Part D

**D1.** As in 8.2: for instance

    open DILL.Dec in
    example : Nonempty (CF ([] ⨾ [p, p ⊸ q] ⟹ q)) := by decide

    open DILL.Dec in
    example : ¬ Nonempty (CF ([] ⨾ [p] ⟹ 𝟏)) := by decide

It cannot be done for a sequent with `!` or with a valid hypothesis:
A3, A4, A5, A9, the second halves of B1 and B2, B3 and B5.

**D2.**

    def d2 : Fam true ([] ⨾ [!p] ⟹ p ⊗ p) :=
      treeCert.verdict _
        (.mk (.bangL p) [.mk (.tensorR p p [])
          [.mk (.copy p) [.mk .init []], .mk (.copy p) [.mk .init []]]])

With `.mk .init []` in the place of the second copy the check answers
`false`: init is tried at `p ; · ⟹ p`, whose linear zone is empty.

**D3.** `[false, false, true, true]`. The budget counts the copies
along one branch, and the branch of the worked derivation that goes
through the first premise of ⊸L has two: `p ⊸ q`, then `p`. For the S
combinator the least budget is 3: the deepest branch copies the first
function, then the second, then `p`. At `p ; · ⟹ q` the search finds
nothing at budget 5, as at every budget: that shows nothing. It is the
answer the search gives to a derivable sequent below its budget.

**D4.** `d4a` and `no_bang_p` of 8.3. The set of the one sequent
`· ; p ⟹ p ⊗ p` is not saturated: ⊗R at the division that sends `p` to
the first premise asks for `· ; p ⟹ p` or for `· ; · ⟹ p`; the first is
an instance of init and may not be a member, so the second must be.

**D5.** `p ; · ⟹ q` has a valid hypothesis, and no member of a
saturated set has one (`Sat.unr_nil`): the premise of copy is always
asked for, and it is longer. `· ; !p, q ⟹ !(p ⊗ q)` has `!p` in its
linear zone (`Sat.no_bang`): the premise of !L has `p` valid. At the
first, `refuteSet` answers nothing at once, "the unrestricted zone is
not empty"; at the second it answers nothing, having set aside the
sequent with `!` in its linear zone. What proves that neither has a
derivation is the counting model with `p` of weight 0 and `q` of weight
1, and soundness (B5, C7).
