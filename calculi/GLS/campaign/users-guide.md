# GLS: a user's guide

For someone who wants to use the calculus in the editor. The tour, with
every step explained, is `Play/GLSTutorial.lean`; the exercises are
`Play/GLS.lean`. Each rule beside its place in the source:
[rule-table.md](rule-table.md).

    (cd ~/Lean/Sources/proof-tools/calculi/GLS && lake build)

then open one of the two files of `Play/` in the editor, with the
infoview.

## How a goal reads

A goal is shown as

    Att S   □p, □(p → q) ⇒ □q

the sequent still to be derived: the antecedent, `⇒`, the succedent, each
a list of formulas read as a multiset (the order does not matter to any
rule). Formulas: the variables `p q r s` (numbered 0 to 3; `p4`, `p5`, …
after), `⊥`, `A → B` (right associative), `□A`. **In a file you type
`⟶` for `→`**, since Lean reserves `→`; `□` and `⊥` as shown. A sequent is
typed `[□p, □(p ⟶ q)] ⇒ [□q]`.

`Att S true j` is an attempt at `j`, which may leave goals open; `Der S j`
is a derivation, with none.

## The moves

| move | the rule (source: `GLS_rules`, the Coq file l. 306) | asks | leaves |
|---|---|---|---|
| `idP n` | IdP | the variable numbered `n` on both sides | nothing |
| `botL` | BotL | `⊥` on the left | nothing |
| `impR A B` | ImpR | `A ⟶ B` on the right | `A, Γ ⇒ B, Δ'`, where `Δ'` is `Δ` less one `A ⟶ B` |
| `impL A B` | ImpL | `A ⟶ B` on the left | `Γ' ⇒ A, Δ` and `B, Γ' ⇒ Δ`, where `Γ'` is `Γ` less one `A ⟶ B` |
| `glr A` | GLR | `□A` on the right | `B₁, □B₁, …, Bₙ, □Bₙ, □A ⇒ A`, where `□B₁, …, □Bₙ` are the boxed formulas of `Γ`. Everything else is dropped |

There is no move for the identity on a formula that is not a variable,
and none for cut, weakening, contraction or exchange: GLS has no such
rules. They are theorems about it (`Fam.id`, `cutAdmissible`, and
[statements.md](statements.md)).

## The lines of the tactic

`glsmove` is `apply_move` of proof-tools, fixed to GLS.

| line | what it does |
|---|---|
| `glsmove impR p q` | makes the move at goal 0 |
| `glsmove glr p at 1` | at goal 1, counted from 0 |
| `glsmove impR`, `glsmove impL _ q`, `glsmove idP` | a pattern: made if one move of that form applies (and shown as "Try this"), offered if several do |
| `glsmove` | a query: the moves that apply at goal 0; none is made |
| `glsmove im` | a query: those whose names begin with `im` |
| `glsmove where` | draws the attempt so far, goal 0 marked `>`; no move is made |
| `apply_script ls` | makes the lines of a stored script |
| `leave_open`, `all_goals leave_open` | leaves goals open, without an error |

Put a comment on a line of its own, and not on the lines after a
pattern: the line the tactic offers back is written after them.

## The messages

| message | when |
|---|---|
| `the move does not apply to goal 0: IdP: the variable is not on both sides of the sequent` | `idP n` where it is not |
| `… BotL: ⊥ is not in the antecedent` | `botL` |
| `… ImpR: the implication is not in the succedent` | `impR A B` |
| `… ImpL: the implication is not in the antecedent` | `impL A B` |
| `… GLR: the boxed formula is not in the succedent` | `glr A` |
| `glsmove: no move applies at goal 0` | a query at a goal with no axiom, no implication at top level and no box on the right. Such a goal has no derivation: `explain` gives its countermodel |

## Beyond a move at a time (`import GLS.Explore`)

| | |
|---|---|
| `routine n` | a tactic of the calculus: the axioms and the two implication rules, at every goal they leave, at most `n` deep. What it leaves has only GLR to try. `apply_script (routine 20 j).getD []` |
| `found` | the search, as a tactic of the calculus: the script of a derivation of `j`, where there is one. `apply_script (found j).getD []` |
| `#eval IO.println (explain j)` | what the search says of `j`: derivable, with the height of the derivation found; or the countermodel, drawn as a tree, a world on each line with the variables true there. A world sees every world below it |
| `#walk d`, `#walk d down 0 down 1` | a derivation or an attempt, looked at a node at a time |
| `famOfDer d : Fam j` | the derivation `d : Der S j` as a derivation of GLS as the source states it, on which the theorems act |

`apply_script` takes its script as a closed term: the sequent is written
out again for `routine` and `found`. No tactic applies either to the goal
in front of you (a limit of the library, recorded on the closing page).

## Facts the kernel checks

    import GLS.Run
    def d : Fam ([] ⇒ [□(□p ⟶ p) ⟶ □p]) := treeCert.verdict _ (the tree of moves)
    theorem t : ¬ Derivable ([] ⇒ [□p ⟶ p]) := noDerivable.verdict _ (.node [] [])
    instance (s : Seq) : Decidable (Valid s) := validDecidable s
    example : Valid ([] ⇒ [□p ⟶ □□p]) := by decide +kernel

The first two check a certificate; the last has the kernel run the
search. `glsrun` (`lake build glsrun`) writes such facts for the corpus:
`GLS/Corpus/Facts.lean`. What each costs: `measurements.md`.
