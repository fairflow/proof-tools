# `ProofTools.Explore`: a proof explorer for any calculus

Written 2026-11-19. Core Lean only. The examples are from the tests'
calculus, `ProofToolsTest/Explore/Calculus.lean`: an intuitionistic
propositional sequent calculus of nine moves.

## In short

An instance gives three things:

```lean
structure ProofSystem where
  Judg : Type                                       -- what is derived
  Move : Type                                       -- a rule, named by its data
  step : Move → Judg → Except String (List Judg)    -- the premises, or why the move does not apply
```

and proves one theorem, that its moves are sound for its own notion `D` of
what holds:

```lean
def ProofSystem.Sound (S : ProofSystem) (D : S.Judg → Prop) : Prop :=
  ∀ m j ps, S.step m j = .ok ps → (∀ p ∈ ps, D p) → D j
```

The library then gives, the same for every instance:

| what | where |
|---|---|
| attempts and derivations as data, with soundness | `Explore/System.lean` |
| a zipper of attempts | `Explore/Zipper.lean`, on `ProofTools/Zipper.lean` |
| scripts, and `run` | `Explore/Script.lean`, `Explore/Cursor.lean`, `Explore/Run.lean` |
| the two checkers, as certifiers of `LeanCertify` | `Explore/Certify.lean` |
| tactics of the calculus, built from tactics | `Explore/Tac.lean` |
| Lean tactics: `apply_move`, `apply_script`, `leave_open` | `Explore/Tactic.lean` |
| the motions of the cursor, and their laws | `Explore/Motion.lean` |
| the view at a position; the command `#walk` | `Explore/Walk.lean` |

What it is for, and the entry point of each purpose (this table changes in
the same commit as any entry point):

| purpose | entry point |
|---|---|
| build by hand, a move at a time | `apply_move`, or the instance's alias of it |
| build by program | a script and `run`; the tactics of the calculus (`Tac`) |
| check | the term itself, each node's equation by `rfl`; a script by `derives` |
| look at an attempt that is built | `#walk`; as functions `Cursor.view`, `walkText`; all of it at once, `Att.render` |
| change an attempt that is built | a move at an open goal (`apply_move … at k`, `Att.run`); nothing else yet |
| map out to the mathematics | `Der.sound` and `Att.sound`, with the instance's soundness theorem |
| keep and replay | `Att.script`, `run`, `apply_script` |

## Attempts and derivations

```lean
inductive Att (S : ProofSystem) : Bool → S.Judg → Type
  | goal : Att S true j                                   -- an open goal
  | node (m : S.Move) (ps : List S.Judg)
      (h : S.step m j = .ok ps) (ds : Atts S o ps) : Att S o j

abbrev Der (S : ProofSystem) (j : S.Judg) := Att S false j
```

The Boolean says whether open goals are allowed. A node writes its premises
and carries the equation `S.step m j = .ok ps`, which the kernel proves by
evaluating `step`. `Atts S o ps` is a list of attempts, one at each premise.

PROVED, for every proof system:

    S.Sound D → (d : Att S o j) → (∀ g ∈ d.goals, D g) → D j        (Att.sound)
    S.Sound D → Der S j → D j                                        (Der.sound)

An attempt is a derived rule, from its open goals to its root.

## Scripts

A script is a list of lines. A line names an open goal by its number,
counted from the left over the whole attempt, and a move to make there.

```lean
def swapScript : Script IPC := [⟨0, .impR⟩, ⟨0, .andL p q⟩, ⟨0, .andR⟩, ⟨0, .ax⟩, ⟨0, .ax⟩]

#eval IO.println (run IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) (swapScript.take 3)).att.render
--  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
--   (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
--     p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
--       ? p0, p1, (p0 ∧ p1) ⊢ p1
--       ? p0, p1, (p0 ∧ p1) ⊢ p0
```

`run S j ls` answers with the attempt reached and, if a line failed, its
number and the reason; the attempt is then as it was before that line.

**How `run` works.** It keeps one zipper from the first line to the last.
A cursor is a zipper with one number, the count of open goals left of its
focus; with it a line's goal is found from where the last line left the
cursor, without going back to the root. The attempt is rebuilt once, at
the end.

**What it is proved equal to.** `Att.runBySteps` makes each line's move by
a recursion over the whole attempt from its root (`Att.moveAt`). It is the
specification, and what it does to the goals is stated outright:

    d.moveAt m k = .inl (.ok d') → ∃ g ps, d.goals[k]? = some g ∧ S.step m g = .ok ps ∧
        d'.goals = d.goals.take k ++ ps ++ d.goals.drop (k + 1)             (Att.moveAt_ok)
    d.moveAt m k = .inl (.error e) → ∃ g, d.goals[k]? = some g ∧ S.step m g = .error e
    d.moveAt m k = .inr c → c = d.goals.length ∧ c ≤ k

PROVED, for every proof system:

    d.run ls = d.runBySteps ls                                       (Att.run_eq_runBySteps)
    run S j d.script = { att := d.toAtt }        for d : Att S o j   (run_script)
    (d.runFrom n ls).failed = none →
      d.runFrom n (ls ++ ls') = (d.runFrom n ls).att.runFrom (n + ls.length) ls'
                                                                     (Att.runFrom_append)

The first: the same attempt, the same failing line, the same message. The
second: a script read back from an attempt rebuilds it. The third: a script
can be run in two parts, the second numbered after the first. (Without the
numbering the statement is false: the two sides give different numbers to a
failing line. `ProofToolsTest/Explore/Run.lean` has the case.)

**Timings** (one machine, 2026-11-19; a derivation as deep as its script is
long, `ProofToolsTest/Explore/Count.lean`):

| lines | `run`, by `#eval` | by steps, by `#eval` | `run`, in the kernel | by steps, in the kernel |
|---|---|---|---|---|
| 251 | 0.4 ms | 11 ms | | |
| 1,001 | 1.5 ms | 161 ms | | |
| 4,001 | 6.2 ms | 2.5 s | | |
| 16,001 | 24 ms | not run | | |
| 201 | | | 0.2 s | 4.6 s |
| 1,601 | | | 1.5 s | not run |
| 3,201 | | | 3.2 s | not run |

`run` is linear in the length of the script, the run by steps quadratic.

## The two checkers

```lean
def derives (S) (j : S.Judg) (ls : Script S) : Bool      -- no line fails, no goal is left
def certifier (hS : S.Sound D) : Certify.Certifier S.Judg (Script S) D

example : Valid swap := (certifier sound).verdict swap swapScript    -- the kernel runs the script
```

PROVED: `derives S j ls = true → S.Sound D → D j`, and every derivation has
a script that `derives` accepts, its own (`derives_script`).

The refutation side is optional. An instance stops where its mathematics
stops:

| level | the instance has | it gets |
|---|---|---|
| 1 | moves and their soundness | `certifier`: scripts checked |
| 2 | also a notion of model with a sound check (`Evaluator`) | `engine`, a `Certify.Engine`; its producer may answer `flag`, and nothing says a model is ever found |
| 3 | also a theorem that one side always answers | `Certify.Engine.Complete`, or the instance's own statement |

The example calculus is at level 2, on purpose. What holds is truth under
every classical valuation; the calculus is intuitionistic, so Peirce's law
holds and has no derivation, and its engine answers `flag`.

## Lean tactics

A goal is `Att S o j` or `Der S j` with `j` a closed term. The open goals of
the calculus are Lean's goals.

```lean
def swap : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move impR
  apply_move andL p q
  apply_move andR
  apply_move ax
  apply_move ax

theorem swap_valid : Valid ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := Der.sound sound swap
```

* `apply_move m` makes the move at the first goal, `apply_move m at k` at
  goal `k`. The calculus is read off the goal's type.
* A move's name may be written bare, with a dot, or in full.
* **Patterns.** `apply_move andL` (arguments left out) or
  `apply_move andL _ q` (holes) is matched against the moves the instance
  proposes at the goal. One match is made, and shown as "Try this"; several
  are offered; none is an error. The line shown keeps each argument as it
  was typed, and fills the holes and the arguments left out.
* **Queries.** `apply_move` alone offers the moves that apply;
  `apply_move an` those whose names begin with `an`. A query makes no move.
* A move one of whose premises adds nothing to its conclusion is set aside
  while another matches.
* `apply_script ls` makes the lines of a stored script; `leave_open` leaves
  the first goal open.
* `declare_move_tactic ipc for IPC` declares `ipc` as `apply_move` fixed to
  the calculus `IPC`.

The lines of a proof by `apply_move` are the lines of a script:
`swap.script` gives them back.

## Looking at an attempt that is built

An attempt or a derivation is a value, whatever made it: a proof by
`apply_move`, `(run S j ls).att`, `Der.ofScript j ls h`, a search.  `#walk`
names one and makes motions from its root; it shows the **view** at the
position reached, and changes nothing.

```lean
#walk swap down 0 down 0
```

```
   ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
>     p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        0: p0, p1, (p0 ∧ p1) ⊢ p1   by ax   [closed]
        1: p0, p1, (p0 ∧ p1) ⊢ p0   by ax   [closed]
  at 0.0: 2 premises; no open goals
```

The view is: the nodes from the root down to the focus, each with its move;
the focus, marked `>`; the premises of the focus, numbered, an open one
marked `?` and a node with its move and whether it is closed; then the
address of the focus (the premise numbers from the root) and where the open
goals are.

| motion | goes to |
|---|---|
| `up` | the node the focus is a premise of |
| `down i` | premise number `i` of the focus, numbered from 0 |
| `left`, `right` | the premise before, or after, of the same node |
| `top` | the root |
| `goal k` | open goal `k` of the whole attempt, numbered from 0 |

Written over several lines, a walk shows the view after each line as a
message at that line, so the infoview follows the editor's cursor:

```lean
#walk swap
  down 0
  down 0
  down 1
  up
```

A motion that cannot be made is an error at that motion, with the reason
(`the focus is the root`, `the focus has no premise 3: its premises are
numbered 0 to 0`, `there is no goal 4`, …); the view before it is shown.
A comma may follow a motion.

The motions are functions of the library (`Explore/Motion.lean`):
`Cursor.move m c`, and `Cursor.moves c ms` for several.  A motion changes
the position and nothing else (PROVED; `c.Ok` says that the cursor's count
of the open goals left of the focus is right):

    c.Ok → c.move m = some c'   →  c'.toRoot = c.toRoot ∧ c'.Ok      (Cursor.move_some)
    c.Ok → c.moves ms = .ok c'  →  c'.toRoot = c.toRoot ∧ c'.Ok      (Cursor.moves_ok)
    c.down i = some c'  →  c'.up = some c                            (Cursor.up_down)

`walkText d ms` is the view after the motions `ms` as a string, for use
without the command.

## Tactics of the calculus, from tactics

```lean
abbrev Tac (S : ProofSystem) := S.Judg → Option (Script S)

Tac.move m          -- the one move, where it applies
Tac.orElse t u      -- t, or u where t gives nothing
Tac.andThen t u     -- t, then u at every goal t leaves
Tac.iterate n t     -- t at every goal it leaves, at most n deep
Script.shift k ls   -- the same script at goal k of a larger attempt
```

A tactic is a total function in the logic. PROVED:

    (d.runFrom n' ls).failed = none →
      (p.plug d).runFrom n (ls.shift (goalsL p).length ++ rest) =
        (p.plug (d.runFrom n' ls).att).runFrom (n + ls.length) rest      (Att.runFrom_shift)

    (Tac.move m).Valid        (t.andThen u).Valid        (Tac.iterate n t).Valid
    t.Valid → u.Valid → (t.orElse u).Valid

where `t.Valid` says that every script `t` gives runs without a failing
line, and `p` is a path with `d` at its hole. So a tactic built from moves
with these combinators never gives a script that fails. Whether the script
closes its goal is for `derives` to say: a wrong tactic costs a failure,
never a wrong derivation.

## What is trusted

* Lean's kernel.
* For a script: `derives`, `Att.sound` and the instance's `Sound` theorem.
* For a model: the instance's `Evaluator.sound`.

Not trusted: everything in `Explorable`, the tactics, `candidates`, any
producer, and `run` being fast. The tactic evaluates compiled code to find
the premises and quotes them with the instance's `ToExpr`; the node it
builds is checked by the kernel. `ProofToolsTest/Explore/Tactic.lean` has an
instance that quotes wrongly, and the kernel's refusal.

Each theory file ends with its bound on axioms (`#axioms_within_file`), and
every bound is `[propext, Quot.sound]`: nothing in the library uses
`Classical.choice`. One thing to know when proving about numbers of goals:
`omega` stays within that bound when it is given one comparison to prove,
and brings in `Classical.choice` when it is given a conjunction (it negates
the goal, and pushes the negation through `∧` with
`Classical.propDecidable`). Split the goal first.

## Declaring an instance

1. `Judg`, `Move` (one constructor for each rule, with its data) and `step`.
2. The system as an `abbrev`, so that `S.Judg` unfolds to the instance's own
   type where Lean looks for instances and notations.
3. `S.Sound D`, for the instance's `D`.
4. For the tactics, `Explorable S`: `candidates`, `quoteJudg` and `quoteMove`
   (`deriving Lean.ToExpr` gives them), `showJudg`, `showMove`, and
   optionally `within` and `moveSource` (a move as Lean source, for the
   lines the tactic suggests; without it Lean prints the move's term).
5. Optionally an `Evaluator`, a producer, and an alias.

`step` should reduce in the kernel: structural recursion, and `Decidable`
instances that compute. `docs/deciders.md` says what to avoid.

Two things that instances have found useful:

* Write `step` through one function that gives, for a move at a judgment,
  whether it applies, its premises, and what to say if it does not. The
  lemmas about `step` are then one case analysis each.
* A function or theorem by recursion on an attempt is written for every
  `o`, with `o = false` as a hypothesis where it is about derivations:
  Lean's structural recursion needs the indices of `Att S o j` to be
  variables.

A worked instance on a calculus with a decision procedure, a certified
countermodel side and a translation to natural deduction: the subframe
tableau for propositional lax logic, in
[lax-logic-in-lean](https://github.com/fairflow/lax-logic-in-lean)
(`LaxLogic/PLL/SubTab/Explore.lean`). There a derivation and a closed
tableau of the existing checker are each computed from the other, so every
proof its search finds is also a script.

**Judgments that hold functions.** The tactic writes each premise as a
term, quoted from its value, and proves the node's equation
`S.step m j = .ok ps` by `rfl`. That asks the quoted premises to be, by
definition, what `step` computes. A function quoted is seldom the function
computed (`fun b => cond b 2 1` against `fun b => (fun b => cond b 1 2) (!b)`),
so an instance whose judgments hold functions sets `eqByDecide := true` and
gives `DecidableEq S.Judg`: the equation is then proved by
`step_of_stepIs (Eq.refl true)`, the kernel evaluating `step` and deciding
that its premises are the ones written. `run`, `derives` and the certifier
do not quote, and need neither.

## Limits

1. When the cursor passes a premise off its path, it reads that premise to
   see whether the goal is in it; nothing records that a premise is closed.
   In the usual order (leftmost goal first) this costs nothing.
2. Going left, the open goals of a premise are counted before it is
   entered: two passes over that premise.
3. `Att.script` counts the goals of each premise as it passes: quadratic on
   a derivation as deep as it is long.
4. The tactics need the goal's judgment to be a closed term, and see only
   the candidates the instance proposes when a line is a pattern.
5. There is no search procedure, no model of an open goal, and no map
   between systems: those belong to the instance.
6. `#walk` needs the attempt to be a closed term, and evaluates compiled
   code, as the tactics do.  The view draws the premises of the focus, not
   those of the nodes above it: `up` shows them.  Going `up`, the open
   goals of the premises before the focus are counted again.
