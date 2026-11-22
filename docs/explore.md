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

and shows one thing, that its moves are sound for its own notion of what
holds. That notion is a family `T` over the judgments, into any sort: a
proposition (validity, or that a derivation exists), or a type, the
derivations of the calculus as its source states it.

```lean
def ProofSystem.SoundT (S : ProofSystem) (T : S.Judg → Sort u) :=
  ∀ m j ps, S.step m j = .ok ps → Each T ps → T j     -- one `T p` for each premise, by position

def ProofSystem.Sound (S : ProofSystem) (D : S.Judg → Prop) : Prop :=
  ∀ m j ps, S.step m j = .ok ps → (∀ p ∈ ps, D p) → D j     -- for a proposition: by membership
```

For a proposition the two are one notion (`soundT_iff_sound`), and an
instance proves whichever is easier to state. For a type, `S.SoundT T` is a
definition: each move that applies is a rule of the calculus, applied to
the derivations of its premises.

The library then gives, the same for every instance:

| what | where |
|---|---|
| attempts and derivations as data, with soundness | `Explore/System.lean` |
| a zipper of attempts | `Explore/Zipper.lean`, on `ProofTools/Zipper.lean` |
| scripts, and `run` | `Explore/Script.lean`, `Explore/Cursor.lean`, `Explore/Run.lean` |
| trees of moves as certificates, and their check | `Explore/Cert.lean`, on the rose trees of `ProofTools/Zipper/Rose.lean` |
| the checkers of scripts and of trees, as certifiers of `LeanCertify` | `Explore/Certify.lean` |
| tactics of the calculus, built from tactics | `Explore/Tac.lean` |
| the motions of the cursor, which are the moves of the zipper; their laws; the one loop of the cursor | `Explore/Motion.lean` |
| changing an attempt that is built: one change at the focus and its uses; a session of commands | `Explore/Cursor.lean`, `Explore/Session.lean` |
| what an instance supplies for the editor (`Explorable`); an attempt drawn as text: all of it, the view at a position, the view with every branch | `Explore/View.lean` |
| Lean tactics: `apply_move`, `apply_script`, `leave_open`; the query `apply_move where`; a goal shown as its judgment | `Explore/Tactic.lean` |
| the command `#walk`; the goal `Walk d`, for a tactic block of motions | `Explore/Walk.lean` |
| the panel of `#walk` (a trial): the attempt as a tree in the infoview | `Explore/Panel.lean`, `Explore/walkPanel.js` |

What it is for, and the entry point of each purpose (this table changes in
the same commit as any entry point):

| purpose | entry point |
|---|---|
| build by hand, a move at a time | `apply_move`, or the instance's alias of it; `apply_move where` draws the attempt so far, with the goal marked |
| build by program | a script and `run`; the tactics of the calculus (`Tac`); a tree of moves and `Der.ofCert` |
| check | the term itself, each node's equation by `rfl`; a script by `derives`; a tree of moves by `Cert.check` |
| look at an attempt that is built | `#walk`, by typing motions or by clicking the ones it offers; `example : Walk d := by …`, a tactic block of motions whose goal is the view; as functions `Cursor.view`, `Cursor.viewAll`, `walkText`, `Cursor.motions`; all of it at once, `Att.render` |
| change an attempt that is built | a move at an open goal (`apply_move … at k`, `Att.run`); at a position, as functions: `Cursor.replace` and its uses `Cursor.rule`, `Cursor.prune`, `Cursor.graft`, `Cursor.script`; in turn with motions, `Cursor.walk` on a list of commands (`Cmd`). No tactic or command of the editor changes one yet |
| map out to the mathematics | `Der.mapOut` and `Att.mapOut`, with the instance's soundness: into a type, a derivation of the calculus as data; into a proposition, a proof (there also as `Der.sound`, `Att.sound`) |
| keep and replay | `Att.script`, `run`, `apply_script`; `Att.cert`, the tree of moves, which is printed and compared as it stands |

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

## The map out

`Each T ps` is one `T p` for each judgment `p` of the list `ps`, by
position: `Each T [a, b]` is `T a ×' T b ×' PUnit`. For every proof system,
and every `T` into any sort:

    S.SoundT T → (d : Att S o j) → Each T d.goals → T j             (Att.mapOut)
    S.SoundT T → Der S j → T j                                       (Der.mapOut)

An attempt is a derived rule, from its open goals to its root. With `T` a
type these are functions: `Der.mapOut` carries a derivation of the explorer
to a derivation of the calculus, and `Att.mapOut` an attempt to a function
from derivations of its open goals to a derivation of its root. In the
tests the example calculus is stated a second time, as an inductive family
`G3 : Seq → Type` with a constructor for each rule, and

```lean
def soundT : IPC.SoundT G3            -- each move that applies is a rule, applied

example : Der.mapOut soundT swap = swapG3 := rfl       -- the kernel evaluates the map out
```

(`ProofToolsTest/Explore/MapOut.lean`). On a derivation the map out
computes by the rule of each move (`Der.mapOutAll` is `Der.mapOut` at each
premise):

    Der.mapOut hS (.node m ps h ds) = hS m j ps h (Der.mapOutAll hS ds)    (Der.mapOut_node)
    Der.mapOutAll hS (.cons d ds) = ⟨Der.mapOut hS d, Der.mapOutAll hS ds⟩  (Der.mapOutAll_cons)

For a proposition, the same with the premises and the goals taken by
membership. PROVED:

    S.SoundT D ↔ S.Sound D                                           (soundT_iff_sound)
    S.Sound D → (d : Att S o j) → (∀ g ∈ d.goals, D g) → D j        (Att.sound)
    S.Sound D → Der S j → D j                                        (Der.sound)
    S.SoundT T → S.Sound (fun j => Nonempty (T j))                   (SoundT.nonempty)

`Att.sound` and `Der.sound` are `Att.mapOut` and `Der.mapOut` at a
proposition: the recursion over an attempt is written once.

**Why there are two statements of soundness, and not one.** `Sound`, with
`Sort u` in place of `Prop`, is still a definition; but it has no map out.
Its premises are given by membership (`∀ p ∈ ps, T p`), and a node of an
attempt holds its premises' attempts by position. To go from the second to
the first is to say, for a proof of `p ∈ ps`, which position is meant, and
a proof of a proposition cannot be taken apart into data (Lean: "recursor
`Or.casesOn` can only eliminate into `Prop`"). With decidable equality of
judgments it can be written, and then two premises with one judgment get
the derivation of the first: the map out of a node with premises `[p, p]`
and derivations `d₁`, `d₂` would hold `d₁` twice. So for data the premises
are by position; for a proposition nothing is lost either way, and `Sound`
keeps the statement its instances prove.

**In the kernel.** A soundness definition carries what it is given, for the
premises a node writes, to the premises `step` computes, by a cast along
the node's equation, and the kernel reduces such a cast when the two lists
are equal by definition. So the kernel evaluates `Der.mapOut hS d` on a
derivation whose nodes hold their equation by `rfl`, and on any derivation
that `run` built, which writes the premises as `step` computes them. It
does not on a derivation the tactic built for an instance that sets
`eqByDecide` (below); `Der.ofScript j d.script (derives_script d)` is that
derivation rebuilt by `run`, and there it does. Compiled code runs either
way. The tests have both cases (`swByRun`, `swByTactic`).

**The map out is natural in the family.** For two families `T`, `T'` with
their soundness `hS`, `hS'`, and `f : ∀ j, T j → T' j`. PROVED:

    (∀ m j ps h e, f j (hS m j ps h e) = hS' m j ps h (e.map f)) →
      f j (Att.mapOut hS d g) = Att.mapOut hS' d (g.map f)           (Att.mapOut_map)
      f j (Der.mapOut hS d) = Der.mapOut hS' d                       (Der.mapOut_map)

(`e.map f` is `f` at each position.) A function between two families that
agrees with their rules at each move agrees with their maps out on every
attempt. So what an instance says of one move, it has of every derivation,
with no recursion over attempts of its own: that two ways from a derivation
to the mathematics give the same thing, or that what one way gives has a
property (take `T` to be the family of the things that have it, and `f`
the projection). The trees of moves below are made this way.

**Not asked, not given: the converse.** That every derivation of the
calculus is a derivation of the explorer (`T j → Der S j`) is no field and
no theorem here. A `step` that refuses a move the rule allows passes
`SoundT` and is not the calculus.

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

## Trees of moves

A derivation writes, at each node, the move, the premises and the equation.
Its **tree of moves** keeps the moves and the shape, and nothing else:

```lean
abbrev Cert (S : ProofSystem) : Type := Zip.RTree Unit S.Move    -- a rose tree: moves at the nodes, nothing on the edges

def Cert.check : S.Judg → Cert S → Bool          -- `step` at the root, then each child at its premise
def Der.ofCert (j : S.Judg) (c : Cert S) (h : c.check j = true) : Der S j
def Att.cert   : Der S j → Cert S

def swapCert : Cert IPC := .mk .impR [.mk (.andL p q) [.mk .andR [.mk .ax [], .mk .ax []]]]

example : Cert.check ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) swapCert = true := by decide +kernel
example : swap.cert = swapCert := rfl             -- the kernel evaluates `Att.cert`
```

(`swap` there is the derivation built by `apply_move`, under "Lean tactics"
below; the tests are `ProofToolsTest/Explore/Cert.lean`.)

PROVED, for every proof system:

    d.cert.check j = true                      for d : Der S j       (Att.check_cert)
    (Der.ofCert j c h).cert = c                                      (Att.cert_ofCert)
    Der.ofCert j d.cert h = d                                        (Der.ofCert_cert)
    d.cert = d'.cert → d = d'                  for d d' : Der S j    (Att.cert_inj)

So the derivations of `j` and the trees of moves that check at `j` are the
same things, each computed from the other.

* **It is a rose tree of the library**, not a type of its own. Trees of
  moves are compared by `==` (`RTree.beq`, proved lawful), printed by
  `Repr`, drawn by `RTree.drawWith`, and walked by Huet's zipper, with
  nothing written for them. A node is `((), c)` for each child `c`;
  `Cert.mk m cs` takes a list of trees. (The drawing prints an arrow for
  every edge, also for these, which have nothing on them.)
* **`Att.cert` is a map out**, `Der.mapOut Cert.moves`, at the constant
  family `fun _ => Cert S`: a move over the trees of its premises is a
  node. That the tree checks is the map out at the family of the trees
  that check (`Cert.checked`), by naturality. No recursion over attempts
  is written for either.
* **An attempt with open goals has no tree of its own**, and `Cert` no leaf
  for an open goal. It is `Att.mapOut Cert.moves d`: from one tree for each
  open goal, by position, the tree of the whole.
* `Cert.moves` makes no use of a node's equation, so the kernel evaluates
  `d.cert` on every derivation, also for an instance that sets `eqByDecide`
  (below).

## The checkers

A derivation has two writings as a certificate. Each has its checker, and
with the soundness of the moves each is a certifier of `LeanCertify`:

```lean
def derives (S) (j : S.Judg) (ls : Script S) : Bool      -- no line fails, no goal is left
def certifier (hS : S.SoundT T) : Certify.Certifier S.Judg (Script S) T
def Cert.certifier (hS : S.SoundT T) : Certify.Certifier S.Judg (Cert S) T

example : Valid swap := (certifier sound.soundT).verdict swap swapScript   -- the kernel runs the script
def swapByScript : G3 swap := (certifier soundT).verdict swap swapScript   -- and here builds the derivation
example : Valid swap := (Cert.certifier sound.soundT).verdict swap swapCert   -- the kernel checks the tree
def swapByTree : G3 swap := (Cert.certifier soundT).verdict swap swapCert
```

`T` is into any sort, as the property of a `Certify.Certifier` is. With a
proposition a certifier proves it (from `sound : S.Sound D`, by
membership: `certifier sound.soundT`). With a type of derivations its
`sound` is a function, `Der.mapOut hS (Der.ofScript j ls h)` or
`Der.mapOut hS (Der.ofCert j c h)`: the certificate is one for the
derivation itself.

PROVED: `derives S j ls = true → S.Sound D → D j` (`derives_sound`); every
derivation has a script that `derives` accepts, its own (`derives_script`),
and a tree that `Cert.check` accepts, its own (`Att.check_cert`).

**Which to use.** The script keeps the order of the work: it can be
continued, composed (`Tac`), and replayed line by line in the editor. The
tree keeps the shape: a producer that has a tree hands over a tree, and its
check builds nothing. In the kernel (one machine, 2026-11-22;
`ProofToolsTest/Explore/CertScale.lean`, where the command is):

| derivation | moves | the tree, `Cert.check` | the script, `derives` | script / tree |
|---|---|---|---|---|
| `swap` | 5 | 1.4 ms | 4.9 ms | 3.4 |
| `distr` | 11 | 2.3 ms | 10.0 ms | 4.3 |
| `chain 300` | 301 | 44 ms | 264 ms | 6.1 |
| `chain 1000` | 1,001 | 157 ms | 970 ms | 6.2 |
| `conj 4` | 31 | 10 ms | 37 ms | 3.5 |
| `conj 6` | 127 | 140 ms | 269 ms | 1.9 |
| `conj 7` | 255 | 591 ms | 917 ms | 1.6 |

`chain` is a derivation as deep as it is long, whose steps cost next to
nothing; `conj k` a balanced one with `2 ^ k` hypotheses to search at each
leaf. The tree's gain is the checker's own work, so it is largest where a
step costs least and falls towards 1 as the steps dominate (`conj 8`: 1.3).
Being a rose tree costs the tree's check something: a tree type with no
edges, tried beside it, checked `chain 1000` in 96 ms and `conj 6` in
137 ms.

The refutation side is optional. An instance stops where its mathematics
stops:

| level | the instance has | it gets |
|---|---|---|
| 1 | moves and their soundness | `certifier`, `Cert.certifier`: scripts and trees checked |
| 2 | also a certifier against what holds: a notion of model with a sound check | `engine`, a `Certify.Engine`; its producer may answer `flag`, and nothing says a model is ever found |
| 3 | also a theorem that one side always answers | `Certify.Engine.Complete`, or the instance's own statement |

A certifier against what holds is `LeanCertify`'s, as it stands:
`Certify.Certifier S.Judg Model (fun j => D j → False)`. Bundled with its
type of models, a name and a producer, it is a `Certify.Disprover`. The
explorer has no structure of its own for it (until 2026-11-22 it had one,
`Evaluator`, which held the same things as a `Disprover` does):

```lean
def engine (hS : S.Sound D) (no : Certify.Certifier S.Judg Model (fun j => D j → False))
    (produce : S.Judg → Nat → Certify.Verdict (Script S) Model) :
    Certify.Engine S.Judg (Script S) Model D
```

The example calculus is at level 2, on purpose. What holds is truth under
every classical valuation; the calculus is intuitionistic, so Peirce's law
holds and has no derivation, and its engine answers `flag`. Its no side is
a `Certify.Disprover` (`refuter`), whose certifier the engine takes.

## Lean tactics

A goal is `Att S o j` or `Der S j` with `j` a closed term. The open goals of
the calculus are Lean's goals. A goal is shown as its judgment, drawn by the
instance's `showJudg`: `Att IPC   p0, p1 ⊢ p0`, or `Der IPC   …` where no
goal may be left open; a judgment drawn on several lines goes below the
head. One delaborator in the library does this for every instance.

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

**Where the proof is: `apply_move where`.** The goals show what is left to
do, and not what was done. The query `apply_move where` draws the attempt so
far, all of it, with the first goal marked `>`; `apply_move where at k`
marks goal `k`. It makes no move. After the third line of `swap`:

```
   ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
      p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
>       ? p0, p1, (p0 ∧ p1) ⊢ p1
        ? p0, p1, (p0 ∧ p1) ⊢ p0
  at 0.0.0: open goal 0; 2 open in all
```

The lines are those of `Att.render` on the attempt, an open goal marked `?`;
the last line is the last line of a view (below): the address of the goal,
its number among the open goals of the attempt, and how many there are.
The message is at the line of the query, so the infoview shows it while the
editor's cursor is there. An alias has the query too (`ipc where`).

`set_option apply_move.showWhere true` asks it after every move: each line
that makes a move then shows where the proof is after it, the goal the next
line acts on marked, and the line that closes the last goal shows the
derivation. It is off by default: a script then shows a message at every
line, and the attempt is read again at each (below).

**How the attempt is found.** The tactic keeps no state: the attempt so far
is the value, assigned in part, of the metavariable the proof began with,
and Lean does not hand a tactic that metavariable. It is found again from
the goal: among the metavariables that are assigned and whose value, with
every later assignment put in, still mentions the goal, those of type
`Att S o j` are the attempts the goal is part of, and the one made first
holds the others. Its value is read as a closed term (each open goal
becomes `Att.goal`; a part given with `exact` is taken as it is) and drawn
by evaluating `Att.whereText`, which is `Cursor.viewAll` at that goal. So:

* it is found under bullets, `case`, `all_goals`, `<;>`, and when the goals
  are in another order (`rotate_left`): the goal marked is the tactic's
  goal, wherever it is in the attempt;
* a block inside a term (`exact .node m _ rfl (.cons (by …) .nil)`) is an
  attempt of its own while it runs, since the term around it is not yet
  the value of anything;
* inside a `have d : Der S j := by …` the attempt drawn is `d`'s, and the
  message says that there is more around it; after the `have` the goal is
  drawn alone, since the proof is then under a binder;
* with no goal left there is nothing to start from, and the query says so.
  With the option on, the attempt is found before each move is made, so
  the last line can draw the derivation;
* each query has the kernel check the term so far again (the term is
  evaluated as compiled code, and Lean checks what it compiles): about as
  long as the check of the finished proof, at each query.

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

**As a tactic block.**  The same walk, with the view as the goal:

```lean
example : Walk swap := by
  down 0
  down 0
  down 1
  up
```

`Walk d` is the goal of a block whose lines are motions.  The goal after
each line is `Walk d` at the position reached, and it is shown as the view
there, so the infoview's goal follows the editor's cursor and no message is
written.  A motion that cannot be made is an error at its line, with the
same reason.  The block needs no last line: the goal that is left is closed
by Lean when the block ends.  `Walk d` says nothing about `d`; it is there
to be looked at.

The motions `up`, `down i`, `top`, `goal k` are tactics for this goal only
(on another goal: `a motion is for a goal Walk d`), and of low priority, so
that a tactic of another library with the same form is read first.  `left`
and `right` are Lean's own tactics: on a goal `Walk d` they are the
motions, on any other goal they are Lean's, with Lean's errors.  The words
are not reserved: `def top`, an argument named `left`, are as before.  The
block does not offer motions to click; `#walk` does.

**Walking by clicking.**  After the last view, `#walk` offers the motions
that can be made from the position reached, as a second message:

```
Motions from here:
  [apply] down 0
  [apply] down 1
  [apply] up
  [apply] top
```

A click on `[apply]` writes that motion after the last one, on the same
line; the same edits are in the editor's menu of code actions (`#walk:
down 0`, …).  The editor's cursor stays on that line, so the infoview shows
the next view and the next offer: an attempt is walked by clicking from
`#walk d` alone.  The walk stays in the file as text; break the line where
a view in between is wanted.  Offered, in this order: `down i` for each
premise of the focus; `up`, `left`, `right`; `top`, unless the focus is
the root; `goal k` for each open goal, unless the focus is that goal; at
most 40.  A walk that fails offers nothing.  `set_option walk.offer false`
turns the offer off (in a file of walks kept as a record, for example).

**The panel (a trial, 2026-11-21).**  With `set_option walk.panel true`,
`#walk` also draws the attempt as a tree in the infoview, while the
editor's cursor is on the command:

```
Walk: at 0.0
[down 0] [down 1] [up] [top] [goal 0]
▾  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
  ▾ (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
    ▾ p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        0: ? p0, p1, (p0 ∧ p1) ⊢ p1
        1: p0, p1, (p0 ∧ p1) ⊢ p0   by ax   [closed]
at 0.0: 2 premises; open goals: 1 under the focus, 0 left of it, 1 in all.  write into the file
```

The whole attempt is there.  A node's premises are drawn if it is on the
way to the focus or is the focus; `▸` and `▾` show and hide the premises
of any node, and a hidden part says `[closed]` or `[n open]`.

At a focus the panel says what the view says there: the buttons are the
motions that can be made, the same and in the same order as those offered
under Messages; the rows from the root to the focus, and the premises of
the focus with their numbers, read as the lines of the view; the last line
is the view's.  A click on a button, or on a node, puts the focus there.
The panel keeps the focus: nothing is written to the file until `write
into the file` is clicked, which replaces the motions of the `#walk` by
the path to the focus (`down i …`).  When the motions in the file change,
the panel follows them.

It is off by default, and a trial: the script that draws it
(`Explore/walkPanel.js`, about 220 lines of JavaScript on the infoview's
React) is the only code of the library that is not Lean.  What Lean gives
it is tested here (`walkPanelData`); the script is not run by the tests.
That its buttons, rows and last line are those of the view was compared
once, outside the tests, at every address of eight attempts (2026-11-22);
nothing in the repository repeats that comparison.

The motions are functions of the library (`Explore/Motion.lean`):
`Cursor.move m c`, and `Cursor.moves c ms` for several.  One loop makes
motions in turn, `Cursor.trail`, which keeps every position passed, the
last one reached and the motion that could not be made; `Cursor.moves`, the
views of `#walk` and the panel's focus are read off it.  (It is
`Cursor.trailBy`, the loop over any kind of step, at motions; a session,
below, is the same loop at commands.)

**The motions are the moves of the zipper** (`ProofTools/Zipper.lean`), with
the cursor's count of goals kept beside them.  `up` and `down i` are its
`up` and `down`; `left` and `right` are its one step to a sibling
(`Deriv.Sibling`: the hole of the node moved one premise, where going up
and down again fills the node and opens it from its first premise); `top`
is its `ofRoot` of `toRoot`.  The count changes by the open goals of the
premises before the focus in its node, read off the zipper's nearest crumb
(`Zipper.crumb`).  So the laws are the zipper's.  A motion changes the
position and nothing else (PROVED; `c.Ok` says that the cursor's count of
the open goals left of the focus is right):

    c.Ok → c.move m = some c'   →  c'.toRoot = c.toRoot ∧ c'.Ok      (Cursor.move_some)
    c.Ok → c.moves ms = .ok c'  →  c'.toRoot = c.toRoot ∧ c'.Ok      (Cursor.moves_ok)
    c.down i = some c'  →  c'.up = some c                            (Cursor.up_down)
    c.move .right = match c.pos.ds with
      | [] => none | d :: _ => c.up.bind (·.down (d + 1))            (Cursor.move_right)
    c.move .left = match c.pos.ds with
      | [] => none | 0 :: _ => none | (d + 1) :: _ => c.up.bind (·.down d)   (Cursor.move_left)

The last two say that the one step reaches what up, then down at the
neighbouring premise number, reaches, with the same count.

`Cursor.motions c` is the list of motions offered, and each can be made
(PROVED):

    m ∈ c.motions  →  ∃ c', c.move m = some c'                       (Cursor.motions_move)

`walkText d ms` is the view after the motions `ms` as a string, and
`walkOffers d ms` the motions offered after them, for use without the
command.

**The drawings** (`Explore/View.lean`) are three, from the same pieces:
`Att.render d`, all of an attempt; `Cursor.view c`, the view above;
`Cursor.viewAll c`, the lines of `Att.render` with the focus marked `>` and
the last line of the view, which is what `apply_move where` shows.  A node,
made or open, is drawn by one function (`nodeLines`), and what is around a
focus by one (`Path.linesAround`, which goes up the zipper's path crumb by
crumb, with the other branches or without them).

## Changing an attempt that is built

An attempt is changed at a position.  The cursor goes there by motions,
and the attempt at its focus is replaced: there is one change,
`Cursor.replace` (the zipper's `replace`), and the others are uses of it.

| | the focus | becomes |
|---|---|---|
| `c.replace d` | anything | the attempt `d`, at the same judgment |
| `c.rule m` | an open goal | the node of the move `m`, its premises open |
| `c.prune` | anything | an open goal |
| `c.graft d` | an open goal | the attempt `d` |
| `c.script ls` | anything | what the script `ls` leaves of it, the goals of `ls` numbered within the focus; nothing changes if a line fails |

The position stays, and the cursor's count with it, since the goals left of
the focus are not touched.  What a change does to the whole attempt is
PROVED (`goalsL`, `goalsR`: the open goals left and right of the focus):

    (c.replace d).toRoot.goals = goalsL ++ d.goals ++ goalsR               (Cursor.goals_replace)
    c.prune.toRoot.goals = goalsL ++ c.pos.i :: goalsR                     (Cursor.goals_prune)
    c.rule m = .ok c' → ∃ ps, S.step m c.pos.i = .ok ps ∧
        c'.toRoot.goals = goalsL ++ ps ++ goalsR                           (Cursor.goals_rule)
    c.rule m = .ok c' → c'.prune = c                                       (Cursor.prune_rule)
    c.Ok → c.rule m = .ok c' → c.toRoot.step ⟨c.left, m⟩ = .ok c'.toRoot   (Cursor.toRoot_rule)
    c.Ok → c.script ls = .ok c' →
        c.toRoot.run (ls.shift c.left) = { att := c'.toRoot }              (Cursor.toRoot_script)

The last two say what a change at the focus is at the root: a rule is the
line of a script at goal number `c.left`, and a script at the focus is the
script shifted by `c.left`.  A line of `run` is the motion to its goal and
then the rule there (`Cursor.step_eq`).  Soundness asks nothing new: every
state is an attempt, `c.toRoot`, to which `Att.mapOut` and `Att.sound`
apply.

**A session** is commands in turn: the motions, as they are, and the
changes.

```lean
inductive Cmd (S : ProofSystem)
  | motion (m : Motion) | rule (m : S.Move) | prune | script (ls : Script S)

def Cursor.walk : Cursor S j → List (Cmd S) → Except (Nat × String) (Cursor S j)
```

`Cursor.walk` answers with the cursor reached, or the number of the first
command that fails and why.  A graft enters a session as `script`, since a
command cannot hold an attempt whose type depends on the focus.  From the
tests (`ProofToolsTest/Explore/Session.lean`): a derivation built where the
cursor is, and a branch taken the wrong way, pruned and built again.

```lean
def build : List (Cmd IPC) :=
  [.rule .impR, .motion (.down 0), .rule (.andL p q), .motion (.down 0), .rule .andR,
   .motion (.down 0), .rule .ax, .motion .right, .rule .ax]

#guard ((start swap).walk build).toOption.map (·.toRoot.script) == some swapScript

-- after `orL`, the wrong disjunct in the first branch; then back up, prune, the right one
def wrong : List (Cmd IPC) := [… .rule (.orL q r), .motion (.down 0), .rule .orR2, .motion (.down 0), .rule .andR]
def again : List (Cmd IPC) := [.motion .up, .prune, .rule .orR1, …]
```

PROVED of sessions:

    c.Ok → c.walk cs = .ok c' → c'.Ok                                      (Cursor.walk_ok)
    c.walk (ms.map .motion) = c.moves ms                                   (Cursor.walk_motions)
    c.Ok → c.walk (ms.map .motion) = .ok c' → c'.toRoot = c.toRoot ∧ c'.Ok (Cursor.walk_motions_ok)
    (d.run ls).failed = none →
        ∃ c, (Cursor.ofRoot d).walk (Script.cmds ls) = .ok c ∧ c.toRoot = (d.run ls).att   (Att.walk_cmds)
    (Cursor.ofRoot d).walk (Script.cmds ls) = .ok c → d.run ls = { att := c.toRoot }       (Att.run_of_walk_cmds)

The first: the count stays right through a session, so `goal k` finds open
goal `k` after any change.  The next two: a session of motions only is the
motions in turn, and leaves the attempt as it was.  The last two: a script
is the session that goes to each line's goal and makes its move there
(`Script.cmds ls`), and succeeds exactly when no line of the run fails.

A session is not a certificate.  It records what was done, with its
retreats; the certificate is read off the result (`c.toRoot.script`; or,
once no goal is open, the tree of moves of the derivation
`c.toRoot.toDer h`), and the kernel checks that.  There
is no tactic or command of the editor for a session yet: `Cursor.walk` is a
function.

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
* For a script: `derives`, `Att.mapOut` (of which `Att.sound` is the case of
  a proposition) and the instance's soundness, `SoundT` or `Sound`.
* For a tree of moves: `Cert.check`, `Der.ofCert`, `Att.mapOut` and the
  instance's soundness.
* For a model: the `sound` of the instance's certifier against what holds.

Not trusted: everything in `Explorable`, the tactics, `candidates`, any
producer, and `run` being fast. The tactic evaluates compiled code to find
the premises and quotes them with the instance's `ToExpr`; the node it
builds is checked by the kernel. `ProofToolsTest/Explore/Tactic.lean` has an
instance that quotes wrongly, and the kernel's refusal.

Each theory file ends with its bound on axioms (`#axioms_within_file`), and
every bound is `[propext, Quot.sound]`: nothing that is proved, and nothing
on the path of trust, uses `Classical.choice`. The code for the editor
(`View.lean`, `Tactic.lean`, `Walk.lean`, `Panel.lean`) carries no bound:
it proves nothing, and its drawings use Lean's own functions on strings,
which do use `Classical.choice`. One thing to know when proving about numbers of goals:
`omega` stays within that bound when it is given one comparison to prove,
and brings in `Classical.choice` when it is given a conjunction (it negates
the goal, and pushes the negation through `∧` with
`Classical.propDecidable`). Split the goal first.

## Declaring an instance

1. `Judg`, `Move` (one constructor for each rule, with its data) and `step`.
2. The system as an `abbrev`, so that `S.Judg` unfolds to the instance's own
   type where Lean looks for instances and notations.
3. Soundness of the moves. Where the calculus is an inductive family
   `T : S.Judg → Type`, `S.SoundT T`, a definition: a case for each move,
   its rule applied to the derivations of its premises (`e.1`, `e.2.1`, …
   of `e : Each T ps`). `Der.mapOut` then gives the calculus's own
   derivation, and `SoundT.nonempty` the proposition that there is one.
   Where there is only a proposition `D`, `S.Sound D` or `S.SoundT D`.
4. For the tactics, `Explorable S`: `candidates`, `quoteJudg` and `quoteMove`
   (`deriving Lean.ToExpr` gives them), `showJudg`, `showMove`, and
   optionally `within` and `moveSource` (a move as Lean source, for the
   lines the tactic suggests; without it Lean prints the move's term).
   `showJudg` is also how a goal is shown: there is no delaborator to
   write.
5. Optionally a certifier against what holds (level 2, above), a producer,
   and an alias.

`step` should reduce in the kernel: structural recursion, and `Decidable`
instances that compute. `docs/deciders.md` says what to avoid.

Two things that instances have found useful:

* Write `step` through one function that gives, for a move at a judgment,
  whether it applies, its premises, and what to say if it does not. The
  lemmas about `step` are then one case analysis each.
* A function or theorem by recursion on an attempt is written for every
  `o`, with `o = false` as a hypothesis where it is about derivations:
  Lean's structural recursion needs the indices of `Att S o j` to be
  variables. Before writing one, see whether it is a map out
  (`Att.mapOut`, at a constant family for a function that forgets) or
  follows from one by naturality (`Der.mapOut_map`): then there is no
  recursion to write. Where a theorem about derivations does need its own
  induction, a bound on the number of moves serves, the derivation matched
  as it stands (`Der.ofCert_cert_aux`).

A worked instance on a calculus with a decision procedure, a certified
countermodel side and a translation to natural deduction: the subframe
tableau for propositional lax logic, in
[lax-logic-in-lean](https://github.com/fairflow/lax-logic-in-lean)
(`LaxLogic/PLL/SubTab/Explore.lean`). There a derivation and a closed
tableau of the existing checker are each computed from the other, so every
proof its search finds is also a script and a tree of moves.

**Judgments that hold functions.** The tactic writes each premise as a
term, quoted from its value, and proves the node's equation
`S.step m j = .ok ps` by `rfl`. That asks the quoted premises to be, by
definition, what `step` computes. A function quoted is seldom the function
computed (`fun b => cond b 2 1` against `fun b => (fun b => cond b 1 2) (!b)`),
so an instance whose judgments hold functions sets `eqByDecide := true` and
gives `DecidableEq S.Judg`: the equation is then proved by
`step_of_stepIs (Eq.refl true)`, the kernel evaluating `step` and deciding
that its premises are the ones written. `run`, `derives` and the certifier
do not quote, and need neither. For such an instance the kernel does not
evaluate `Der.mapOut` into a type on a derivation the tactic built, and
does on the derivation rebuilt from its script (see "In the kernel",
above).

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
   `apply_move where` reads the attempt again at each query, and does not
   see past a `have` or out of a block inside a term (above).  A goal
   stated with `Der S j` is printed by Lean until the first move; the
   goals after it are shown as their judgments.
5. There is no search procedure, no model of an open goal, and no map
   between systems: those belong to the instance. The map out goes one
   way: nothing here takes a derivation of the calculus to a derivation of
   the explorer.
6. `#walk` needs the attempt to be a closed term, and evaluates compiled
   code, as the tactics do.  The view draws the premises of the focus, not
   those of the nodes above it: `up` shows them.  Going `up`, the open
   goals of the premises before the focus are counted again.  The motions
   are offered at the end of a walk only, and a click writes on its last
   line.  That every motion that can be made is among those offered is not
   stated; that each one offered can be made is proved.
7. A session (`Cursor.walk`) is a function, with no syntax of its own and
   no view in the editor.  `Cursor.script` runs its script on the focus
   from that focus's root, so its cost is the script's, not the attempt's.
   A step to a sibling counts the open goals of the premises before the old
   focus and before the new one: linear in those premises.
