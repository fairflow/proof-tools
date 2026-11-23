# Part (c): the proof explorer

Covers the second half of Adopt (the first instance, and the reviewer's
test) and the Explore stage. The library is `ProofTools.Explore`. This
part is the procedure: what to write, in what order, and how to check each
piece. Its Lean is that of `templates/Instance.lean.txt`, which was
compiled; read the template beside §2 to §5 and §10. The library's guide,
`docs/explore.md` in `proof-tools`, is the reference for the statements
the library proves.

Contents: 1 the project; 2 judgments and moves; 3 `step`; 4 the proof
system, its theorem and the map out; 5 the editor's part; 6 building with
`apply_move`; 7 scripts and trees of moves; 8 tactics of the calculus;
9 looking, and changing; 10 tests, exercises, the reviewer's test; 11 the
full exploration; 12 notes and limits; 13 judgments that are not flat.

Words, as the library uses them. An **attempt** `Att S o j` is a tree of
moves with conclusion `j` that may have open goals (`o = true`); a
**derivation** `Der S j` is an attempt with none (`o = false`); a **move**
is a rule of the calculus named by its data; a **motion** changes the
position in an attempt and nothing else. "The editor" is the Lean editor
with its infoview.

## 1. The project

Where the campaign's files go was settled at the first act. Either way the
project is a Lake package in a git repository.

**A folder under `calculi/` of `proof-tools`**: the default. Core Lean
only. The folder is a package of its own, which requires the library by
its path:

    calculi/<Calculus>/
      lakefile.toml           below
      lean-toolchain          a copy of the library's
      lake-manifest.json      written by Lake; committed
      <Calculus>.lean         the root module: it imports the others
      <Calculus>/…            the modules of the calculus
      Play/<Calculus>.lean    the reviewer's exercises, in no library
      campaign/               the campaign folder

```toml
name = "mycalculus"
defaultTargets = ["MyCalculus"]

[leanOptions]
autoImplicit = false

[[require]]
name = "proof-tools"
path = "../.."

[[lean_lib]]
name = "MyCalculus"
globs = ["MyCalculus", "MyCalculus.+"]
```

Build with `lake build`, run in `calculi/<Calculus>/`. This layout was
built on Lean v4.31.0 at the library's commit `3fa25c0`, as
`examples/Probe/` (the default folder was then named `examples/`; the
layout does not depend on the name, only on the folder being two levels
below the root), with the instance of `templates/Instance.lean.txt`.
What it showed: the first `lake build` built the library's modules as
well (39 jobs in all, under a minute); the library's build products went to
`.lake/` at the root of the checkout and the package's to its own
`.lake/`, both ignored by the library's `.gitignore`; `git status` at the
root showed that one folder and nothing else. So no tracked file outside the
folder changes (rule 7).

**A repository of its own, or a project that exists**: the same lakefile
with, in place of `path`,

```toml
git = "https://github.com/fairflow/proof-tools"
rev = "<a commit, written out>"
```

then `lake update proof-tools` and `lake build`. (This form is the
library README's; it was not run for this skill.) A project that already
requires the package `lean-certify` replaces that requirement: the two
packages hold modules of the same names.

- **Which commit** (of the checkout, in the first case; of `rev`, in the
  second): one that contains `3fa25c0`, at which this text was checked.
  The signs are the files `ProofTools/Explore/Cert.lean` and
  `ProofTools/Explore/Session.lean`. Write the commit in the plan, and do
  not move it during a stage.
- **Which Lean**: v4.31.0, the line of the library's `lean-toolchain`.
  Everything this skill shows was compiled on it; do not use a later one.
- **Three places for files.** Theory files (definitions, `step`,
  theorems), each ending with its bound on axioms. Code for the editor
  and the tests, with no bound. Both are modules of the library
  (`Basic`, `Tactic`, `Test` in the template). And the reviewer's
  exercises file, in **no** library: `Play/<Calculus>.lean`, outside
  every glob, so that no build touches it and nothing imports it. It
  imports the library; check it from the command line with
  `lake env lean Play/<Calculus>.lean`.

## 2. Judgments and moves, as data

```lean
inductive Form where … deriving DecidableEq, Repr, Lean.ToExpr
structure Seq where … deriving DecidableEq, Repr, Lean.ToExpr     -- the judgments
inductive Move where … deriving DecidableEq, Repr, Lean.ToExpr
```

- How a judgment is represented is the plan's choice of encoding
  (`reference/adopt.md` §3 for lists; §13 here where a judgment is not
  flat).
- **A move names a rule by its data**: one constructor for each rule, with
  what is needed to say which instance of the rule is meant, and no more.
  Nothing a move could compute from the judgment need be in it.
- `Lean.ToExpr` is needed for the tactics, which write judgments and moves
  as terms. These three `deriving` lines stay within
  `[propext, Quot.sound]` (compiled, under `#axioms_within_file`).
- Give formulas and judgments the source's notation (`infix`,
  `notation`): `#rules` and Lean's goals then read as the figure does.

## 3. `step`, through one function

`step m j` gives the premises of the move `m` at the judgment `j`, or the
reason it does not apply. Write it through one function that gives, for a
move at a judgment, whether it applies, its premises, and what to say if
it does not. As compiled, for a sequent with hypotheses and a conclusion:

```lean
structure Rule where
  ok : Bool
  prems : List Seq
  why : String

def Move.rule (j : Seq) : Move → Rule
  | .andL a b => ⟨decide (Form.and a b ∈ j.hyps), [⟨a :: b :: j.hyps, j.concl⟩],
      "the conjunction is not among the hypotheses"⟩
  | …

def step (m : Move) (j : Seq) : Except String (List Seq) :=
  if (m.rule j).ok then .ok (m.rule j).prems else .error (m.rule j).why
```

with two lemmas, proved once in the template whatever the rules are,
after which every lemma about `step` is one case analysis on the move:

    (m.rule j).ok = true → S.step m j = .ok (m.rule j).prems                (step_of)
    S.step m j = .ok ps → (m.rule j).ok = true ∧ ps = (m.rule j).prems      (step_ok)

- `step` is what the kernel evaluates: structural recursion only, and
  `Decidable` instances that compute (`reference/certify.md` §2).
- The message of a refusal is read by the person at the tactic. Make each
  say which side condition failed, in the source's words.
- Check each rule as you write it, with `#guard`: it applies where the
  figure says and gives the figure's premises; it refuses where a side
  condition fails.

## 4. The proof system, its one theorem, and the map out

```lean
abbrev S : ProofSystem where
  Judg := Seq
  Move := Move
  step := step
```

An `abbrev`, so that `S.Judg` unfolds to your own type where Lean looks
for instances and notations.

**S1, the soundness of the moves**, for what holds as the plan chose it.
Its statement is fixed once that choice is, so the reviewer has seen it
with the plan. The library has two forms. For a family `T` over the
judgments into any sort, with `Each T ps` one `T p` for each premise, by
position (`Each T [a, b]` is `T a ×' T b ×' PUnit`):

    S.SoundT T  :=  ∀ m j ps, S.step m j = .ok ps → Each T ps → T j

and for a proposition `P`, the premises by membership, equivalent to
`S.SoundT P` (`h.soundT` and `h.sound` pass between them):

    S.Sound P   :=  ∀ m j ps, S.step m j = .ok ps → (∀ p ∈ ps, P p) → P j

- *What holds is the family* (the default). `step_sound : S.SoundT Fam`:
  a case for each move, the rule's constructor applied to the derivations
  of its premises. With the family into `Type` it is a definition. It is
  the check that `step` says no more than the rules do. The proposition
  that there is a derivation comes with it:
  `step_sound.nonempty : S.Sound Derivable`.
- *What holds is validity.* `step_sound : S.Sound Valid`, the soundness of
  the moves themselves (`sound` in the library's `Calculus.lean`). The
  tie to the family is then two statements of its own:
  `Fam j → Valid j`, the source's soundness theorem, and S2.

**The map out.** From S1 the library gives, for every attempt and
derivation:

    S.SoundT T → (d : Att S o j) → Each T d.goals → T j              (Att.mapOut)
    S.SoundT T → Der S j → T j                                       (Der.mapOut)

and at a proposition, from `S.Sound P`, the same under the names
`Att.sound` and `Der.sound`. With the family into `Type`,
`Der.mapOut step_sound d : Fam j` is the calculus's own derivation, as
data, of what was built a move at a time; and an attempt with open goals
maps out to a function from derivations of its goals to a derivation of
its root: a derived rule.

**S2, the other direction, is not asked by the library, and is to be
stated.** S1 does not say that `step` allows every instance of every rule:
a `step` that refuses a legitimate instance is sound and unfaithful, and
only the reviewer's test would show it. Where there is a family, enter
this in `statements.md` during Adopt, PROVED or OPEN:

    Fam j → Nonempty (Der S j)

by induction on the derivation, each constructor a node (the template has
the form, compiled). It is not needed to pass the reviewer's test, and it
may stay OPEN.

## 5. The editor's part

None of it is trusted. In a file of code (the template's `Tactic.lean`):

```lean
instance : Explorable S where
  candidates := candidates        -- S.Judg → List S.Move: the moves to try at a judgment
  showJudg := Seq.show            -- a judgment as text
  showMove := Move.show           -- a move as text
  quoteJudg := inferInstanceAs (Lean.ToExpr Seq)
  quoteMove := inferInstanceAs (Lean.ToExpr Move)
  -- optional:
  within := within                -- within p j: the premise p adds nothing to the conclusion j
  moveSource m := some m.src      -- a move as the Lean source the tactic should suggest

-- `mycalc` is `apply_move` fixed to S  (a `--` comment: no doc comment here)
declare_move_tactic mycalc for S
```

- **The tactic's name becomes a keyword.** `declare_move_tactic k for S`
  makes `k` a token in every file that imports the declaration, and no
  variable, field or function can then be called `k` there. Choose a
  name that nothing else will want: not a letter, not the name of the
  system, not a word of the source's notation (`kmove`, not `k`). The
  same holds for the words of a library's own syntax: with
  `LeanCertify` imported, `size` is a keyword (from
  `certify_chunks … size n`) and cannot name a function of yours. The
  sign is a parse error at a name that was accepted the day before:
  rename, do not quote.
- `candidates` should propose every move that could apply: queries offer
  from it, and a line with holes is matched against it. Too many costs
  nothing (those that do not apply are dropped); one missing is a move the
  reviewer is never offered.
- `within p j` is yours to define: the premise `p` has nothing that the
  conclusion `j` lacks. A move with such a premise is set aside while
  another move applies, and offered when none does. Look in the source
  first: where it ends its search by a proviso (a rule is not applied
  when its premise has the same formulas as its conclusion, as a set),
  that proviso is the first candidate for `within`, and the source's
  definition of it is what to write (Q3 of the plan has its place). In
  one instance it was one line: the premise and the conclusion have the
  same set sequent, which the source defines.
- `moveSource` is optional: `m.src` is a function you write that gives
  the move as it is typed after the tactic's name (`andL p q`). Without
  it Lean prints the move's term (`andL (Form.atom 0) (Form.atom 1)`). If
  it writes atoms by name, a file that uses the tactic declares those
  names.
- `showJudg` and `showMove` draw attempts for `#walk` and `Att.render`.
- **`showJudg` is also how a goal is shown.** During `apply_move` the
  infoview shows a goal `Att S o j` as `Att S   ` and the judgment as
  `showJudg` writes it (below the head, if it takes several lines): the
  library does this for every instance, and there is no delaborator to
  write. One exception: a goal stated as `Der S j` is printed by Lean, as
  a term, until the first move. Pin what the reviewer will see with
  `trace_state` under `#guard_msgs` (§10).

## 6. Building: `apply_move`

A goal is `Att S true j` (open goals allowed) or `Der S j` (none), with
`j` a closed term. The open goals of the calculus are Lean's goals. In the
library's example (`IPC` is its proof system; `⊢`, `⋏`, `⟶` its notations;
`p`, `q` atoms):

```lean
def swap : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move impR
  apply_move andL p q
  apply_move andR
  apply_move ax
  apply_move ax
```

| line | what it does |
|---|---|
| `apply_move m` | makes the move at goal 0 |
| `apply_move m at k` | at goal `k`, counted from 0 |
| `apply_move andL`, `apply_move andL _ q` | a pattern: a move's name with arguments left out, or holes (`_`, `?_`). Matched against the candidates that apply: one match is made, and shown as "Try this"; several are offered; none is an error |
| `apply_move` | a query: offers the moves that apply, and makes none. Where none applies it is an error |
| `apply_move an` | a query: those whose names begin with `an`. A word that is exactly a move's name is a pattern, not a query |
| `apply_move where`, `apply_move where at k` | a query: draws the attempt so far, all of it, with goal 0 (goal `k`) marked `>`, its address and how many goals are open. It makes no move |
| `apply_script ls` | makes the lines of a stored script |
| `leave_open` | leaves the first goal open (`all_goals leave_open` for all) |

A move's name may be written bare, with a dot, or in full. A refusal shows
`step`'s reason: `the move does not apply to goal 0: …`. The goals are
Lean's, so Lean's own combinators apply to these tactics (`all_goals`,
`<;>`, `repeat`); of these only `all_goals leave_open` is exercised by a
test. `set_option apply_move.tryThis false` stops the "Try this" of a
filled pattern; `set_option apply_move.showWhere true` (off by default)
asks `where` after every move. Every line of the table is a line of the
alias too (`mycalc where`). `where` reads the attempt again at each query,
and does not see out of a `have` or of a block inside a term.

**No comment after a pattern.** A line `mycalc andL   -- a comment` is
offered back as `mycalc andL` with the move's arguments written after
the comment. In a file a person types in (the exercises, the tutorial),
put each comment on a line of its own.

The node the tactic builds carries the equation `S.step m j = .ok ps`,
which the kernel proves by evaluating `step` when the declaration is
checked. So a derivation built this way is checked, whatever proposed it.

## 7. Scripts, and trees of moves

A derivation has two writings as data, and each is a certificate of
part (b).

A **script** is a list of lines; a line is an open goal's number, counted
from the left over the whole attempt, and a move. It keeps the order of
the work.

| | |
|---|---|
| `run S j ls` | the attempt reached and, if a line failed, its number and the reason |
| `derives S j ls : Bool` | no line fails and no goal is left |
| `Der.ofScript j ls h` | the derivation, from a script that `derives` accepts |
| `d.script` | the script of an attempt or derivation; `run S j d.script` rebuilds it (PROVED) |
| `d.render` | the attempt drawn as text |

The lines of a proof by `apply_move` are the lines of a script:
`swap.script` gives them back.

A **tree of moves**, `Cert S`, keeps the moves and the shape of a
derivation, and nothing else. It is a rose tree of the library with a
move at each node: `.mk m [c₁, …]`.

| | |
|---|---|
| `Cert.check j c : Bool` | `step` at the root, then each child at its premise |
| `Der.ofCert j c h` | the derivation, from a tree that `Cert.check` accepts |
| `d.cert` | the tree of a derivation `d : Der S j` |

PROVED in the library: `d.cert` checks; `(Der.ofCert j c h).cert = c`;
`Der.ofCert j d.cert h = d`. So the derivations of `j` and the trees that
check at `j` are the same things. Trees are compared by `==`, printed by
`Repr` and drawn by `drawWith`, with nothing to write. An attempt with
open goals has no tree: keep it as a script.

## 8. Tactics of the calculus

`Tac S := S.Judg → Option (Script S)`: a program that gives a script for a
judgment, or nothing.

    Tac.move m          the one move, where it applies
    Tac.orElse t u      t, or u where t gives nothing
    Tac.andThen t u     t, then u at every goal t leaves
    Tac.iterate n t     t at every goal it leaves, at most n deep
    Tac.first ts        the first of a list that gives a script
    Script.shift k ls   the same script at goal k of a larger attempt

PROVED in the library: a tactic built from moves with these never gives a
script with a failing line. Whether the script closes its goal is for
`derives` to say. So a wrong tactic costs a failure, never a wrong
derivation. Use them for the routine steps a reader of the source does
without comment (Q4), and as producers (part (b) §4).

## 9. Looking, and changing

`#walk d m₁ m₂ …` takes an attempt or derivation `d` (a name, or a closed
term in parentheses) and makes the motions from its root. It shows the
view at the position reached, and changes nothing.

| motion | goes to |
|---|---|
| `up` | the node the focus is a premise of |
| `down i` | premise `i` of the focus, from 0 |
| `left`, `right` | the premise before, or after, of the same node |
| `top` | the root |
| `goal k` | open goal `k` of the whole attempt, from 0 |

The view: the nodes from the root to the focus, each with its move; the
focus, marked `>`; its premises, numbered, an open one marked `?`; then
the address of the focus and where the open goals are. Written a motion to
a line, the view after each line is a message at that line. After the last
view the motions that can be made are offered, and a click writes one
(`set_option walk.offer false` for none, as in a file of tests). With
`set_option walk.panel true` the whole attempt is also drawn as a tree in
the infoview, with nodes to click: a trial of the library, off by
default, described in its guide.

**As a tactic block.** `example : Walk d := by` followed by motions, one
to a line: the goal after each line is the view there, so the infoview
follows the editor's cursor and no message is written. It offers nothing
to click; `#walk` does.

What looking is for in a campaign: showing the reviewer what a search
found; showing what an attempt left open, and where; reading a long
derivation a node at a time.

**Changing an attempt that is built**, at the position of a cursor, is
in the library as functions, with what each does to the open goals
PROVED: `c.rule m` (a move at the open goal in focus), `c.prune` (the
focus becomes an open goal again), `c.graft d`, `c.script ls`, all uses of
one change, `c.replace d`. In turn with motions they make a session,
`Cursor.walk` on a list of commands:

```lean
#eval IO.println <| match (Cursor.ofAtt att).walk
    [.motion (.goal 0), .rule .ax, .motion .up, .prune] with
  | .ok c => c.viewAll
  | .error (n, why) => s!"command {n} fails: {why}"
```

(compiled, on an attempt `att` of the template's instance). A session is
not a certificate: the certificate is read off its result
(`c.toRoot.script`). **No tactic or command of the editor runs a
session**: in the editor an attempt is changed only by a move at an open
goal.

## 10. Tests, the exercises file, and the reviewer's test

**The tests file** (a module of the library, every message pinned with
`#guard_msgs`). The template's `Test.lean` is the compiled model of all
nine kinds; the library's own tests have more of each.

1. each rule by `#guard` on `step`: where it applies, and where it is
   refused;
2. the source's own derivations, as reference derivations by the tactic;
3. each known non-theorem, taken as far as it goes, with what the plan
   predicted: the refusal of a move with its message, or a query where no
   move applies, or an attempt left open (`leave_open`);
4. every refusal message of `step`, seen once;
5. a query and a pattern;
6. a goal as the infoview shows it, `trace_state` after a move (its
   message is of kind `trace:`); and the attempt so far, as `where` draws
   it;
7. a tree of moves and a script, each checked by the kernel with no
   tactic; of each, one with a wrong move and one that stops early,
   rejected (part (b) §5);
8. a derivation walked: by `#walk`, and as a tactic block;
9. where the family is into `Type`: a derivation mapped out
   (`Der.mapOut step_sound`), equal by `rfl` to the same derivation
   written with the family's constructors.

**A printer that writes a combining character.** Where the source marks
a letter (`p̄` for a negated atom) and the printer writes the letter
followed by a combining character (the macron U+0304), the text a test
expects must be those two characters. `#guard` on a string and
`#guard_msgs` on a message compare character by character, and text
typed or pasted with the precomposed letter (`ā`, one character) fails
against output that looks the same.

- In an expected string, spell the mark as an escape: `"ā ∧ b̄"`.
- In a pinned message no escape is read: paste the message from Lean's
  output, and do not retype it.
- Say at the head of the tests file how marked letters are spelt in it,
  comments included: an editor that composes the two characters into one
  breaks the comparison.
- A tool that writes the file for you may put the character where you
  typed the escape. Read back what is in the file.

**The exercises file** (`templates/Play.lean.txt`), in no library. It is
the reviewer's. Its header says how to type a line and gives the rule
table in brief; each exercise is a statement with the first query already
written. One exception: where no move applies to the judgment as it
stands, a query is an error, and the file must elaborate with none. For
such an exercise the query is left for the reviewer to type, and the
text says so, and says what the message will be. Comments are on lines
of their own (§6). The reference derivations stay in the tests file,
not here.
Where the source has no worked derivations, take the simplest instances of
its theorems, or the axioms of the logic, and say that the choice is
yours. Check that the file elaborates (§1) before the report. Once the
reviewer has it, do not change it without saying so: a fault found at the
reviewer's test is repaired in the calculus's modules, and a change to
the file itself is recorded in `gates.md`.

**The reviewer's test** is the gate of Adopt. The reviewer types the
source's derivations, with `rule-table.md` beside the source's figure. In
the report's part (iii) say, for each exercise, what should happen: which
moves are offered, where a non-theorem stops and how. Afterwards, in
`gates.md`: what was typed, what happened, and what was asked for that the
instance could not do.

## 11. The full exploration

From Q4 and from the record of the reviewer's test, list what a user of
this calculus needs. Then serve each from what exists:

| need | from |
|---|---|
| the routine steps done at once | a `Tac`. Its script is made at a goal by `apply_script`, which takes the script as a closed term: the goal's judgment is written out again for the `Tac`. No tactic applies a `Tac`, or a producer, to the goal in front of it |
| a proof found by the search, to read | the search's script or attempt, and `#walk` |
| a failed attempt, to see why | while building, `where`; afterwards `leave_open`, then `#walk d goal k` |
| a proof kept and replayed | `d.script`, `apply_script` |
| a result used in the mathematics | `Der.mapOut`, `Att.mapOut`: the calculus's own derivation, as data where the family is into `Type` (an attempt is a derived rule, from its open goals to its root); at a proposition, `Der.sound`, `Att.sound` |
| a branch taken back, and tried another way | in the editor: delete the lines and type others. As functions: a session (§9). No tactic or command runs a session: report the need |

**The tutorial**, `Play/<Calculus>Tutorial.lean`: a Lean file in the form
of the exercises file, in no library, with its prose in comments, that
takes a new user through building, a query, a pattern, a script, a tactic
of the calculus, a walk, and one non-theorem. Unlike the exercises it
explains each step and shows the answers. Its comments are on lines of
their own, never after a line of the tactic (§6). The reviewer works
through it: that is the gate.

**The user's guide**: a page in the campaign folder: how a goal reads,
the moves with their rules, the lines of the tactic, the messages. The
section "Lean tactics" of the library's guide is the model.

## 12. Notes from instances, and limits

- **Recursion on an attempt is written for every `o`**, with `o = false`
  as a hypothesis where it is about derivations: Lean's structural
  recursion needs the indices of `Att S o j` to be variables. It is the
  one kind of proof repair an instance has needed.
- **Judgments that hold functions** (no calculus on lists or trees of
  formulas has them). The tactic proves a node's equation by `rfl`, which
  asks the premises as quoted to be by definition what `step` computes,
  and a function quoted is seldom the function computed. Such an instance
  sets `eqByDecide := true` in `Explorable` and gives `DecidableEq S.Judg`.
  For it the kernel does not evaluate a map out into a type on a
  derivation the tactic built: map out the derivation rebuilt from its
  script, `Der.ofScript j d.script (derives_script d)`. The library's
  guide has the reason ("In the kernel"), and its tests both cases.
- `omega` given a conjunction brings in `Classical.choice`; split first.
- The tactics and `#walk` need the judgment, or the attempt, to be a
  closed term, and evaluate compiled code.
- An equation between a map out and the verdict of a script, by `rfl`,
  ran out of heartbeats in the elaborator; with the verdict of a tree it
  went through (the template's ninth test). Compare longer derivations
  through a function on them.
- The view draws the premises of the focus only; `up` shows those above.
- `Att.script` is quadratic on a derivation as deep as it is long.
- **Not in the library**: a search; a model of an open goal; a map
  between two systems, or from the family's derivations to the
  explorer's; a tactic or command of the editor for a session (§9); a
  tactic that applies a `Tac` or a producer to the goal in front of you;
  a tree of moves for an attempt with open goals; an instance whose
  judgments are not flat (§13).

## 13. Judgments that are not flat

In some calculi a judgment has structure inside it (a tree, a list of
sequents, sequents within sequents), and a rule acts at a place inside
one. How such a judgment is represented, how a rule and a move name the
place they act at, and what a move carries, are the plan's choices of
encoding, signed by the reviewer with the plan. This section gives the
options and what each costs. It chooses nothing, and it gives no rule of
any calculus. One instance is of this kind: `calculi/BrunnlerK/` of
`proof-tools`, nested sequents by the second option below.

| option | what you get | what it costs |
|---|---|---|
| a type of your own: an inductive type whose constructors hold lists of it | the source's shape, as the source writes it | every function on it is yours: what is at a place, the judgment changed at a place, the printer. On Lean v4.31.0 `Repr` and `Lean.ToExpr` derive for such a type and `DecidableEq` does not (tried): equality is a Boolean test written by recursion, with the proof that it decides |
| a type of your own that holds itself directly and never in a list: the inner judgments joined by a constructor, `leaf` of a node's formulas and `cons` of an inner judgment and the rest | the source's shape; every `deriving` line works, `DecidableEq`, `Repr` and `Lean.ToExpr` (tried on Lean v4.31.0, and compiled: `calculi/BrunnlerK/BrunnlerK/Sequent.lean` of `proof-tools`) | the inner judgments of a node are not a `List`, and its formulas sit at the end of the chain: the formulas of a node, its inner judgments as a list, the one at a position, a formula or an inner judgment added or replaced, are each a recursion of yours, with its lemmas. Written with the constructors a judgment cannot be read: a term syntax is needed (below) |
| the library's rose trees, `RTree κ α`: a node has a label in `α` and a list of children, each along an edge labelled in `κ` | the subtree at an address (`get?`), the label there (`at?`), the tree changed there (`updateAt`), with laws PROVED; Huet's zipper; a printer (`drawWith`); an equality test PROVED to decide equality (`RTree.beq_iff_eq`); `Repr`. On a small tree `get?`, `at?`, `updateAt` and `beq` reduce in the kernel (tried, by `decide +kernel`) | the source's judgment must be read as such a tree: what the labels are is yours to say, and a divergence of representation. An address is the list of edge labels from the root, and `get?`, `updateAt` take the first child along an edge: children of one node are told apart by their edge labels, or not at all. `Lean.ToExpr` does not derive for `RTree` (tried): it is written by recursion. `DecidableEq` comes from the equality test (`instDecidableEqOfLawfulBEq` of core Lean, a definition and not an instance) |
| a flat type: lists, with the structure carried as data beside them | every `deriving` line works | the structure the source draws becomes an invariant to state and keep |

The rose trees are four modules in the namespace `ProofTools.Zip`
(`ProofTools.Zipper.Rose`, `RoseUpdate`, `RoseRender`, `RoseIndexed`),
each within `[propext, Quot.sound]`. The section "The zipper" of the
library's README lists their functions and theorems, and
`ProofToolsTest/Zipper/Rose.lean` exercises every move and edit.

Whatever is chosen:

- **the functions the family's rules use are the functions `step` uses.**
  In the family they stand in side conditions and premises, never in a
  conclusion (`reference/adopt.md` §3). Then S1 is one constructor for
  each move, and S2 one node for each constructor;
- `step` is on the path the kernel evaluates: try early that one step on a
  small judgment reduces, since `#guard` does not go through the kernel.
  Core Lean has no `DecidableEq (Except String (List _))`, so the
  equation `S.step m j = .ok ps` is not one `decide` can be asked.
  State the check through `Except.toOption`:

  ```lean
  example : (S.step m j).toOption = some ps := by decide +kernel
  ```

  and a refusal as `(S.step m j).toOption = none`;
- find out during the Survey what derives for the proposed type (a few
  lines suffice), and budget in the plan the groundwork that remains: the
  quoting, the equality, the printer, the candidates. Try the same on
  the type of models and of every other certificate the plan names: a
  tree of worlds is a type that holds a list of itself, and gets no
  `DecidableEq`. A construction of Prove that would test two of its
  members for equality (a model whose worlds are the subtrees of a
  tree) is then to be designed another way, and the plan is where that
  is cheap to see;
- **S1, where every rule begins by looking its place up.** The
  template's S1 is one match on the move and the judgment, each case a
  constructor: it relies on `m.rule j` reducing once the move and the
  shape of the judgment are known. A rule that begins with "the node
  at this path" does not reduce for a variable judgment. Split the
  rule in two: the rule given what is at the place, and the lookup.

  ```lean
  def Move.ruleAt (Γ Θ : Judg) : Move → Rule        -- the rule, given the node Θ at the move's path
  def Move.rule (Γ : Judg) (m : Move) : Rule :=
    match Γ.node? m.path with
    | some Θ => m.ruleAt Γ Θ
    | none => ⟨false, [], "the sequent has no node at this path"⟩

  theorem rule_some (h : Γ.node? m.path = some Θ) : m.rule Γ = m.ruleAt Γ Θ
  theorem rule_none (h : Γ.node? m.path = none) : (m.rule Γ).ok = false
  ```

  S1 then matches on `Γ.node? m.path` first, with the equation kept
  (`match hΘ : Γ.node? m.path with`), and under `some Θ` is the
  template's match, on `ruleAt`. A rule that looks up a second thing
  (a part of the node, by position) is split once more in the same
  way, as a function of its own on what the second lookup returns,
  with its own case of S1: a `match` on the second lookup inside the
  first does not generalise the hypotheses. S2 is then one equation
  for each constructor, `S.step m Γ = .ok [the premises, written out]`,
  proved by `simp` with the side conditions. Compiled:
  `calculi/BrunnlerK/BrunnlerK/Proof.lean` of `proof-tools`
  (`Move.ruleAt`, `diaRule`, `step_sound`);
- **prove S2 in Adopt.** §4 lets it stay OPEN. For a calculus of this
  kind it is worth its lines (forty, in the instance above): the
  premises of `step` and of the family are the same functions applied
  at a place, and S2 is the one check that `step` refuses no instance
  of a rule. The reviewer's test shows a refusal only at the instances
  the reviewer happens to type;
- **a term syntax for judgments.** A judgment in a statement, a test
  or an exercise is a closed term, and written with the constructors
  it cannot be read against the source. Write a syntax that reads as
  the source does: for nested sequents, `seq[A, B, [C, [D]]]`, where
  an item in list brackets is an inner judgment and anything else a
  formula. One `syntax "seq[" term,* "]" : term` and one `macro_rules`
  that sorts the items did it, in a dozen lines, with no syntax
  category. The kernel sees the term the macro gives, and the reviewer
  sees the notation: pin in the tests, by `rfl`, that a judgment so
  written is the term meant, as the display of a goal is pinned.
  Compiled: `calculi/BrunnlerK/BrunnlerK/Tactic.lean`;
- **the rule table needs the definitions.** `#rules` prints these
  functions by name, so the table has three further sections for this
  case (`reference/adopt.md` §4; `templates/rule-table.md`).
