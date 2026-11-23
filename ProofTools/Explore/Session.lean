/-
# `ProofTools.Explore.Session`: changing an attempt that is built

An attempt that is built is changed at a position: the cursor goes there
by motions (`ProofTools.Explore.Motion`), and the attempt at the focus is
replaced.  There is one change, `Cursor.replace` (the zipper's `replace`,
in `ProofTools.Explore.Cursor`), and three uses of it:

    c.replace d     the focus becomes the attempt `d`, at the same judgment
    c.rule m        an open goal becomes the node of the move `m`, its
                    premises open (what a line of a script does at its goal)
    c.prune         the focus, whatever it is, becomes an open goal
    c.graft d       an open goal becomes the attempt `d`

and a fourth, for an attempt that is given as a script:

    c.script ls     the script `ls` is run on the attempt at the focus, its
                    goals numbered within the focus, and the result
                    replaces the focus

**What a change does** (all PROVED; `goalsL`, `goalsR` are the open goals
of the whole attempt left and right of the focus, `c.Ok` says that `c.left`
is the number of the first):

    (c.replace d).toRoot.goals = goalsL ++ d.goals ++ goalsR               (E1, Cursor.goals_replace)
    c.prune.toRoot.goals = goalsL ++ c.pos.i :: goalsR                     (Cursor.goals_prune)
    c.rule m = .ok c' → ∃ ps, S.step m c.pos.i = .ok ps ∧
        c'.toRoot.goals = goalsL ++ ps ++ goalsR                           (Cursor.goals_rule)
    c.rule m = .ok c' → c'.prune = c                                       (Cursor.prune_rule)
    c.Ok → c.rule m = .ok c' → c.toRoot.step ⟨c.left, m⟩ = .ok c'.toRoot   (Cursor.toRoot_rule)
    c.Ok → c.script ls = .ok c' →
        c.toRoot.run (ls.shift c.left) = { att := c'.toRoot }              (Cursor.toRoot_script)
    c.Ok → (c.replace d).Ok                                                (Cursor.ok_replace)

So a rule at the focus is the line of a script at goal number `c.left` of
the whole attempt, and a script at the focus is the script shifted by
`c.left`, run from the root.  Soundness asks nothing new: every state of a
cursor is an attempt, `c.toRoot`, to which `Att.mapOut` and `Att.sound`
apply.

**A session** is commands in turn: motions, which are those of `Motion`,
and changes.

    inductive Cmd S
      | motion (m : Motion)  | rule (m : S.Move)  | prune  | script (ls : Script S)

    Cursor.cmd c x       one command: the cursor reached, or why not
    Cursor.walk c cs     commands in turn: the cursor reached, or the number
                         of the first command that fails and why

`Cursor.walk` is the loop of `Cursor.moves` (`Cursor.trailBy`) at commands.
A graft enters a session as `script`, since a command cannot hold an
attempt whose type depends on the focus.  PROVED:

    c.Ok → c.walk cs = .ok c' → c'.Ok                                      (Cursor.walk_ok)
    c.walk (ms.map .motion) = c.moves ms                                   (Cursor.walk_motions)
    c.Ok → c.walk (ms.map .motion) = .ok c' → c'.toRoot = c.toRoot ∧ c'.Ok (S2, Cursor.walk_motions_ok)

**A script is a session** that only goes to an open goal and makes a move
there.  `Script.cmds ls` is `goal l.goal`, then `rule l.move`, for each
line `l` (written `ls.cmds` below).
PROVED, for `d.run ls` and so for `run S j ls` (`d` the open goal):

    (d.run ls).failed = none →
        ∃ c, (Cursor.ofRoot d).walk ls.cmds = .ok c ∧ c.toRoot = (d.run ls).att   (S1, Att.walk_cmds)
    (Cursor.ofRoot d).walk ls.cmds = .ok c → d.run ls = { att := c.toRoot }       (Att.run_of_walk_cmds)

A session is not a certificate.  It records what was done, with its
retreats; the certificate is read off the result (`c.toRoot.script`, or its
tree of moves), and the kernel checks that.

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Explore.Motion
import ProofTools.Explore.Tac

namespace ProofTools.Explore

open ProofTools

variable {S : ProofSystem}

/-! ## One change at the focus -/

/-- The whole attempt after a change: the path, filled with the new focus
(the zipper's `toRoot_replace`). -/
theorem Cursor.toRoot_replace {j : S.Judg} (c : Cursor S j) (d : Att S true c.pos.i) :
    (c.replace d).toRoot = Zip.Deriv.Path.plug c.pos.z.path d :=
  Zip.Deriv.Zipper.toRoot_replace c.pos.z d

/-- **(E1) The open goals after a change**: those left of the focus, those
of the new focus, those right of it. -/
theorem Cursor.goals_replace {j : S.Judg} (c : Cursor S j) (d : Att S true c.pos.i) :
    (c.replace d).toRoot.goals =
      Path.goalsL c.pos.z.path ++ d.goals ++ Path.goalsR c.pos.z.path := by
  rw [Cursor.toRoot_replace, Path.goals_plug]

/-- The new focus is what was put there. -/
theorem Cursor.focus_replace {j : S.Judg} (c : Cursor S j) (d : Att S true c.pos.i) :
    (c.replace d).focus = d := rfl

/-- Replacing the focus by itself changes nothing. -/
theorem Cursor.replace_focus {j : S.Judg} (c : Cursor S j) : c.replace c.pos.z.focus = c := rfl

/-- Of two changes at one position the second stands. -/
theorem Cursor.replace_replace {j : S.Judg} (c : Cursor S j) (d e : Att S true c.pos.i) :
    (c.replace d).replace e = c.replace e := rfl

/-- **The open goals after pruning**: the judgment of the focus is one of
them, between those left and right of it. -/
theorem Cursor.goals_prune {j : S.Judg} (c : Cursor S j) :
    c.prune.toRoot.goals = Path.goalsL c.pos.z.path ++ c.pos.i :: Path.goalsR c.pos.z.path := by
  simp [Cursor.prune, Cursor.goals_replace]

/-- **What a rule does to the open goals**: the goal at the focus gives way
to the premises of the move. -/
theorem Cursor.goals_rule {j : S.Judg} {m : S.Move} {c c' : Cursor S j} (h : c.rule m = .ok c') :
    ∃ ps, S.step m c.pos.i = .ok ps ∧
      c'.toRoot.goals = Path.goalsL c.pos.z.path ++ ps ++ Path.goalsR c.pos.z.path := by
  obtain ⟨-, nd, hnd, rfl⟩ := Cursor.rule_eq_ok h
  obtain ⟨ps, hs, rfl⟩ := Att.ofMove_eq_ok hnd
  exact ⟨ps, hs, by simp [Cursor.goals_replace]⟩

/-- **Prune undoes a rule.** -/
theorem Cursor.prune_rule {j : S.Judg} {m : S.Move} {c c' : Cursor S j} (h : c.rule m = .ok c') :
    c'.prune = c := by
  obtain ⟨hg, nd, -, rfl⟩ := Cursor.rule_eq_ok h
  have hf := Att.eq_goal_of_isGoal _ hg
  have e : c.replace .goal = c.replace c.pos.z.focus := by rw [hf]
  exact e

/-- **A rule at the focus is a line of a script at the root**: the move at
goal number `c.left` of the whole attempt (`Att.step`, the specification of
a line). -/
theorem Cursor.toRoot_rule {j : S.Judg} {m : S.Move} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.rule m = .ok c') : c.toRoot.step ⟨c.left, m⟩ = .ok c'.toRoot := by
  obtain ⟨hg, nd, hnd, rfl⟩ := Cursor.rule_eq_ok h
  obtain ⟨ps, hs, rfl⟩ := Att.ofMove_eq_ok hnd
  have hf := Att.eq_goal_of_isGoal _ hg
  have key := Att.step_plug_goal hs c.pos.z.path
  rw [Cursor.toRoot_replace, show c.left = (Path.goalsL c.pos.z.path).length from hc]
  show (Zip.Deriv.Path.plug c.pos.z.path c.pos.z.focus).step _ = _
  rw [hf]
  exact key

/-- A graft that is made has replaced an open goal. -/
theorem Cursor.graft_eq_ok {j : S.Judg} {c c' : Cursor S j} {d : Att S true c.pos.i}
    (h : c.graft d = .ok c') : c.pos.z.focus.isGoal = true ∧ c' = c.replace d := by
  unfold Cursor.graft at h
  split at h
  · next hg => exact ⟨hg, (Except.ok.inj h).symm⟩
  · cases h

/-- **A script at the focus**: its lines are made on the attempt at the
focus, their goals numbered within it, and what they leave replaces the
focus.  If a line fails nothing is changed, and the line is named.  At an
open goal this grafts the attempt the script builds. -/
def Cursor.script {j : S.Judg} (c : Cursor S j) (ls : Script S) : Except String (Cursor S j) :=
  let r := c.pos.z.focus.run ls
  match r.failed with
  | none => .ok (c.replace r.att)
  | some (n, e) => .error s!"line {n} of the script: {e}"

/-- A script that is run at the focus had no failing line, and has replaced
the focus by what it left. -/
theorem Cursor.script_eq_ok {j : S.Judg} {ls : Script S} {c c' : Cursor S j}
    (h : c.script ls = .ok c') :
    (c.pos.z.focus.run ls).failed = none ∧ c' = c.replace (c.pos.z.focus.run ls).att := by
  unfold Cursor.script at h
  simp only at h
  split at h
  · next hf => exact ⟨hf, (Except.ok.inj h).symm⟩
  · cases h

/-- **A script at the focus is the script, shifted, at the root**: its goal
numbers moved up by the goals left of the focus (`Att.runFrom_shift`). -/
theorem Cursor.toRoot_script {j : S.Judg} {ls : Script S} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.script ls = .ok c') : c.toRoot.run (ls.shift c.left) = { att := c'.toRoot } := by
  obtain ⟨hf, rfl⟩ := Cursor.script_eq_ok h
  have key := Att.runFrom_shift c.pos.z.path ls 0 0 c.pos.z.focus [] hf
  rw [List.append_nil] at key
  rw [show c.left = (Path.goalsL c.pos.z.path).length from hc]
  exact key

/-! ## A session -/

/-- **A command of a session**: a motion of the cursor, or a change at the
focus. -/
inductive Cmd (S : ProofSystem) where
  /-- A motion (`Motion`): `up`, `down i`, `left`, `right`, `top`, `goal k`. -/
  | motion (m : Motion)
  /-- The move `m` at the open goal at the focus. -/
  | rule (m : S.Move)
  /-- The focus becomes an open goal. -/
  | prune
  /-- The script `ls` on the attempt at the focus, its goals numbered within
  the focus. -/
  | script (ls : Script S)

/-- **One command**: the cursor reached, or why the command cannot be
made. -/
def Cursor.cmd {j : S.Judg} (c : Cursor S j) : Cmd S → Except String (Cursor S j)
  | .motion m => c.tryMove m
  | .rule m => c.rule m
  | .prune => .ok c.prune
  | .script ls => c.script ls

/-- **Commands in turn**: the cursor reached, or the number of the first
command that fails (from `n`) and why.  The loop of `Cursor.movesFrom`
(`Cursor.trailBy`), at commands. -/
def Cursor.walkFrom {j : S.Judg} (n : Nat) (c : Cursor S j) (cs : List (Cmd S)) :
    Except (Nat × String) (Cursor S j) :=
  (Cursor.trailBy Cursor.cmd n c cs).result

/-- **A session**: commands in turn, numbered from 0. -/
def Cursor.walk {j : S.Judg} (c : Cursor S j) (cs : List (Cmd S)) :
    Except (Nat × String) (Cursor S j) := Cursor.walkFrom 0 c cs

theorem Cursor.walkFrom_nil {j : S.Judg} (n : Nat) (c : Cursor S j) :
    Cursor.walkFrom n c [] = .ok c := rfl

theorem Cursor.walkFrom_cons {j : S.Judg} (n : Nat) (c : Cursor S j) (x : Cmd S)
    (cs : List (Cmd S)) :
    Cursor.walkFrom n c (x :: cs) =
      match c.cmd x with
      | .ok c' => Cursor.walkFrom (n + 1) c' cs
      | .error e => .error (n, e) :=
  Cursor.trailBy_result_cons Cursor.cmd n c x cs

theorem Cursor.tryMove_eq_ok {j : S.Judg} {m : Motion} {c c' : Cursor S j}
    (h : c.tryMove m = .ok c') : c.move m = some c' := by
  unfold Cursor.tryMove at h
  split at h
  · next c₁ hm => rw [hm, Except.ok.inj h]
  · cases h

/-- **A command keeps the count right.** -/
theorem Cursor.cmd_ok {j : S.Judg} {x : Cmd S} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.cmd x = .ok c') : c'.Ok := by
  cases x with
  | motion m => exact (Cursor.move_some hc (Cursor.tryMove_eq_ok h)).2
  | rule m =>
    obtain ⟨-, nd, -, rfl⟩ := Cursor.rule_eq_ok h
    exact Cursor.ok_replace hc nd
  | prune =>
    obtain rfl := Except.ok.inj h
    exact Cursor.ok_replace hc _
  | script ls =>
    obtain ⟨-, rfl⟩ := Cursor.script_eq_ok h
    exact Cursor.ok_replace hc _

theorem Cursor.walkFrom_ok {j : S.Judg} : ∀ (cs : List (Cmd S)) (n : Nat) {c c' : Cursor S j},
    c.Ok → Cursor.walkFrom n c cs = .ok c' → c'.Ok
  | [], _, _, _, hc, h => by
    obtain rfl := Except.ok.inj h
    exact hc
  | x :: cs, n, c, c', hc, h => by
    rw [Cursor.walkFrom_cons] at h
    split at h
    · next c₁ h₁ => exact Cursor.walkFrom_ok cs (n + 1) (Cursor.cmd_ok hc h₁) h
    · cases h

/-- **A session keeps the count right**: after it `goal k` still finds open
goal `k`. -/
theorem Cursor.walk_ok {j : S.Judg} {cs : List (Cmd S)} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.walk cs = .ok c') : c'.Ok :=
  Cursor.walkFrom_ok cs 0 hc h

/-! ## A session of motions only -/

theorem Cursor.walkFrom_motions {j : S.Judg} : ∀ (ms : List Motion) (n : Nat) (c : Cursor S j),
    Cursor.walkFrom n c (ms.map Cmd.motion) = Cursor.movesFrom n c ms
  | [], _, _ => rfl
  | m :: ms, n, c => by
    rw [List.map_cons, Cursor.walkFrom_cons, Cursor.movesFrom_cons]
    simp only [Cursor.cmd, Cursor.tryMove]
    cases c.move m with
    | some c' => exact Cursor.walkFrom_motions ms (n + 1) c'
    | none => rfl

/-- **A session of motions only is the motions in turn** (`Cursor.moves`). -/
theorem Cursor.walk_motions {j : S.Judg} (ms : List Motion) (c : Cursor S j) :
    c.walk (ms.map Cmd.motion) = c.moves ms :=
  Cursor.walkFrom_motions ms 0 c

/-- **(S2) A session of motions only leaves the attempt unchanged**, and the
count of goals stays right. -/
theorem Cursor.walk_motions_ok {j : S.Judg} {ms : List Motion} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.walk (ms.map Cmd.motion) = .ok c') : c'.toRoot = c.toRoot ∧ c'.Ok := by
  rw [Cursor.walk_motions] at h
  exact Cursor.moves_ok hc h

/-! ## A script is a session -/

/-- **The session of a script**: for each line, to the goal it names, then
its move there. -/
def Script.cmds : Script S → List (Cmd S)
  | [] => []
  | l :: ls => .motion (.goal l.goal) :: .rule l.move :: Script.cmds ls

/-- The session of a script and the run of the script, from one cursor: if
the session succeeds, the run is its result and has no failing line; if a
command fails, a line of the run fails. -/
theorem Cursor.walkFrom_cmds {j : S.Judg} : ∀ (ls : Script S) (n k : Nat) {c : Cursor S j}, c.Ok →
    (∀ c', Cursor.walkFrom k c (Script.cmds ls) = .ok c' → Cursor.runFrom n c ls = { att := c'.toRoot }) ∧
    (∀ e, Cursor.walkFrom k c (Script.cmds ls) = .error e → (Cursor.runFrom n c ls).failed.isSome = true)
  | [], _, _, _, _ => by
    refine ⟨fun c' h => ?_, fun e h => ?_⟩
    · obtain rfl := Except.ok.inj h
      rfl
    · cases h
  | l :: ls, n, k, c, hc => by
    have hw : Cursor.walkFrom k c (Script.cmds (l :: ls)) =
        match c.seek l.goal with
        | none => .error (k, c.whyNot (.goal l.goal))
        | some c₁ =>
          match c₁.rule l.move with
          | .ok c₂ => Cursor.walkFrom (k + 1 + 1) c₂ (Script.cmds ls)
          | .error e => .error (k + 1, e) := by
      simp only [Script.cmds, Cursor.walkFrom_cons, Cursor.cmd, Cursor.tryMove, Cursor.move]
      cases c.seek l.goal <;> rfl
    cases hs : c.seek l.goal with
    | none =>
      have hw' : Cursor.walkFrom k c (Script.cmds (l :: ls)) =
          .error (k, c.whyNot (.goal l.goal)) := by rw [hw, hs]
      rw [hw']
      refine ⟨fun c' h => (nomatch h), fun e _ => ?_⟩
      simp only [Cursor.runFrom, Cursor.step_eq, hs]
      rfl
    | some c₁ =>
      obtain ⟨-, -, -, o₁⟩ := Cursor.seek_some hc hs
      cases hr : c₁.rule l.move with
      | error e' =>
        have hw' : Cursor.walkFrom k c (Script.cmds (l :: ls)) = .error (k + 1, e') := by
          rw [hw, hs]
          simp only [hr]
        rw [hw']
        refine ⟨fun c' h => (nomatch h), fun e _ => ?_⟩
        simp only [Cursor.runFrom, Cursor.step_eq, hs, hr]
        rfl
      | ok c₂ =>
        have hw' : Cursor.walkFrom k c (Script.cmds (l :: ls)) =
            Cursor.walkFrom (k + 1 + 1) c₂ (Script.cmds ls) := by
          rw [hw, hs]
          simp only [hr]
        have hrun : Cursor.runFrom n c (l :: ls) = Cursor.runFrom (n + 1) c₂ ls := by
          simp only [Cursor.runFrom, Cursor.step_eq, hs, hr]
        obtain ⟨-, nd, -, rfl⟩ := Cursor.rule_eq_ok hr
        rw [hw', hrun]
        exact Cursor.walkFrom_cmds ls (n + 1) (k + 1 + 1) (Cursor.ok_replace o₁ nd)

/-- **(S1) A script is a session**: if no line of the run fails, the session
that goes to each line's goal and makes its move there succeeds, and its
result is the attempt the run reaches. -/
theorem Att.walk_cmds {j : S.Judg} (d : Att S true j) (ls : Script S)
    (h : (d.run ls).failed = none) :
    ∃ c, (Cursor.ofRoot d).walk (Script.cmds ls) = .ok c ∧ c.toRoot = (d.run ls).att := by
  obtain ⟨h₁, h₂⟩ := Cursor.walkFrom_cmds ls 0 0 (Cursor.ok_ofRoot d)
  cases hw : Cursor.walkFrom 0 (Cursor.ofRoot d) (Script.cmds ls) with
  | ok c =>
    have hr : d.run ls = { att := c.toRoot } := h₁ c hw
    exact ⟨c, hw, by rw [hr]⟩
  | error e =>
    have hf : (d.run ls).failed.isSome = true := h₂ e hw
    rw [h] at hf
    cases hf

/-- **(S1, the converse)** If the session of a script succeeds, the run of
the script is its result, with no failing line. -/
theorem Att.run_of_walk_cmds {j : S.Judg} (d : Att S true j) (ls : Script S) {c : Cursor S j}
    (h : (Cursor.ofRoot d).walk (Script.cmds ls) = .ok c) : d.run ls = { att := c.toRoot } :=
  (Cursor.walkFrom_cmds ls 0 0 (Cursor.ok_ofRoot d)).1 c h

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
