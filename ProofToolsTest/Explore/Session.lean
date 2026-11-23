/-
Tests of `ProofTools.Explore.Session`: the changes at the focus (`replace`,
`rule`, `prune`, `graft`, `script`) and a session of commands
(`Cursor.walk`), on the example calculus and on the counting system.

What is checked by running: a derivation built by a session of rules and
motions; a branch pruned and built again another way; a script run at a
focus, and what it is at the root; every way a command can fail, with the
number of the command and the reason; the open goals after each change
(E1); a session of motions only (S2); a script as a session, on every
script of length at most 3 over an alphabet (S1); a session in the kernel.
The statements PROVED are pinned at the end.
-/
import ProofTools.Audit
import ProofToolsTest.Explore.Run
import ProofToolsTest.Explore.Count

namespace ProofToolsTest.Explore.SessionTest

open ProofTools ProofTools.Explore ProofToolsTest.Explore
open RunTest

/-- The cursor at the open goal of a sequent. -/
def start (s : Seq) : Cursor IPC s := .ofRoot .goal

/-- What a session leaves: the whole attempt drawn, or the failing command. -/
def shown {s : Seq} (c : Cursor IPC s) (cs : List (Cmd IPC)) : String :=
  match c.walk cs with
  | .ok c' => c'.viewAll
  | .error (n, why) => s!"command {n} fails: {why}"

/-! ## A derivation built by a session: rules, and motions between them -/

/-- `(p ∧ q) → (q ∧ p)`, built where the cursor is: each rule at the focus,
and a motion to the premise worked on next. -/
def build : List (Cmd IPC) :=
  [.rule .impR, .motion (.down 0), .rule (.andL p q), .motion (.down 0), .rule .andR,
   .motion (.down 0), .rule .ax, .motion .right, .rule .ax]

#guard ((start swap).walk build).toOption.map (·.toRoot.goals) == some []
-- it builds what the script builds
#guard ((start swap).walk build).toOption.map (·.toRoot.script) == some swapScript
-- and the cursor is where the last rule was made
#guard ((start swap).walk build).toOption.map (·.addr) == some [0, 0, 1]

/--
info:    ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
    (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
>     p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR
        ? p0, p1, (p0 ∧ p1) ⊢ p1
        ? p0, p1, (p0 ∧ p1) ⊢ p0
  at 0.0: 2 premises; open goals: 2 under the focus, 0 left of it, 2 in all
-/
#guard_msgs in
#eval IO.println (shown (start swap) (build.take 5))

/-! ## Prune, and build again another way

`distr` is `(p ∧ (q ∨ r)) → ((p ∧ q) ∨ (p ∧ r))`.  After `orL` its first
branch is tried with the wrong disjunct, which leaves a goal that cannot be
closed; the branch is pruned and built again with the right one. -/

/-- To the first branch of `orL`, and the wrong disjunct there. -/
def wrong : List (Cmd IPC) :=
  [.rule .impR, .motion (.down 0), .rule (.andL p (q ⋎ r)), .motion (.down 0), .rule (.orL q r),
   .motion (.down 0), .rule .orR2, .motion (.down 0), .rule .andR]

-- the wrong way leaves `r` (`p2`) to be shown where `q` (`p1`) is assumed
#guard ((start distr).walk wrong).toOption.map (·.toRoot.goals.map Seq.show) ==
  some ["p1, p0, (p1 ∨ p2), (p0 ∧ (p1 ∨ p2)) ⊢ p0", "p1, p0, (p1 ∨ p2), (p0 ∧ (p1 ∨ p2)) ⊢ p2",
        "p2, p0, (p1 ∨ p2), (p0 ∧ (p1 ∨ p2)) ⊢ ((p0 ∧ p1) ∨ (p0 ∧ p2))"]

/-- Back up to the branch, prune it, and the right disjunct. -/
def again : List (Cmd IPC) :=
  [.motion .up, .prune, .rule .orR1, .motion (.down 0), .rule .andR, .motion (.down 0), .rule .ax,
   .motion .right, .rule .ax]

-- pruning the branch gives its goal back, in its place (E1)
#guard ((start distr).walk (wrong ++ [.motion .up, .prune])).toOption.map
    (·.toRoot.goals.map Seq.show) ==
  some ["p1, p0, (p1 ∨ p2), (p0 ∧ (p1 ∨ p2)) ⊢ ((p0 ∧ p1) ∨ (p0 ∧ p2))",
        "p2, p0, (p1 ∨ p2), (p0 ∧ (p1 ∨ p2)) ⊢ ((p0 ∧ p1) ∨ (p0 ∧ p2))"]
-- prune undoes a rule (`Cursor.prune_rule`), here by running
#guard ((start distr).walk (wrong ++ [.prune])).toOption.map (·.toRoot.script) ==
  ((start distr).walk (wrong.take 8)).toOption.map (·.toRoot.script)

/-- The other branch of `orL`: to the open goal left, and a script there. -/
def other : List (Cmd IPC) :=
  [.motion (.goal 0), .script [⟨0, .orR2⟩, ⟨0, .andR⟩, ⟨0, .ax⟩, ⟨0, .ax⟩]]

#guard ((start distr).walk (wrong ++ again ++ other)).toOption.map (·.toRoot.goals) == some []
-- the session with its retreat reaches the derivation the script builds
#guard ((start distr).walk (wrong ++ again ++ other)).toOption.map (·.toRoot.script) ==
  some distrScript
-- so its result is checked as any derivation is: by its script, in the kernel
example : derives IPC distr distrScript = true := by decide +kernel

/-! ## A script at the focus

Its goals are numbered within the focus.  At the root of the whole attempt
it is the script shifted by the goals left of the focus
(`Cursor.toRoot_script`, PROVED), here by running. -/

/-- At the second premise of `andR`, with the first still open. -/
def atSecond : List (Cmd IPC) :=
  [.rule .impR, .motion (.down 0), .rule (.andL p q), .motion (.down 0), .rule .andR,
   .motion (.down 1)]

#guard ((start swap).walk atSecond).toOption.map (fun c => (c.addr, c.left)) == some ([0, 0, 1], 1)
-- goal 0 of the script is goal 1 of the attempt
#guard ((start swap).walk (atSecond ++ [.script [⟨0, .ax⟩]])).toOption.map (·.toRoot.script) ==
  some (swapScript.take 3 ++ [⟨1, .ax⟩])
#guard ((start swap).walk (atSecond ++ [.script [⟨0, .ax⟩]])).toOption.map (·.toRoot.script) ==
  ((start swap).walk atSecond).toOption.map fun c =>
    (c.toRoot.run (Script.shift c.left [⟨0, .ax⟩])).att.script
-- a script on a focus that is a node: on its open goals
#guard ((start swap).walk (build.take 5 ++ [.script [⟨1, .ax⟩, ⟨0, .ax⟩]])).toOption.map
  (·.toRoot.goals) == some []

/-! ## Every way a command can fail

The number is the command's, from 0; the attempt is as it was. -/

#guard shown (start swap) [.rule .andR] == "command 0 fails: the conclusion is not a conjunction"
#guard shown (start swap) [.rule .impR, .rule .impR] == "command 1 fails: the focus is not an open goal"
#guard shown (start swap) [.rule .impR, .motion (.down 1)] ==
  "command 1 fails: the focus has no premise 1: its premises are numbered 0 to 0"
#guard shown (start swap) [.rule .impR, .motion (.goal 3)] == "command 1 fails: there is no goal 3"
#guard shown (start swap) [.motion .up] == "command 0 fails: the focus is the root"
#guard shown (start swap) [.script [⟨0, .impR⟩, ⟨0, .impR⟩]] ==
  "command 0 fails: line 1 of the script: the move does not apply to goal 0: " ++
    "the conclusion is not an implication"
#guard shown (start swap) [.script [⟨0, .impR⟩, ⟨1, .ax⟩]] ==
  "command 0 fails: line 1 of the script: there is no goal 1"
-- `prune` never fails; at an open goal it changes nothing
#guard ((start swap).walk [.prune]).toOption.map (·.toRoot.script) == some []

-- the functions behind the commands: a graft at an open goal, none at a node
#guard ((start swap).graft (run IPC swap swapScript).att).toOption.map (·.toRoot.goals) == some []
#guard (((start swap).replace (run IPC swap [⟨0, .impR⟩]).att).graft .goal).toOption.isNone
#guard ((start swap).rule .impR).toOption.map (·.prune.toRoot.script) == some []

/-! ## The count stays right through a session (`Cursor.walk_ok`)

After changes `goal k` still finds open goal `k`: the count of the goals
left of the focus is kept, not computed again. -/

#guard ((start swap).walk (build.take 5 ++ [.motion (.goal 1), .rule .ax, .motion (.goal 0)])).toOption.map
  (fun c => (c.addr, c.left, c.toRoot.goals.length)) == some ([0, 0, 0], 0, 1)

/-! ## A session of motions only (S2)

It is the motions in turn (`Cursor.walk_motions`, PROVED), and leaves the
attempt as it was (`Cursor.walk_motions_ok`, PROVED). -/

#guard ((start swap).walk (build.take 5 ++ [.motion (.down 1), .motion .left, .motion .up, .motion .top])).toOption.map
    (·.toRoot.script) ==
  ((start swap).walk (build.take 5)).toOption.map (·.toRoot.script)

/-! ## A script is a session (S1)

`Script.cmds ls`: to each line's goal, then its move there.  On every
script of length at most 3 over the alphabet of `Count.lean`: the session
succeeds exactly when no line of the run fails, and then reaches the same
attempt (`Att.walk_cmds`, `Att.run_of_walk_cmds`, PROVED). -/

section Count

open Count

/-- Do the session of a script and its run agree? -/
def agree (j : Nat) (ls : Script Count) : Bool :=
  let a := run Count j ls
  match (Cursor.ofRoot (.goal : Att Count true j)).walk (Script.cmds ls) with
  | .ok c => a.failed.isNone && c.toRoot.script == a.att.script && c.toRoot.goals == a.att.goals
  | .error _ => a.failed.isSome

#guard (scripts 3).length == 1885
#guard (scripts 3).all (agree 2)
#guard (scripts 3).all (agree 3)
-- of them, these succeed
#guard ((scripts 3).filter fun s =>
  ((Cursor.ofRoot (.goal : Att Count true 3)).walk (Script.cmds s)).toOption.isSome).length == 47
#guard ((scripts 3).filter fun s => (run Count 3 s).failed.isNone).length == 47

/-! ## In the kernel -/

/-- A chain `n` deep, built by a session that goes down after each rule. -/
def chainCmds (n : Nat) : List (Cmd Count) :=
  (List.replicate n [(.rule (CMove.split 1) : Cmd Count), .motion (.down 0)]).flatten ++
    [.rule CMove.done]

example : ((Cursor.ofRoot (.goal : Att Count true 200)).walk (chainCmds 200)).toOption.map
    (·.toRoot.goals) = some [] := by
  decide +kernel

end Count

/-! ## The statements, pinned -/

section Statements

variable {S : ProofSystem} {j : S.Judg}

/-- E1. -/
example (c : Cursor S j) (d : Att S true c.pos.i) :
    (c.replace d).toRoot.goals =
      Path.goalsL c.pos.z.path ++ d.goals ++ Path.goalsR c.pos.z.path :=
  Cursor.goals_replace c d

/-- S1. -/
example (d : Att S true j) (ls : Script S) (h : (d.run ls).failed = none) :
    ∃ c, (Cursor.ofRoot d).walk (Script.cmds ls) = .ok c ∧ c.toRoot = (d.run ls).att :=
  Att.walk_cmds d ls h

/-- S1 at a judgment: `run S j ls` is `Att.run .goal ls`. -/
example (ls : Script S) (h : (run S j ls).failed = none) :
    ∃ c, (Cursor.ofRoot (.goal : Att S true j)).walk (Script.cmds ls) = .ok c ∧
      c.toRoot = (run S j ls).att :=
  Att.walk_cmds .goal ls h

/-- S1, the converse. -/
example (d : Att S true j) (ls : Script S) {c : Cursor S j}
    (h : (Cursor.ofRoot d).walk (Script.cmds ls) = .ok c) : d.run ls = { att := c.toRoot } :=
  Att.run_of_walk_cmds d ls h

/-- S2. -/
example {ms : List Motion} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.walk (ms.map Cmd.motion) = .ok c') : c'.toRoot = c.toRoot ∧ c'.Ok :=
  Cursor.walk_motions_ok hc h

example {m : S.Move} {c c' : Cursor S j} (hc : c.Ok) (h : c.rule m = .ok c') :
    c.toRoot.step ⟨c.left, m⟩ = .ok c'.toRoot :=
  Cursor.toRoot_rule hc h

example {ls : Script S} {c c' : Cursor S j} (hc : c.Ok) (h : c.script ls = .ok c') :
    c.toRoot.run (ls.shift c.left) = { att := c'.toRoot } :=
  Cursor.toRoot_script hc h

example {m : S.Move} {c c' : Cursor S j} (h : c.rule m = .ok c') : c'.prune = c :=
  Cursor.prune_rule h

end Statements

end ProofToolsTest.Explore.SessionTest

/-! ## Axioms -/

open ProofTools ProofTools.Explore in
#axioms_within Cursor.goals_replace [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Cursor.toRoot_rule [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Cursor.toRoot_script [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Cursor.walk [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Cursor.walk_ok [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Cursor.walk_motions_ok [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Att.walk_cmds [propext, Quot.sound]
open ProofTools ProofTools.Explore in
#axioms_within Att.run_of_walk_cmds [propext, Quot.sound]
