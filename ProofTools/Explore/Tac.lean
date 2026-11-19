/-
# `ProofTools.Explore.Tac`: scripts as programs

A **tactic of a calculus** is a function from a judgment to a script for
it, or `none`.  It is a total function in the logic, so it can be given
theorems; and a script it returns is checked like any other, so a wrong
tactic costs a failure, never a wrong derivation.

    Script.shift k ls     the same script at goal `k` of a larger attempt
    Tac.move m            the one move `m`, where it applies
    Tac.orElse t u        `t`, or `u` where `t` gives nothing
    Tac.andThen t u       `t`, then `u` at every goal `t` leaves
    Tac.iterate n t       `t` at every goal it leaves, at most `n` deep

`andThen` gives nothing if the script of `t` does not run, or `u` gives
nothing at one of the goals.  `iterate` always gives a script: where `t`
gives nothing, the goal is left open.

What is PROVED.  A script that runs on `d` runs, shifted, wherever `d`
sits (`p` a path with `d` at its hole):

    (d.runFrom n' ls).failed = none →
      (p.plug d).runFrom n (ls.shift (goalsL p).length ++ rest) =
        (p.plug (d.runFrom n' ls).att).runFrom (n + ls.length) rest      (Att.runFrom_shift)

A tactic is *valid* if every script it gives runs without a failing line
(`Tac.Valid`).  Then

    (Tac.move m).Valid                                  (Tac.valid_move)
    t.Valid → u.Valid → (t.orElse u).Valid              (Tac.valid_orElse)
    (t.andThen u).Valid          for every t and u      (Tac.valid_andThen)
    (Tac.iterate n t).Valid      for every t            (Tac.valid_iterate)

`andThen` and `iterate` need no hypothesis, because they run each script
before they use it.  So a tactic built from moves with these combinators
never gives a script that fails; whether the script closes its goal is for
`derives` to say.

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Explore.Run

namespace ProofTools.Explore

variable {S : ProofSystem}

/-- **The same script at goal `k` of a larger attempt**: every goal number
moved up by `k`. -/
def Script.shift (k : Nat) (ls : Script S) : Script S :=
  ls.map fun l => { l with goal := k + l.goal }

/-- **A tactic of the calculus**: a script for a judgment, or nothing. -/
abbrev Tac (S : ProofSystem) : Type := S.Judg → Option (Script S)

/-- The tactic that does nothing, and leaves its goal open. -/
def Tac.skip : Tac S := fun _ => some []

/-- The one move `m`, where it applies. -/
def Tac.move (m : S.Move) : Tac S := fun j =>
  match S.step m j with
  | .ok _ => some [⟨0, m⟩]
  | .error _ => none

/-- `t`, or `u` where `t` gives nothing. -/
def Tac.orElse (t u : Tac S) : Tac S := fun j =>
  match t j with
  | some ls => some ls
  | none => u j

/-- `u` at each goal of a list, from the left.  `k` is the number, in the
attempt being built, of the first goal of the list; each script is shifted
to its goal's number, and the next goal's number counts what the script
leaves open. -/
def Tac.atGoals (u : Tac S) : List S.Judg → Nat → Option (Script S)
  | [], _ => some []
  | g :: gs, k =>
    match u g with
    | none => none
    | some ls =>
      let r := run S g ls
      if r.failed.isNone then
        match Tac.atGoals u gs (k + r.att.goals.length) with
        | none => none
        | some rest => some (ls.shift k ++ rest)
      else none

/-- **`t`, then `u` at every goal `t` leaves.** -/
def Tac.andThen (t u : Tac S) : Tac S := fun j =>
  match t j with
  | none => none
  | some ls =>
    let r := run S j ls
    if r.failed.isNone then (Tac.atGoals u r.att.goals 0).map (ls ++ ·) else none

/-- **`t` at every goal it leaves, at most `n` deep.**  Where `t` gives
nothing the goal is left open. -/
def Tac.iterate : Nat → Tac S → Tac S
  | 0, _ => Tac.skip
  | n + 1, t => (t.andThen (Tac.iterate n t)).orElse Tac.skip

/-- The first of a list of tactics that gives a script. -/
def Tac.first : List (Tac S) → Tac S
  | [] => fun _ => none
  | t :: ts => t.orElse (Tac.first ts)

/-! ## What the combinators guarantee -/

open ProofTools

theorem Att.step_eq_ok {j : S.Judg} {d d' : Att S true j} {l : Line S} (h : d.step l = .ok d') :
    d.moveAt l.move l.goal = .inl (.ok d') := by
  unfold Att.step at h
  split at h
  · next d'' hm =>
    rw [hm, Except.ok.inj h]
  · cases h
  · cases h

/-- **A script that runs on `d` runs, shifted, wherever `d` sits**: at the
hole of a path with `k` goals to its left, the script shifted by `k` does to
the whole attempt what the script does to `d`. -/
theorem Att.stepsFrom_shift {i t : S.Judg} {ds : List Nat} (p : Path S true ds i t) :
    (ls : Script S) → (n n' : Nat) → (d : Att S true i) → (rest : Script S) →
    (Att.stepsFrom n' d ls).failed = none →
      Att.stepsFrom n (Zip.Deriv.Path.plug p d) (ls.shift (Path.goalsL p).length ++ rest) =
        Att.stepsFrom (n + ls.length) (Zip.Deriv.Path.plug p (Att.stepsFrom n' d ls).att) rest
  | [], _, _, _, _, _ => rfl
  | l :: ls, n, n', d, rest, h => by
    simp only [Att.stepsFrom] at h
    cases hs : d.step l with
    | error e =>
      rw [hs] at h
      simp at h
    | ok d' =>
      rw [hs] at h
      have hm := Path.moveAt_plug l.move p d l.goal (Att.step_eq_ok hs)
      have hstep : (Zip.Deriv.Path.plug p d).step ⟨(Path.goalsL p).length + l.goal, l.move⟩ =
          .ok (Zip.Deriv.Path.plug p d') := by
        simp only [Att.step, hm]
        rfl
      have ih := Att.stepsFrom_shift p ls (n + 1) (n' + 1) d' rest h
      simp only [Script.shift, List.map_cons, List.cons_append, Att.stepsFrom, hstep, hs,
        List.length_cons]
      rw [show n + (ls.length + 1) = n + 1 + ls.length by omega]
      exact ih

/-- `Att.stepsFrom_shift`, for `run`. -/
theorem Att.runFrom_shift {i t : S.Judg} {ds : List Nat} (p : Path S true ds i t)
    (ls : Script S) (n n' : Nat) (d : Att S true i) (rest : Script S)
    (h : (d.runFrom n' ls).failed = none) :
    (Zip.Deriv.Path.plug p d).runFrom n (ls.shift (Path.goalsL p).length ++ rest) =
      (Zip.Deriv.Path.plug p (d.runFrom n' ls).att).runFrom (n + ls.length) rest := by
  simp only [Att.runFrom_eq_stepsFrom] at h ⊢
  exact Att.stepsFrom_shift p ls n n' d rest h

/-- **A tactic is valid** if every script it gives runs without a failing
line. -/
def Tac.Valid (t : Tac S) : Prop := ∀ j ls, t j = some ls → (run S j ls).failed = none

theorem Tac.valid_skip : (Tac.skip : Tac S).Valid := by
  intro j ls h
  simp only [Tac.skip, Option.some.injEq] at h
  subst h
  rfl

theorem Tac.valid_move (m : S.Move) : (Tac.move m).Valid := by
  intro j ls h
  unfold Tac.move at h
  split at h
  · next ps hs =>
    simp only [Option.some.injEq] at h
    subst h
    show (Att.run .goal [⟨0, m⟩]).failed = none
    rw [Att.run_eq_runBySteps]
    have hstep : (Att.goal : Att S true j).step ⟨0, m⟩ = .ok (.node m ps hs (Atts.open ps)) := by
      simp only [Att.step, Att.moveAt, Att.ofMove_ok hs]
    simp only [Att.runBySteps, Att.stepsFrom, hstep]
  · cases h

theorem Tac.valid_orElse {t u : Tac S} (ht : t.Valid) (hu : u.Valid) : (t.orElse u).Valid := by
  intro j ls h
  unfold Tac.orElse at h
  split at h
  · next ls' hl =>
    simp only [Option.some.injEq] at h
    subst h
    exact ht j _ hl
  · exact hu j ls h

/-- The open goal `k` of an attempt, as the hole of a path. -/
theorem Att.exists_path_goal {j : S.Judg} (e : Att S true j) (pre gs : List S.Judg) (g : S.Judg)
    (hg : e.goals = pre ++ g :: gs) :
    ∃ (ds : List Nat) (p : Path S true ds g j), Zip.Deriv.Path.plug p .goal = e ∧
      Path.goalsL p = pre ∧ Path.goalsR p = gs := by
  have hlt : ¬ e.goals.length ≤ pre.length := by
    rw [hg]
    simp only [List.length_append, List.length_cons]
    omega
  cases hs : (Cursor.ofRoot e).seek pre.length with
  | none => exact absurd (Cursor.seek_none (Cursor.ok_ofRoot e) hs) hlt
  | some c =>
    obtain ⟨r₁, r₂, r₃, r₄⟩ := Cursor.seek_some (Cursor.ok_ofRoot e) hs
    obtain ⟨⟨ds, i, ⟨f, path⟩⟩, lft⟩ := c
    simp only at r₂ r₃
    subst r₂ r₃
    have hroot : Zip.Deriv.Path.plug path (.goal : Att S true i) = e := r₁
    have hlen : pre.length = (Path.goalsL path).length := r₄
    have hgoals := Path.goals_plug path (.goal : Att S true i)
    rw [hroot, hg] at hgoals
    simp only [Att.goals_goal, List.append_assoc, List.singleton_append] at hgoals
    obtain ⟨h₁, h₂⟩ := List.append_inj hgoals hlen
    obtain ⟨h₃, h₄⟩ := List.cons.inj h₂
    subst h₃
    exact ⟨ds, path, hroot, h₁.symm, h₄.symm⟩

/-- The script `atGoals` gives runs, on any attempt whose open goals from
number `k` on are the list. -/
theorem Tac.atGoals_runs (u : Tac S) {j : S.Judg} : (gs : List S.Judg) → (pre : List S.Judg) →
    (e : Att S true j) → (n : Nat) → (rest : Script S) → e.goals = pre ++ gs →
    Tac.atGoals u gs pre.length = some rest → (e.runFrom n rest).failed = none
  | [], _, e, n, rest, _, h => by
    simp only [Tac.atGoals, Option.some.injEq] at h
    subst h
    rfl
  | g :: gs, pre, e, n, rest, hg, h => by
    unfold Tac.atGoals at h
    split at h
    · cases h
    · next ls hl =>
      simp only at h
      split at h
      · next hrun =>
        split at h
        · cases h
        · next rest' hrest =>
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨ds, p, hp, hL, hR⟩ := Att.exists_path_goal e pre gs g hg
          have hfail : ((.goal : Att S true g).runFrom 0 ls).failed = none :=
            Option.isNone_iff_eq_none.mp hrun
          have key := Att.runFrom_shift p ls n 0 .goal rest' hfail
          rw [hp, hL] at key
          rw [key]
          refine Tac.atGoals_runs u gs (pre ++ (run S g ls).att.goals) _ _ rest' ?_ ?_
          · show (Zip.Deriv.Path.plug p (run S g ls).att).goals = _
            rw [Path.goals_plug, hL, hR]
          · rw [List.length_append]
            exact hrest
      · cases h

/-- **`andThen` gives only scripts that run**, whatever its tactics are: it
runs each script before it uses it. -/
theorem Tac.valid_andThen (t u : Tac S) : (t.andThen u).Valid := by
  intro j ls h
  unfold Tac.andThen at h
  split at h
  · cases h
  · next ls₀ hl =>
    simp only at h
    split at h
    · next hrun =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      have hfail : ((.goal : Att S true j).runFrom 0 ls₀).failed = none :=
        Option.isNone_iff_eq_none.mp hrun
      show ((.goal : Att S true j).runFrom 0 (ls₀ ++ rest)).failed = none
      rw [Att.runFrom_append 0 .goal ls₀ rest hfail]
      exact Tac.atGoals_runs u _ [] _ _ rest rfl hrest
    · cases h

/-- **`iterate` gives only scripts that run**, whatever its tactic is. -/
theorem Tac.valid_iterate (t : Tac S) : (n : Nat) → (Tac.iterate n t).Valid
  | 0 => Tac.valid_skip
  | n + 1 => Tac.valid_orElse (Tac.valid_andThen t (Tac.iterate n t)) Tac.valid_skip

theorem Tac.valid_first : (ts : List (Tac S)) → (∀ t ∈ ts, t.Valid) → (Tac.first ts).Valid
  | [], _ => by
    intro j ls h
    cases h
  | t :: ts, h =>
    Tac.valid_orElse (h t (by simp)) (Tac.valid_first ts fun u hu => h u (by simp [hu]))

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.  `Classical.choice` comes
-- with the theorems of `Cursor` and `Run`.
#axioms_within_file [propext, Classical.choice, Quot.sound]
