/-
# `ProofTools.Explore.Run`: what `run` does

`run` keeps a zipper from line to line (`ProofTools.Explore.Cursor`).  Its
specification is the run by steps from the root
(`ProofTools.Explore.Script`).  PROVED here, for every proof system:

    d.run ls = d.runBySteps ls                                       (Att.run_eq_runBySteps)

so `run` gives the attempt, the failing line and the message that the
specification gives.  A script read back from an attempt rebuilds it:

    run S j d.script = { att := d.toAtt }        for d : Att S o j   (run_script)
    run S j d.script = { att := d }              for d : Att S true j (run_script_att)

and a script can be run in two parts, the second numbered after the first:

    (d.runFrom n ls).failed = none →
      d.runFrom n (ls ++ ls') = (d.runFrom n ls).att.runFrom (n + ls.length) ls'
                                                                     (Att.runFrom_append)

The step that joins the cursor to the specification is

    w.moveAt m n = .inl r →
      (p.plug w).moveAt m ((goalsL p).length + n) = .inl (r.map p.plug)   (Path.moveAt_plug)

a move inside the filling of a path is the move in the whole attempt, at
the goal number shifted by the goals left of the hole.

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Explore.Cursor

namespace ProofTools.Explore

open ProofTools

variable {S : ProofSystem}

/-! ## A move under a context -/

private theorem Except.map_id' {ε α : Type} (r : Except ε α) : r.map (fun x => x) = r := by
  cases r <;> rfl

private theorem Except.map_map' {ε α β γ : Type} (f : α → β) (g : β → γ) (r : Except ε α) :
    (r.map f).map g = r.map (fun x => g (f x)) := by
  cases r <;> rfl

/-- Carry an answer of `moveAt` out through a context `f` with `k` open
goals to its left. -/
def liftAt {α β : Type} (f : α → β) (k : Nat) : Except String α ⊕ Nat → Except String β ⊕ Nat
  | .inl r => .inl (r.map f)
  | .inr c => .inr (k + c)

theorem Atts.moveAt_revAppend (m : S.Move) : {o : Bool} → {ls rs : List S.Judg} →
    (l : Atts S o ls) → (rest : Atts S o rs) → (n : Nat) →
    (l.revAppend rest).moveAt m (l.goalsRev.length + n) =
      liftAt (fun x => l.revAppend x) l.goalsRev.length (rest.moveAt m n)
  | _, _, _, .nil, rest, n => by
    show rest.moveAt m (0 + n) = liftAt (fun x => x) 0 (rest.moveAt m n)
    rw [Nat.zero_add]
    cases rest.moveAt m n with
    | inl r => simp only [liftAt, Except.map_id']
    | inr c => simp only [liftAt, Nat.zero_add]
  | _, p :: ls, rs, .cons e l, rest, n => by
    have ih := Atts.moveAt_revAppend m (ls := ls) (rs := p :: rs) l (.cons e rest)
      (e.goals.length + n)
    have hidx : (Atts.cons e l).goalsRev.length + n = l.goalsRev.length + (e.goals.length + n) := by
      simp only [Atts.goalsRev_cons, List.length_append]
      omega
    have hcons : (Atts.cons e rest).moveAt m (e.goals.length + n) =
        liftAt (Atts.cons e) e.goals.length (rest.moveAt m n) := by
      simp only [Atts.moveAt, Att.moveAt_of_le m e (e.goals.length + n) (by omega),
        Nat.add_sub_cancel_left]
      cases rest.moveAt m n <;> rfl
    show (l.revAppend (.cons e rest)).moveAt m _ = _
    rw [hidx, ih, hcons]
    cases rest.moveAt m n with
    | inl r =>
      simp only [liftAt, Except.map_map']
      rfl
    | inr c =>
      simp only [liftAt, Atts.goalsRev_cons, List.length_append, Nat.add_assoc]
      rfl

/-- A move inside the filling of a crumb is the move in the node. -/
theorem Crumb.moveAt_plug {o : Bool} {d : Nat} {p j : S.Judg} (c : Crumb S o d p j)
    (w : Att S o p) (m : S.Move) (n : Nat) {r : Except String (Att S o p)}
    (hw : w.moveAt m n = .inl r) :
    (c.plug w).moveAt m (c.left.goalsRev.length + n) = .inl (r.map c.plug) := by
  have hcons : (Atts.cons w c.right).moveAt m n = .inl (r.map (Atts.cons · c.right)) := by
    simp only [Atts.moveAt, hw]
  simp only [Crumb.plug, Att.moveAt, Atts.moveAt_revAppend, hcons, liftAt, Except.map_map']
  rfl

/-- **A move inside the filling of a path is the move in the whole
attempt**, at the goal number shifted by the goals left of the hole. -/
theorem Path.moveAt_plug {o : Bool} (m : S.Move) : {ds : List Nat} → {i k : S.Judg} →
    (p : Path S o ds i k) → (w : Att S o i) → (n : Nat) → {r : Except String (Att S o i)} →
    w.moveAt m n = .inl r →
      (Zip.Deriv.Path.plug p w).moveAt m ((Path.goalsL p).length + n) =
        .inl (r.map (Zip.Deriv.Path.plug p))
  | _, _, _, .top, w, n, r, hw => by
    simp only [Zip.Deriv.Path.plug_top, Path.goalsL, List.length_nil, Nat.zero_add, hw]
    exact congrArg Sum.inl (Except.map_id' r).symm
  | _, _, _, .cons c p, w, n, r, hw => by
    have h₁ := Crumb.moveAt_plug c w m n hw
    have ih := Path.moveAt_plug m p (c.plug w) (c.left.goalsRev.length + n) h₁
    have hidx : (Path.goalsL (Zip.Deriv.Path.cons c p)).length + n =
        (Path.goalsL p).length + (c.left.goalsRev.length + n) := by
      simp only [Path.goalsL, List.length_append]
      omega
    show (Zip.Deriv.Path.plug p (c.plug w)).moveAt m _ = _
    rw [hidx, ih, Except.map_map']
    rfl

/-! ## `run` is the run by steps -/

/-- **One line of the cursor is one step from the root.** -/
theorem Cursor.step_toRoot {j : S.Judg} {c : Cursor S j} (hc : c.Ok) (l : Line S) :
    c.toRoot.step l = (c.step l).map Cursor.toRoot := by
  unfold Cursor.step
  cases hs : c.seek l.goal with
  | none =>
    have hle := Cursor.seek_none hc hs
    simp only [Att.step, Att.moveAt_of_le l.move c.toRoot l.goal hle]
    rfl
  | some c' =>
    obtain ⟨r₁, r₂, r₃, r₄⟩ := Cursor.seek_some hc hs
    obtain ⟨⟨ds, i, ⟨f, path⟩⟩, lft⟩ := c'
    simp only at r₂ r₃
    subst r₂ r₃
    have hroot : c.toRoot = Zip.Deriv.Path.plug path .goal := r₁.symm
    have hmv := Path.moveAt_plug l.move path .goal 0 (r := Att.ofMove l.move i) rfl
    have hk : (Path.goalsL path).length + 0 = l.goal := r₄.symm
    rw [hk] at hmv
    simp only [Att.step, hroot, hmv]
    cases Att.ofMove l.move i <;> rfl

/-- A line keeps the cursor's count right. -/
theorem Cursor.step_ok {j : S.Judg} {c c' : Cursor S j} (hc : c.Ok) {l : Line S}
    (h : c.step l = .ok c') : c'.Ok := by
  unfold Cursor.step at h
  split at h
  · cases h
  · next c₁ hs =>
    obtain ⟨-, -, -, r₄⟩ := Cursor.seek_some hc hs
    split at h
    · next nd hnd =>
      simp only [Except.ok.injEq] at h
      subst h
      exact Cursor.ok_replace r₄ nd
    · cases h

theorem Cursor.runFrom_eq_stepsFrom {j : S.Judg} : (ls : Script S) → (n : Nat) →
    (c : Cursor S j) → c.Ok → Cursor.runFrom n c ls = Att.stepsFrom n c.toRoot ls
  | [], _, _, _ => rfl
  | l :: ls, n, c, hc => by
    simp only [Cursor.runFrom, Att.stepsFrom, Cursor.step_toRoot hc l]
    cases hs : c.step l with
    | ok c' => exact Cursor.runFrom_eq_stepsFrom ls (n + 1) c' (Cursor.step_ok hc hs)
    | error e => rfl

theorem Att.runFrom_eq_stepsFrom {j : S.Judg} (n : Nat) (d : Att S true j) (ls : Script S) :
    d.runFrom n ls = Att.stepsFrom n d ls :=
  Cursor.runFrom_eq_stepsFrom ls n (.ofRoot d) (Cursor.ok_ofRoot d)

/-- **`run` is the run by steps from the root**: the same attempt, the same
failing line, the same message. -/
theorem Att.run_eq_runBySteps {j : S.Judg} (d : Att S true j) (ls : Script S) :
    d.run ls = d.runBySteps ls :=
  Att.runFrom_eq_stepsFrom 0 d ls

/-! ## A script read back rebuilds its attempt -/

theorem Att.step_plug_goal {m : S.Move} {i t : S.Judg} {ps : List S.Judg}
    (hs : S.step m i = .ok ps) {ds : List Nat} (p : Path S true ds i t) :
    (Zip.Deriv.Path.plug p .goal).step ⟨(Path.goalsL p).length, m⟩ =
      .ok (Zip.Deriv.Path.plug p (.node m ps hs (Atts.open ps))) := by
  have hmv := Path.moveAt_plug m p .goal 0 (r := Att.ofMove m i) rfl
  rw [Nat.add_zero, Att.ofMove_ok hs] at hmv
  simp only [Att.step, hmv]
  rfl

mutual
theorem Att.stepsFrom_scriptAt {t : S.Judg} : {o : Bool} → {i : S.Judg} → (d : Att S o i) →
    {ds : List Nat} → (p : Path S true ds i t) → (n : Nat) → (rest : Script S) →
    Att.stepsFrom n (Zip.Deriv.Path.plug p .goal) (d.scriptAt (Path.goalsL p).length ++ rest) =
      Att.stepsFrom (n + d.size) (Zip.Deriv.Path.plug p d.toAtt) rest
  | _, _, .goal, _, _, _, _ => rfl
  | _, _, .node m ps hs cs, _, p, n, rest => by
    have ih := Atts.stepsFrom_scriptAt m (lsr := []) hs .nil cs p (n + 1) rest
    simp only [Atts.goalsRev_nil, List.length_nil, Nat.add_zero] at ih
    simp only [Att.scriptAt, List.cons_append, Att.stepsFrom, Att.step_plug_goal hs p]
    rw [show n + (Att.node m ps hs cs).size = n + 1 + cs.size by simp only [Att.size]; omega]
    exact ih
theorem Atts.stepsFrom_scriptAt {t : S.Judg} (m : S.Move) {i : S.Judg} : {o : Bool} →
    {lsr rs : List S.Judg} → (h : S.step m i = .ok (lsr.reverseAux rs)) →
    (left : Atts S true lsr) → (cs : Atts S o rs) → {ds : List Nat} → (p : Path S true ds i t) →
    (n : Nat) → (rest : Script S) →
    Att.stepsFrom n (Zip.Deriv.Path.plug p (.node m _ h (left.revAppend (Atts.open rs))))
        (cs.scriptAt ((Path.goalsL p).length + left.goalsRev.length) ++ rest) =
      Att.stepsFrom (n + cs.size) (Zip.Deriv.Path.plug p (.node m _ h (left.revAppend cs.toAtts)))
        rest
  | _, _, _, _, _, .nil, _, _, _, _ => rfl
  | _, lsr, q :: rs, h, left, .cons d cs, _, p, n, rest => by
    have ih₁ := Att.stepsFrom_scriptAt d
      (.cons (d := lsr.length) ⟨m, lsr, rs, h, left, Atts.open rs, rfl⟩ p) n
      (cs.scriptAt ((Path.goalsL p).length + left.goalsRev.length + d.goals.length) ++ rest)
    have ih₂ := Atts.stepsFrom_scriptAt m (lsr := q :: lsr) (rs := rs) h (.cons d.toAtt left) cs p
      (n + d.size) rest
    simp only [Path.goalsL, List.length_append] at ih₁
    simp only [Atts.goalsRev_cons, List.length_append, Att.goals_toAtt, ← Nat.add_assoc] at ih₂
    simp only [Atts.scriptAt, List.append_assoc]
    rw [show n + (Atts.cons d cs).size = n + d.size + cs.size by simp only [Atts.size]; omega]
    exact ih₁.trans ih₂
end

/-- **A script read back from an attempt rebuilds it.** -/
theorem run_script {o : Bool} {j : S.Judg} (d : Att S o j) :
    run S j d.script = { att := d.toAtt } := by
  show Att.run .goal d.script = _
  rw [Att.run_eq_runBySteps]
  have h := Att.stepsFrom_scriptAt d (Zip.Deriv.Path.top : Path S true [] j j) 0 []
  simp only [List.append_nil] at h
  exact h

/-- `run_script`, for an attempt. -/
theorem run_script_att {j : S.Judg} (d : Att S true j) : run S j d.script = { att := d } := by
  rw [run_script, Att.toAtt_eq]

/-! ## Running a script in two parts -/

theorem Att.stepsFrom_append {j : S.Judg} : (ls : Script S) → (n : Nat) → (d : Att S true j) →
    (ls' : Script S) → (Att.stepsFrom n d ls).failed = none →
      Att.stepsFrom n d (ls ++ ls') =
        Att.stepsFrom (n + ls.length) (Att.stepsFrom n d ls).att ls'
  | [], _, _, _, _ => rfl
  | l :: ls, n, d, ls', h => by
    simp only [Att.stepsFrom, List.cons_append] at h ⊢
    cases hs : d.step l with
    | ok d' =>
      rw [hs] at h
      simp only at h ⊢
      rw [Att.stepsFrom_append ls (n + 1) d' ls' h, List.length_cons,
        show n + (ls.length + 1) = n + 1 + ls.length by omega]
    | error e =>
      rw [hs] at h
      simp at h

/-- **A script run in two parts**: if the first part does not fail, running
the whole is running the second part on what the first leaves, its lines
numbered after the first's. -/
theorem Att.runFrom_append {j : S.Judg} (n : Nat) (d : Att S true j) (ls ls' : Script S)
    (h : (d.runFrom n ls).failed = none) :
    d.runFrom n (ls ++ ls') = (d.runFrom n ls).att.runFrom (n + ls.length) ls' := by
  simp only [Att.runFrom_eq_stepsFrom] at h ⊢
  exact Att.stepsFrom_append ls n d ls' h

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
