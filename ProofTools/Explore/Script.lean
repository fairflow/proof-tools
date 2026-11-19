/-
# `ProofTools.Explore.Script`: scripts, and one move from the root

A **script** is a list of lines; a line names an open goal by its number,
counted from the left over the whole attempt, and a move to make there.

This file is the *specification* of running a script: `Att.step` makes one
move by a recursion over the whole attempt from its root, and
`Att.runBySteps` does that at every line.  `ProofTools.Explore.Cursor` has
the `run` that is used, which keeps a zipper from line to line, and
`ProofTools.Explore.Run` proves the two equal.

    d.moveAt m k   the move `m` at open goal `k` of `d`: the new attempt or
                   the move's error (`inl`), or, if `d` has no goal `k`, the
                   number of its open goals (`inr`)

What a step does, as statements about the open goals (PROVED):

    d.goals.length ≤ k → d.moveAt m k = .inr d.goals.length                 (Att.moveAt_of_le)
    d.moveAt m k = .inr c → c = d.goals.length ∧ c ≤ k                      (Att.moveAt_inr)
    d.moveAt m k = .inl (.ok d') → ∃ g ps, d.goals[k]? = some g ∧
        S.step m g = .ok ps ∧ d'.goals = d.goals.take k ++ ps ++ d.goals.drop (k + 1)
                                                                            (Att.moveAt_ok)
    d.moveAt m k = .inl (.error e) → ∃ g, d.goals[k]? = some g ∧ S.step m g = .error e
                                                                            (Att.moveAt_error)

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Explore.System

namespace ProofTools.Explore

variable {S : ProofSystem}

/-- **A line** of a script: a move at an open goal, numbered from the left. -/
structure Line (S : ProofSystem) where
  /-- The number of the goal. -/
  goal : Nat := 0
  /-- The move. -/
  move : S.Move

/-- **A script**: lines, made in order. -/
abbrev Script (S : ProofSystem) : Type := List (Line S)

instance [Repr S.Move] : Repr (Line S) where
  reprPrec l _ := "{ goal := " ++ repr l.goal ++ ", move := " ++ repr l.move ++ " }"

instance [BEq S.Move] : BEq (Line S) where
  beq a b := a.goal == b.goal && a.move == b.move

/-! ## A move at an open goal -/

/-- The node a move makes at `j`, from the result of `S.step`. -/
def Att.ofStep (m : S.Move) (j : S.Judg) :
    (r : Except String (List S.Judg)) → S.step m j = r → Except String (Att S true j)
  | .ok ps, h => .ok (.node m ps h (Atts.open ps))
  | .error e, _ => .error e

/-- **The move `m` at an open goal of `j`**: a node with every premise open,
or the reason the move does not apply. -/
def Att.ofMove (m : S.Move) (j : S.Judg) : Except String (Att S true j) :=
  Att.ofStep m j (S.step m j) rfl

theorem Att.ofStep_ok {m : S.Move} {j : S.Judg} {ps : List S.Judg} (h : S.step m j = .ok ps) :
    ∀ (r : Except String (List S.Judg)) (hr : S.step m j = r),
      Att.ofStep m j r hr = .ok (.node m ps h (Atts.open ps))
  | .ok ps', hr => by
    have e : ps' = ps := Except.ok.inj (hr.symm.trans h)
    subst e
    rfl
  | .error _, hr => by
    have e := hr.symm.trans h
    cases e

theorem Att.ofMove_ok {m : S.Move} {j : S.Judg} {ps : List S.Judg} (h : S.step m j = .ok ps) :
    Att.ofMove m j = .ok (.node m ps h (Atts.open ps)) :=
  Att.ofStep_ok h _ rfl

theorem Att.ofStep_error {m : S.Move} {j : S.Judg} {e : String} (h : S.step m j = .error e) :
    ∀ (r : Except String (List S.Judg)) (hr : S.step m j = r), Att.ofStep m j r hr = .error e
  | .ok _, hr => by
    have e' := hr.symm.trans h
    cases e'
  | .error e', hr => by
    have e'' : e' = e := Except.error.inj (hr.symm.trans h)
    subst e''
    rfl

theorem Att.ofMove_error {m : S.Move} {j : S.Judg} {e : String} (h : S.step m j = .error e) :
    Att.ofMove m j = .error e :=
  Att.ofStep_error h _ rfl

/-- What `ofMove` answers, read back. -/
theorem Att.ofMove_eq_ok {m : S.Move} {j : S.Judg} {d : Att S true j}
    (h : Att.ofMove m j = .ok d) :
    ∃ (ps : List S.Judg) (hs : S.step m j = .ok ps), d = .node m ps hs (Atts.open ps) := by
  have key : ∀ r, S.step m j = r →
      ∃ (ps : List S.Judg) (hs : S.step m j = .ok ps), d = .node m ps hs (Atts.open ps) := by
    intro r hs
    cases r with
    | ok ps =>
      rw [Att.ofMove_ok hs] at h
      exact ⟨ps, hs, (Except.ok.inj h).symm⟩
    | error e =>
      rw [Att.ofMove_error hs] at h
      cases h
  exact key _ rfl

theorem Att.ofMove_eq_error {m : S.Move} {j : S.Judg} {e : String}
    (h : Att.ofMove (S := S) m j = .error e) : S.step m j = .error e := by
  have key : ∀ r, S.step m j = r → S.step m j = .error e := by
    intro r hs
    cases r with
    | ok ps =>
      rw [Att.ofMove_ok hs] at h
      cases h
    | error e' =>
      rw [Att.ofMove_error hs] at h
      rw [hs, Except.error.inj h]
  exact key _ rfl

/-! ## One move, from the root -/

mutual
/-- **The move `m` at open goal `k` of `d`**, the goals counted from the
left: the new attempt or the move's error (`inl`), or, if `d` has no goal
`k`, the number of its open goals (`inr`). -/
def Att.moveAt (m : S.Move) : {o : Bool} → {j : S.Judg} → Att S o j → Nat →
    Except String (Att S o j) ⊕ Nat
  | _, j, .goal, 0 => .inl (Att.ofMove m j)
  | _, _, .goal, _ + 1 => .inr 1
  | _, _, .node m' ps h ds, k =>
    match Atts.moveAt m ds k with
    | .inl r => .inl (r.map (Att.node m' ps h))
    | .inr c => .inr c
/-- `Att.moveAt` on a list of attempts. -/
def Atts.moveAt (m : S.Move) : {o : Bool} → {ps : List S.Judg} → Atts S o ps → Nat →
    Except String (Atts S o ps) ⊕ Nat
  | _, _, .nil, _ => .inr 0
  | _, _, .cons d ds, k =>
    match Att.moveAt m d k with
    | .inl r => .inl (r.map (Atts.cons · ds))
    | .inr c =>
      match Atts.moveAt m ds (k - c) with
      | .inl r => .inl (r.map (Atts.cons d))
      | .inr c' => .inr (c + c')
end

mutual
/-- Past the last goal, `moveAt` answers with the number of goals. -/
theorem Att.moveAt_of_le (m : S.Move) : {o : Bool} → {j : S.Judg} → (d : Att S o j) → (k : Nat) →
    d.goals.length ≤ k → d.moveAt m k = .inr d.goals.length
  | _, _, .goal, 0, h => by simp at h
  | _, _, .goal, _ + 1, _ => by simp [Att.moveAt]
  | _, _, .node _ _ _ ds, k, h => by
    simp only [Att.goals_node] at h
    simp [Att.moveAt, Atts.moveAt_of_le m ds k h]
theorem Atts.moveAt_of_le (m : S.Move) : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    (k : Nat) → ds.goals.length ≤ k → ds.moveAt m k = .inr ds.goals.length
  | _, _, .nil, _, _ => by simp [Atts.moveAt]
  | _, _, .cons d ds, k, h => by
    simp only [Atts.goals_cons, List.length_append] at h
    simp [Atts.moveAt, Att.moveAt_of_le m d k (by omega),
      Atts.moveAt_of_le m ds (k - d.goals.length) (by omega)]
end

mutual
/-- If `moveAt` answers with a number, it is the number of goals, and `k` is
past them. -/
theorem Att.moveAt_inr (m : S.Move) : {o : Bool} → {j : S.Judg} → (d : Att S o j) → (k c : Nat) →
    d.moveAt m k = .inr c → c = d.goals.length ∧ c ≤ k
  | _, _, .goal, 0, _, h => by simp [Att.moveAt] at h
  | _, _, .goal, _ + 1, _, h => by
    simp only [Att.moveAt, Sum.inr.injEq] at h
    subst h
    simp
  | _, _, .node _ _ _ ds, k, c, h => by
    simp only [Att.moveAt] at h
    cases hds : Atts.moveAt m ds k with
    | inl r => rw [hds] at h; cases h
    | inr c' =>
      rw [hds] at h
      simp only [Sum.inr.injEq] at h
      subst h
      simpa using Atts.moveAt_inr m ds k c' hds
theorem Atts.moveAt_inr (m : S.Move) : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    (k c : Nat) → ds.moveAt m k = .inr c → c = ds.goals.length ∧ c ≤ k
  | _, _, .nil, _, _, h => by
    simp only [Atts.moveAt, Sum.inr.injEq] at h
    subst h
    simp
  | _, _, .cons d ds, k, c, h => by
    simp only [Atts.moveAt] at h
    cases hd : Att.moveAt m d k with
    | inl r => rw [hd] at h; cases h
    | inr c₁ =>
      rw [hd] at h
      dsimp only at h
      obtain ⟨e₁, l₁⟩ := Att.moveAt_inr m d k c₁ hd
      cases hds : Atts.moveAt m ds (k - c₁) with
      | inl r => rw [hds] at h; cases h
      | inr c₂ =>
        rw [hds] at h
        simp only [Sum.inr.injEq] at h
        obtain ⟨e₂, l₂⟩ := Atts.moveAt_inr m ds (k - c₁) c₂ hds
        subst h
        simp only [Atts.goals_cons, List.length_append]
        exact ⟨by rw [e₁, e₂], Nat.add_le_of_le_sub' l₁ l₂⟩
end

mutual
/-- **What a move that applies does to the open goals**: goal `k` is
replaced by the premises of the move. -/
theorem Att.moveAt_ok (m : S.Move) : {o : Bool} → {j : S.Judg} → (d : Att S o j) → (k : Nat) →
    {d' : Att S o j} → d.moveAt m k = .inl (.ok d') →
      ∃ g ps, d.goals[k]? = some g ∧ S.step m g = .ok ps ∧
        d'.goals = d.goals.take k ++ ps ++ d.goals.drop (k + 1)
  | _, j, .goal, 0, _, h => by
    simp only [Att.moveAt, Sum.inl.injEq] at h
    obtain ⟨ps, hs, rfl⟩ := Att.ofMove_eq_ok h
    exact ⟨j, ps, by simp, hs, by simp⟩
  | _, _, .goal, _ + 1, _, h => by simp [Att.moveAt] at h
  | _, _, .node _ _ _ ds, k, _, h => by
    simp only [Att.moveAt] at h
    split at h
    · next r hr =>
      simp only [Sum.inl.injEq] at h
      cases r with
      | ok ds' =>
        simp only [Except.map, Except.ok.injEq] at h
        subst h
        simpa using Atts.moveAt_ok m ds k hr
      | error e => simp [Except.map] at h
    · cases h
theorem Atts.moveAt_ok (m : S.Move) : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    (k : Nat) → {ds' : Atts S o ps} → ds.moveAt m k = .inl (.ok ds') →
      ∃ g qs, ds.goals[k]? = some g ∧ S.step m g = .ok qs ∧
        ds'.goals = ds.goals.take k ++ qs ++ ds.goals.drop (k + 1)
  | _, _, .nil, _, _, h => by simp [Atts.moveAt] at h
  | _, _, .cons d ds, k, _, h => by
    simp only [Atts.moveAt] at h
    split at h
    · next r hr =>
      simp only [Sum.inl.injEq] at h
      cases r with
      | ok d' =>
        simp only [Except.map, Except.ok.injEq] at h
        subst h
        obtain ⟨g, qs, hg, hs, hgoals⟩ := Att.moveAt_ok m d k hr
        obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.mp hg
        refine ⟨g, qs, ?_, hs, ?_⟩
        · simp only [Atts.goals_cons, List.getElem?_append_left hk, hg]
        · simp only [Atts.goals_cons, hgoals, List.take_append_of_le_length (Nat.le_of_lt hk),
            List.drop_append_of_le_length hk, List.append_assoc]
      | error e => simp [Except.map] at h
    · next c hc =>
      obtain ⟨e₁, l₁⟩ := Att.moveAt_inr m d k c hc
      subst e₁
      split at h
      · next r hr =>
        simp only [Sum.inl.injEq] at h
        cases r with
        | ok ds' =>
          simp only [Except.map, Except.ok.injEq] at h
          subst h
          obtain ⟨g, qs, hg, hs, hgoals⟩ := Atts.moveAt_ok m ds (k - d.goals.length) hr
          refine ⟨g, qs, ?_, hs, ?_⟩
          · simp only [Atts.goals_cons, List.getElem?_append_right l₁, hg]
          · simp only [Atts.goals_cons, hgoals, List.take_append, List.drop_append,
              List.take_of_length_le l₁, List.drop_of_length_le (Nat.le_succ_of_le l₁),
              Nat.succ_sub l₁, List.append_assoc, List.nil_append]
        | error e => simp [Except.map] at h
      · cases h
end

mutual
/-- **A move that does not apply** was tried at goal `k`, and `S.step`
refused it there. -/
theorem Att.moveAt_error (m : S.Move) : {o : Bool} → {j : S.Judg} → (d : Att S o j) →
    (k : Nat) → {e : String} → d.moveAt m k = .inl (.error e) →
      ∃ g, d.goals[k]? = some g ∧ S.step m g = .error e
  | _, j, .goal, 0, _, h => by
    simp only [Att.moveAt, Sum.inl.injEq] at h
    exact ⟨j, by simp, Att.ofMove_eq_error h⟩
  | _, _, .goal, _ + 1, _, h => by simp [Att.moveAt] at h
  | _, _, .node _ _ _ ds, k, _, h => by
    simp only [Att.moveAt] at h
    split at h
    · next r hr =>
      simp only [Sum.inl.injEq] at h
      cases r with
      | ok ds' => simp [Except.map] at h
      | error e' =>
        simp only [Except.map, Except.error.injEq] at h
        subst h
        simpa using Atts.moveAt_error m ds k hr
    · cases h
theorem Atts.moveAt_error (m : S.Move) : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    (k : Nat) → {e : String} → ds.moveAt m k = .inl (.error e) →
      ∃ g, ds.goals[k]? = some g ∧ S.step m g = .error e
  | _, _, .nil, _, _, h => by simp [Atts.moveAt] at h
  | _, _, .cons d ds, k, _, h => by
    simp only [Atts.moveAt] at h
    split at h
    · next r hr =>
      simp only [Sum.inl.injEq] at h
      cases r with
      | ok d' => simp [Except.map] at h
      | error e' =>
        simp only [Except.map, Except.error.injEq] at h
        subst h
        obtain ⟨g, hg, hs⟩ := Att.moveAt_error m d k hr
        obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.mp hg
        exact ⟨g, by simp only [Atts.goals_cons, List.getElem?_append_left hk, hg], hs⟩
    · next c hc =>
      obtain ⟨e₁, l₁⟩ := Att.moveAt_inr m d k c hc
      subst e₁
      split at h
      · next r hr =>
        simp only [Sum.inl.injEq] at h
        cases r with
        | ok ds' => simp [Except.map] at h
        | error e' =>
          simp only [Except.map, Except.error.injEq] at h
          subst h
          obtain ⟨g, hg, hs⟩ := Atts.moveAt_error m ds (k - d.goals.length) hr
          exact ⟨g, by simp only [Atts.goals_cons, List.getElem?_append_right l₁, hg], hs⟩
      · cases h
end

/-- **One move, from the root**: the line's move at the goal it names.  The
specification of a step of `run`. -/
def Att.step {j : S.Judg} (d : Att S true j) (l : Line S) : Except String (Att S true j) :=
  match d.moveAt l.move l.goal with
  | .inl (.ok d') => .ok d'
  | .inl (.error e) => .error s!"the move does not apply to goal {l.goal}: {e}"
  | .inr _ => .error s!"there is no goal {l.goal}"

/-- **The result of a run**: the attempt reached, and the first line that
failed (numbered from 0) with the reason, if one did. -/
structure Result (S : ProofSystem) (j : S.Judg) where
  /-- The attempt after the lines that were made. -/
  att : Att S true j
  /-- The first line that failed, and why. -/
  failed : Option (Nat × String) := none

/-- `Att.step` at every line; `n` is the number of the first line. -/
def Att.stepsFrom {j : S.Judg} : Nat → Att S true j → Script S → Result S j
  | _, d, [] => { att := d }
  | n, d, l :: ls =>
    match d.step l with
    | .ok d' => Att.stepsFrom (n + 1) d' ls
    | .error e => { att := d, failed := some (n, e) }

/-- **Running a script by steps from the root**: the specification of `run`. -/
def Att.runBySteps {j : S.Judg} (d : Att S true j) (ls : Script S) : Result S j :=
  Att.stepsFrom 0 d ls

/-! ## Reading a script back -/

mutual
/-- The script that builds `d` at open goal `k`: each node's move, then its
premises from the left. -/
def Att.scriptAt : {o : Bool} → {j : S.Judg} → Att S o j → Nat → Script S
  | _, _, .goal, _ => []
  | _, _, .node m _ _ ds, k => ⟨k, m⟩ :: ds.scriptAt k
/-- `Att.scriptAt` on a list: each attempt at the goal its left neighbours
leave it. -/
def Atts.scriptAt : {o : Bool} → {ps : List S.Judg} → Atts S o ps → Nat → Script S
  | _, _, .nil, _ => []
  | _, _, .cons d ds, k => d.scriptAt k ++ ds.scriptAt (k + d.goals.length)
end

/-- **The script of an attempt**, leftmost goal first. -/
def Att.script {o : Bool} {j : S.Judg} (d : Att S o j) : Script S := d.scriptAt 0

mutual
/-- A script has one line for each move. -/
theorem Att.length_scriptAt : {o : Bool} → {j : S.Judg} → (d : Att S o j) → (k : Nat) →
    (d.scriptAt k).length = d.size
  | _, _, .goal, _ => rfl
  | _, _, .node _ _ _ ds, k => by simp [Att.scriptAt, Att.size, Atts.length_scriptAt ds k]
theorem Atts.length_scriptAt : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    (k : Nat) → (ds.scriptAt k).length = ds.size
  | _, _, .nil, _ => rfl
  | _, _, .cons d ds, k => by
    simp [Atts.scriptAt, Atts.size, Att.length_scriptAt d k,
      Atts.length_scriptAt ds (k + d.goals.length)]
end

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
