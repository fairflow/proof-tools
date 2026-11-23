/-
# `ProofTools.Explore.Cursor`: `run`, with a zipper kept from line to line

A **cursor** is a position in an attempt (a zipper, `Pos`) together with
`left`, the number of open goals of the whole attempt left of the focus.
With `left` the cursor knows the number of the goal it is on, and can find
goal `k` from where it is, without going back to the root.

    Att.seekIn d n p        the `n`-th open goal inside `d`, which sits at the
                            hole of `p`; or the number of open goals of `d`
    Path.seekRight p d n    the `n`-th open goal right of the hole of `p`
    Path.seekLeft p d n     the `n`-th open goal left of it, counted leftwards
    Cursor.seek k c         to open goal `k`: left if `k < c.left`, else
                            inside the focus, else right
    Cursor.replace c d      the focus becomes the attempt `d` (the zipper's
                            `replace`): the one change at a position
    Cursor.rule c m         the open goal at the focus becomes the node of
                            the move `m`, its premises open
    Cursor.prune c          the focus becomes an open goal
    Cursor.graft c d        the open goal at the focus becomes `d`
    Cursor.step c l         seek the line's goal, make its move there
                            (`Cursor.rule`)
    run S j ls              `Cursor.step` at every line; the attempt is
                            rebuilt once, at the end

What the changes do, and a session of motions and changes, of which a
script is a special case, are in `ProofTools.Explore.Session`.

What the seeking functions find (PROVED; `c.Ok` says that `c.left` is the
number of goals left of the focus):

    c.Ok → c.seek k = some c' →
        c'.toRoot = c.toRoot ∧ c'.pos.z.focus = .goal ∧ c'.left = k ∧ c'.Ok   (Cursor.seek_some)
    c.Ok → c.seek k = none → c.toRoot.goals.length ≤ k                        (Cursor.seek_none)

That `run` equals the run by steps from the root is in
`ProofTools.Explore.Run`.

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Explore.Zipper
import ProofTools.Explore.Script

namespace ProofTools.Explore

open ProofTools

variable {S : ProofSystem}

/-! ## Seeking -/

mutual
/-- **The `n`-th open goal inside `d`**, where `d` sits at the hole of `p`:
its position (`inl`), or, if `d` has no goal `n`, the number of open goals
of `d` (`inr`).  One pass. -/
def Att.seekIn {t : S.Judg} : {o : Bool} → {s : S.Judg} → Att S o s → Nat → {ds : List Nat} →
    Path S o ds s t → Pos S o t ⊕ Nat
  | _, _, .goal, 0, _, p => .inl ⟨_, _, ⟨.goal, p⟩⟩
  | _, _, .goal, _ + 1, _, _ => .inr 1
  | _, _, .node m _ h cs, n, _, p => Atts.seekIn m (lsr := []) h .nil cs n p
/-- `Att.seekIn` along the premises of a node, from the left; the attempts
passed are kept on the left side, nearest first. -/
def Atts.seekIn {t : S.Judg} (m : S.Move) {s : S.Judg} : {o : Bool} →
    {lsr rs : List S.Judg} → S.step m s = .ok (lsr.reverseAux rs) → Atts S o lsr →
    Atts S o rs → Nat → {ds : List Nat} → Path S o ds s t → Pos S o t ⊕ Nat
  | _, _, _, _, _, .nil, _, _, _ => .inr 0
  | _, lsr, q :: rs, h, left, .cons d right, n, _, p =>
    match Att.seekIn d n (.cons (d := lsr.length) ⟨m, lsr, rs, h, left, right, rfl⟩ p) with
    | .inl x => .inl x
    | .inr c =>
      match Atts.seekIn m (lsr := q :: lsr) (rs := rs) h (.cons d left) right (n - c) p with
      | .inl x => .inl x
      | .inr c' => .inr (c + c')
end

/-- **The `n`-th open goal right of the hole of `p`**, which holds `d`: up
the path, and into the premises right of it. -/
def Path.seekRight {o : Bool} {t : S.Judg} : {ds : List Nat} → {s : S.Judg} →
    Path S o ds s t → Att S o s → Nat → Option (Pos S o t)
  | _, _, .top, _, _ => none
  | _, _, .cons (i := q) ⟨mv, lsr, rs, h, left, right, hd⟩ p, d, n =>
    match Atts.seekIn mv (lsr := q :: lsr) (rs := rs) h (.cons d left) right n p with
    | .inl x => some x
    | .inr k => Path.seekRight p (Crumb.plug ⟨mv, lsr, rs, h, left, right, hd⟩ d) (n - k)

/-- The `n`-th open goal among the attempts `left` of a hole, counted
leftwards from the hole: its position, or the number of open goals of
`left`. -/
def Atts.seekLeftIn {t : S.Judg} (m : S.Move) {s : S.Judg} : {o : Bool} →
    {lsr rs : List S.Judg} → S.step m s = .ok (lsr.reverseAux rs) → Atts S o lsr →
    Atts S o rs → Nat → {ds : List Nat} → Path S o ds s t → Pos S o t ⊕ Nat
  | _, _, _, _, .nil, _, _, _, _ => .inr 0
  | _, q :: lsr, rs, h, .cons e left, right, n, _, p =>
    if n < e.goals.length then
      Att.seekIn e (e.goals.length - 1 - n)
        (.cons (d := lsr.length) ⟨m, lsr, rs, h, left, right, rfl⟩ p)
    else
      match Atts.seekLeftIn m (lsr := lsr) (rs := q :: rs) h left (.cons e right)
          (n - e.goals.length) p with
      | .inl x => .inl x
      | .inr c => .inr (e.goals.length + c)

/-- **The `n`-th open goal left of the hole of `p`**, counted leftwards. -/
def Path.seekLeft {o : Bool} {t : S.Judg} : {ds : List Nat} → {s : S.Judg} →
    Path S o ds s t → Att S o s → Nat → Option (Pos S o t)
  | _, _, .top, _, _ => none
  | _, _, .cons (i := q) ⟨mv, lsr, rs, h, left, right, hd⟩ p, d, n =>
    match Atts.seekLeftIn mv (lsr := lsr) (rs := q :: rs) h left (.cons d right) n p with
    | .inl x => some x
    | .inr k => Path.seekLeft p (Crumb.plug ⟨mv, lsr, rs, h, left, right, hd⟩ d) (n - k)

/-! ## The cursor -/

/-- **A cursor**: a position in an attempt at `j`, and the number of open
goals of the whole attempt left of its focus. -/
structure Cursor (S : ProofSystem) (j : S.Judg) where
  /-- The zipper, with its address and the judgment of its focus. -/
  pos : Pos S true j
  /-- The number of open goals left of the focus. -/
  left : Nat

/-- The cursor at the root. -/
def Cursor.ofRoot {j : S.Judg} (d : Att S true j) : Cursor S j :=
  ⟨⟨[], j, Zip.Deriv.Zipper.ofRoot d⟩, 0⟩

/-- The whole attempt. -/
def Cursor.toRoot {j : S.Judg} (c : Cursor S j) : Att S true j := c.pos.z.toRoot

/-- **To open goal `k`**, from where the cursor is. -/
def Cursor.seek {j : S.Judg} (k : Nat) (c : Cursor S j) : Option (Cursor S j) :=
  if k < c.left then
    (Path.seekLeft c.pos.z.path c.pos.z.focus (c.left - 1 - k)).map (⟨·, k⟩)
  else
    match Att.seekIn c.pos.z.focus (k - c.left) c.pos.z.path with
    | .inl x => some ⟨x, k⟩
    | .inr n => (Path.seekRight c.pos.z.path c.pos.z.focus (k - c.left - n)).map (⟨·, k⟩)

/-- Is the attempt an open goal? -/
def Att.isGoal {o : Bool} {j : S.Judg} : Att S o j → Bool
  | .goal => true
  | .node _ _ _ _ => false

theorem Att.eq_goal_of_isGoal {j : S.Judg} (d : Att S true j) (h : d.isGoal = true) :
    d = .goal := by
  cases d with
  | goal => rfl
  | node _ _ _ _ => simp [Att.isGoal] at h

/-! ## Changing the attempt at the focus -/

/-- **Replace the focus** by an attempt at the same judgment (the zipper's
`replace`).  The position stays, and so does the count: the goals left of
the focus are not touched. -/
def Cursor.replace {j : S.Judg} (c : Cursor S j) (d : Att S true c.pos.i) : Cursor S j :=
  ⟨⟨c.pos.ds, c.pos.i, c.pos.z.replace d⟩, c.left⟩

/-- **Prune**: the focus, whatever it is, becomes an open goal. -/
def Cursor.prune {j : S.Judg} (c : Cursor S j) : Cursor S j := c.replace .goal

/-- Why a change that needs an open goal cannot be made. -/
def Cursor.notOpen : String := "the focus is not an open goal"

/-- **Graft**: the open goal at the focus becomes the attempt `d`, at the
same judgment. -/
def Cursor.graft {j : S.Judg} (c : Cursor S j) (d : Att S true c.pos.i) :
    Except String (Cursor S j) :=
  if c.pos.z.focus.isGoal then .ok (c.replace d) else .error Cursor.notOpen

/-- **A rule**: the open goal at the focus becomes the node of the move `m`,
its premises open; or the reason the move does not apply there. -/
def Cursor.rule {j : S.Judg} (c : Cursor S j) (m : S.Move) : Except String (Cursor S j) :=
  if c.pos.z.focus.isGoal then (Att.ofMove m c.pos.i).map c.replace else .error Cursor.notOpen

/-- **One line**: seek its goal, and make its move there.  The cursor stays
on the node made.  It is the motion `goal l.goal`, then `Cursor.rule`
(`Cursor.step_eq`, PROVED); the rule's test that the focus is an open goal
is left out here, since `seek` finds nothing else. -/
def Cursor.step {j : S.Judg} (c : Cursor S j) (l : Line S) : Except String (Cursor S j) :=
  match c.seek l.goal with
  | none => .error s!"there is no goal {l.goal}"
  | some c' =>
    match Att.ofMove l.move c'.pos.i with
    | .ok nd => .ok (c'.replace nd)
    | .error e => .error s!"the move does not apply to goal {l.goal}: {e}"

/-- `Cursor.step` at every line; `n` is the number of the first line.  The
attempt is rebuilt when the script ends or a line fails. -/
def Cursor.runFrom {j : S.Judg} : Nat → Cursor S j → Script S → Result S j
  | _, c, [] => { att := c.toRoot }
  | n, c, l :: ls =>
    match c.step l with
    | .ok c' => Cursor.runFrom (n + 1) c' ls
    | .error e => { att := c.toRoot, failed := some (n, e) }

/-- Run a script on an attempt, its lines numbered from `n`. -/
def Att.runFrom {j : S.Judg} (n : Nat) (d : Att S true j) (ls : Script S) : Result S j :=
  Cursor.runFrom n (.ofRoot d) ls

/-- **Run a script on an attempt.** -/
def Att.run {j : S.Judg} (d : Att S true j) (ls : Script S) : Result S j := d.runFrom 0 ls

/-- **Run a script at a judgment**, from the open goal. -/
def run (S : ProofSystem) (j : S.Judg) (ls : Script S) : Result S j := Att.run .goal ls

/-! ## What seeking finds -/

mutual
theorem Att.seekIn_inr {t : S.Judg} : {o : Bool} → {s : S.Judg} → (d : Att S o s) → (n : Nat) →
    {ds : List Nat} → (p : Path S o ds s t) → {c : Nat} → Att.seekIn d n p = .inr c →
      c = d.goals.length ∧ d.goals.length ≤ n
  | _, _, .goal, 0, _, _, _, h => by simp [Att.seekIn] at h
  | _, _, .goal, _ + 1, _, _, _, h => by
    simp only [Att.seekIn, Sum.inr.injEq] at h
    subst h
    simp
  | _, _, .node m _ hs cs, n, _, p, _, h => by
    simp only [Att.seekIn] at h
    simpa using Atts.seekIn_inr m (lsr := []) hs .nil cs n p h
theorem Atts.seekIn_inr {t : S.Judg} (m : S.Move) {s : S.Judg} : {o : Bool} →
    {lsr rs : List S.Judg} → (h : S.step m s = .ok (lsr.reverseAux rs)) → (left : Atts S o lsr) →
    (right : Atts S o rs) → (n : Nat) → {ds : List Nat} → (p : Path S o ds s t) → {c : Nat} →
    Atts.seekIn m h left right n p = .inr c → c = right.goals.length ∧ right.goals.length ≤ n
  | _, _, _, _, _, .nil, _, _, _, _, hx => by
    simp only [Atts.seekIn, Sum.inr.injEq] at hx
    subst hx
    simp
  | _, lsr, q :: rs, h, left, .cons d right, n, _, p, _, hx => by
    simp only [Atts.seekIn] at hx
    split at hx
    · cases hx
    · next c₁ h₁ =>
      obtain ⟨e₁, l₁⟩ := Att.seekIn_inr d n _ h₁
      split at hx
      · cases hx
      · next c₂ h₂ =>
        obtain ⟨e₂, l₂⟩ := Atts.seekIn_inr m (lsr := q :: lsr) (rs := rs) h (.cons d left) right
          (n - c₁) p h₂
        simp only [Sum.inr.injEq] at hx
        subst hx
        simp only [Atts.goals_cons, List.length_append]
        exact ⟨by omega, by omega⟩
end

mutual
theorem Att.seekIn_inl {t : S.Judg} : {o : Bool} → {s : S.Judg} → (d : Att S o s) → (n : Nat) →
    {ds : List Nat} → (p : Path S o ds s t) → {x : Pos S o t} → Att.seekIn d n p = .inl x →
      x.z.toRoot = Zip.Deriv.Path.plug p d ∧ x.z.focus.isGoal = true ∧
        (Path.goalsL x.z.path).length = (Path.goalsL p).length + n
  | _, _, .goal, 0, _, p, _, h => by
    simp only [Att.seekIn, Sum.inl.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  | _, _, .goal, _ + 1, _, _, _, h => by simp [Att.seekIn] at h
  | _, _, .node m _ hs cs, n, _, p, _, h => by
    simp only [Att.seekIn] at h
    obtain ⟨r₁, r₂, r₃⟩ := Atts.seekIn_inl m (lsr := []) hs .nil cs n p h
    exact ⟨r₁, r₂, by simpa using r₃⟩
theorem Atts.seekIn_inl {t : S.Judg} (m : S.Move) {s : S.Judg} : {o : Bool} →
    {lsr rs : List S.Judg} → (h : S.step m s = .ok (lsr.reverseAux rs)) → (left : Atts S o lsr) →
    (right : Atts S o rs) → (n : Nat) → {ds : List Nat} → (p : Path S o ds s t) →
    {x : Pos S o t} → Atts.seekIn m h left right n p = .inl x →
      x.z.toRoot = Zip.Deriv.Path.plug p (.node m _ h (left.revAppend right)) ∧
        x.z.focus.isGoal = true ∧
        (Path.goalsL x.z.path).length = (Path.goalsL p).length + left.goalsRev.length + n
  | _, _, _, _, _, .nil, _, _, _, _, hx => by simp [Atts.seekIn] at hx
  | _, lsr, q :: rs, h, left, .cons d right, n, _, p, _, hx => by
    simp only [Atts.seekIn] at hx
    split at hx
    · next y h₁ =>
      simp only [Sum.inl.injEq] at hx
      subst hx
      obtain ⟨r₁, r₂, r₃⟩ := Att.seekIn_inl d n _ h₁
      refine ⟨r₁, r₂, ?_⟩
      rw [r₃]
      simp [Path.goalsL, Nat.add_assoc]
    · next c₁ h₁ =>
      obtain ⟨e₁, l₁⟩ := Att.seekIn_inr d n _ h₁
      split at hx
      · next y h₂ =>
        simp only [Sum.inl.injEq] at hx
        subst hx
        obtain ⟨r₁, r₂, r₃⟩ := Atts.seekIn_inl m (lsr := q :: lsr) (rs := rs) h (.cons d left)
          right (n - c₁) p h₂
        refine ⟨r₁, r₂, ?_⟩
        rw [r₃]
        simp only [Atts.goalsRev_cons, List.length_append]
        omega
      · cases hx
end

theorem Path.seekRight_some {o : Bool} {t : S.Judg} : {ds : List Nat} → {s : S.Judg} →
    (p : Path S o ds s t) → (d : Att S o s) → (n : Nat) → {x : Pos S o t} →
    Path.seekRight p d n = some x →
      x.z.toRoot = Zip.Deriv.Path.plug p d ∧ x.z.focus.isGoal = true ∧
        (Path.goalsL x.z.path).length = (Path.goalsL p).length + d.goals.length + n
  | _, _, .top, _, _, _, h => by simp [Path.seekRight] at h
  | _, _, .cons (i := q) ⟨mv, lsr, rs, hs, left, right, hd⟩ p, d, n, _, h => by
    simp only [Path.seekRight] at h
    split at h
    · next y hy =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨r₁, r₂, r₃⟩ := Atts.seekIn_inl mv (lsr := q :: lsr) (rs := rs) hs (.cons d left)
        right n p hy
      refine ⟨r₁, r₂, ?_⟩
      rw [r₃]
      simp only [Path.goalsL, Atts.goalsRev_cons, List.length_append]
      omega
    · next k hk =>
      obtain ⟨e, l⟩ := Atts.seekIn_inr mv (lsr := q :: lsr) (rs := rs) hs (.cons d left) right n
        p hk
      obtain ⟨r₁, r₂, r₃⟩ := Path.seekRight_some p _ (n - k) h
      refine ⟨r₁, r₂, ?_⟩
      rw [r₃]
      simp only [Path.goalsL, Crumb.goals_plug, List.length_append]
      omega

theorem Path.seekRight_none {o : Bool} {t : S.Judg} : {ds : List Nat} → {s : S.Judg} →
    (p : Path S o ds s t) → (d : Att S o s) → (n : Nat) → Path.seekRight p d n = none →
      (Path.goalsR p).length ≤ n
  | _, _, .top, _, _, _ => by simp [Path.goalsR]
  | _, _, .cons (i := q) ⟨mv, lsr, rs, hs, left, right, hd⟩ p, d, n, h => by
    simp only [Path.seekRight] at h
    split at h
    · cases h
    · next k hk =>
      obtain ⟨e, l⟩ := Atts.seekIn_inr mv (lsr := q :: lsr) (rs := rs) hs (.cons d left) right n
        p hk
      have := Path.seekRight_none p _ (n - k) h
      simp only [Path.goalsR, List.length_append]
      omega

theorem Atts.seekLeftIn_inl {t : S.Judg} (m : S.Move) {s : S.Judg} : {o : Bool} →
    {lsr rs : List S.Judg} → (h : S.step m s = .ok (lsr.reverseAux rs)) → (left : Atts S o lsr) →
    (right : Atts S o rs) → (n : Nat) → {ds : List Nat} → (p : Path S o ds s t) →
    {x : Pos S o t} → Atts.seekLeftIn m h left right n p = .inl x →
      x.z.toRoot = Zip.Deriv.Path.plug p (.node m _ h (left.revAppend right)) ∧
        x.z.focus.isGoal = true ∧
        (Path.goalsL x.z.path).length + n + 1 = (Path.goalsL p).length + left.goalsRev.length
  | _, _, _, _, .nil, _, _, _, _, _, hx => by simp [Atts.seekLeftIn] at hx
  | _, q :: lsr, rs, h, .cons e left, right, n, _, p, _, hx => by
    simp only [Atts.seekLeftIn] at hx
    split at hx
    · next hn =>
      obtain ⟨r₁, r₂, r₃⟩ := Att.seekIn_inl e _ _ hx
      refine ⟨r₁, r₂, ?_⟩
      rw [r₃]
      simp only [Path.goalsL, Atts.goalsRev_cons, List.length_append]
      omega
    · next hn =>
      split at hx
      · next y hy =>
        simp only [Sum.inl.injEq] at hx
        subst hx
        obtain ⟨r₁, r₂, r₃⟩ := Atts.seekLeftIn_inl m (lsr := lsr) (rs := q :: rs) h left
          (.cons e right) (n - e.goals.length) p hy
        refine ⟨r₁, r₂, ?_⟩
        simp only [Atts.goalsRev_cons, List.length_append]
        omega
      · cases hx

theorem Atts.seekLeftIn_inr {t : S.Judg} (m : S.Move) {s : S.Judg} : {o : Bool} →
    {lsr rs : List S.Judg} → (h : S.step m s = .ok (lsr.reverseAux rs)) → (left : Atts S o lsr) →
    (right : Atts S o rs) → (n : Nat) → {ds : List Nat} → (p : Path S o ds s t) → {c : Nat} →
    Atts.seekLeftIn m h left right n p = .inr c → c = left.goalsRev.length ∧ c ≤ n
  | _, _, _, _, .nil, _, _, _, _, _, hx => by
    simp only [Atts.seekLeftIn, Sum.inr.injEq] at hx
    subst hx
    simp
  | _, q :: lsr, rs, h, .cons e left, right, n, _, p, _, hx => by
    simp only [Atts.seekLeftIn] at hx
    split at hx
    · next hn =>
      obtain ⟨-, l⟩ := Att.seekIn_inr e _ _ hx
      exact ⟨by omega, by omega⟩
    · next hn =>
      split at hx
      · cases hx
      · next c' hc' =>
        obtain ⟨e', l'⟩ := Atts.seekLeftIn_inr m (lsr := lsr) (rs := q :: rs) h left
          (.cons e right) (n - e.goals.length) p hc'
        simp only [Sum.inr.injEq] at hx
        subst hx
        simp only [Atts.goalsRev_cons, List.length_append]
        exact ⟨by omega, by omega⟩

theorem Path.seekLeft_some {o : Bool} {t : S.Judg} : {ds : List Nat} → {s : S.Judg} →
    (p : Path S o ds s t) → (d : Att S o s) → (n : Nat) → {x : Pos S o t} →
    Path.seekLeft p d n = some x →
      x.z.toRoot = Zip.Deriv.Path.plug p d ∧ x.z.focus.isGoal = true ∧
        (Path.goalsL x.z.path).length + n + 1 = (Path.goalsL p).length
  | _, _, .top, _, _, _, h => by simp [Path.seekLeft] at h
  | _, _, .cons (i := q) ⟨mv, lsr, rs, hs, left, right, hd⟩ p, d, n, _, h => by
    simp only [Path.seekLeft] at h
    split at h
    · next y hy =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨r₁, r₂, r₃⟩ := Atts.seekLeftIn_inl mv (lsr := lsr) (rs := q :: rs) hs left
        (.cons d right) n p hy
      refine ⟨r₁, r₂, ?_⟩
      simp only [Path.goalsL, List.length_append]
      omega
    · next k hk =>
      obtain ⟨e, l⟩ := Atts.seekLeftIn_inr mv (lsr := lsr) (rs := q :: rs) hs left
        (.cons d right) n p hk
      obtain ⟨r₁, r₂, r₃⟩ := Path.seekLeft_some p _ (n - k) h
      refine ⟨r₁, r₂, ?_⟩
      simp only [Path.goalsL, List.length_append]
      omega

theorem Path.seekLeft_none {o : Bool} {t : S.Judg} : {ds : List Nat} → {s : S.Judg} →
    (p : Path S o ds s t) → (d : Att S o s) → (n : Nat) → Path.seekLeft p d n = none →
      (Path.goalsL p).length ≤ n
  | _, _, .top, _, _, _ => by simp [Path.goalsL]
  | _, _, .cons (i := q) ⟨mv, lsr, rs, hs, left, right, hd⟩ p, d, n, h => by
    simp only [Path.seekLeft] at h
    split at h
    · cases h
    · next k hk =>
      obtain ⟨e, l⟩ := Atts.seekLeftIn_inr mv (lsr := lsr) (rs := q :: rs) hs left
        (.cons d right) n p hk
      have := Path.seekLeft_none p _ (n - k) h
      simp only [Path.goalsL, List.length_append]
      omega

/-! ## The cursor's count -/

/-- **The cursor's count is right**: `left` is the number of open goals left
of the focus. -/
def Cursor.Ok {j : S.Judg} (c : Cursor S j) : Prop :=
  c.left = (Path.goalsL c.pos.z.path).length

theorem Cursor.ok_ofRoot {j : S.Judg} (d : Att S true j) : (Cursor.ofRoot d).Ok := rfl

@[simp] theorem Cursor.toRoot_ofRoot {j : S.Judg} (d : Att S true j) :
    (Cursor.ofRoot d).toRoot = d := rfl

/-- Replacing the focus keeps the count right: the path is not touched. -/
theorem Cursor.ok_replace {j : S.Judg} {c : Cursor S j} (hc : c.Ok) (d : Att S true c.pos.i) :
    (c.replace d).Ok := hc

/-- **What a rule that applies has done**: the focus was an open goal, and
it is replaced by the node of the move, as `Att.ofMove` makes it. -/
theorem Cursor.rule_eq_ok {j : S.Judg} {m : S.Move} {c c' : Cursor S j} (h : c.rule m = .ok c') :
    c.pos.z.focus.isGoal = true ∧ ∃ nd, Att.ofMove m c.pos.i = .ok nd ∧ c' = c.replace nd := by
  unfold Cursor.rule at h
  split at h
  · next hg =>
    cases hm : Att.ofMove m c.pos.i with
    | ok nd =>
      rw [hm] at h
      exact ⟨hg, nd, rfl, (Except.ok.inj h).symm⟩
    | error e =>
      rw [hm] at h
      cases h
  · cases h

/-- **Seeking finds the goal**: the attempt is unchanged, the focus is an
open goal, it is goal `k`, and the count is right. -/
theorem Cursor.seek_some {j : S.Judg} {k : Nat} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.seek k = some c') :
    c'.toRoot = c.toRoot ∧ c'.pos.z.focus = .goal ∧ c'.left = k ∧ c'.Ok := by
  unfold Cursor.seek at h
  split at h
  · next hk =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨r₁, r₂, r₃⟩ := Path.seekLeft_some _ _ _ hx
    refine ⟨r₁, Att.eq_goal_of_isGoal _ r₂, rfl, ?_⟩
    show k = (Path.goalsL x.z.path).length
    have := hc
    unfold Cursor.Ok at this
    omega
  · next hk =>
    split at h
    · next x hx =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨r₁, r₂, r₃⟩ := Att.seekIn_inl _ _ _ hx
      refine ⟨r₁, Att.eq_goal_of_isGoal _ r₂, rfl, ?_⟩
      show k = (Path.goalsL x.z.path).length
      have := hc
      unfold Cursor.Ok at this
      omega
    · next n hn =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨e, l⟩ := Att.seekIn_inr _ _ _ hn
      obtain ⟨r₁, r₂, r₃⟩ := Path.seekRight_some _ _ _ hx
      refine ⟨r₁, Att.eq_goal_of_isGoal _ r₂, rfl, ?_⟩
      show k = (Path.goalsL x.z.path).length
      have := hc
      unfold Cursor.Ok at this
      omega

/-- Seeking finds an open goal, from any cursor. -/
theorem Cursor.seek_isGoal {j : S.Judg} {k : Nat} {c c' : Cursor S j} (h : c.seek k = some c') :
    c'.pos.z.focus.isGoal = true := by
  unfold Cursor.seek at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact (Path.seekLeft_some _ _ _ hx).2.1
  · split at h
    · next x hx =>
      simp only [Option.some.injEq] at h
      subst h
      exact (Att.seekIn_inl _ _ _ hx).2.1
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      exact (Path.seekRight_some _ _ _ hx).2.1

/-- **A line is: to its goal, then the rule there.** -/
theorem Cursor.step_eq {j : S.Judg} (c : Cursor S j) (l : Line S) :
    c.step l =
      match c.seek l.goal with
      | none => .error s!"there is no goal {l.goal}"
      | some c' =>
        match c'.rule l.move with
        | .ok c'' => .ok c''
        | .error e => .error s!"the move does not apply to goal {l.goal}: {e}" := by
  unfold Cursor.step
  cases hs : c.seek l.goal with
  | none => rfl
  | some c' =>
    simp only [Cursor.rule, Cursor.seek_isGoal hs, if_true]
    cases Att.ofMove l.move c'.pos.i <;> rfl

/-- **Seeking fails only past the last goal.** -/
theorem Cursor.seek_none {j : S.Judg} {k : Nat} {c : Cursor S j} (hc : c.Ok)
    (h : c.seek k = none) : c.toRoot.goals.length ≤ k := by
  have hg : c.toRoot.goals.length = (Path.goalsL c.pos.z.path).length +
      c.pos.z.focus.goals.length + (Path.goalsR c.pos.z.path).length := by
    show (Zip.Deriv.Path.plug c.pos.z.path c.pos.z.focus).goals.length = _
    rw [Path.goals_plug]
    simp only [List.length_append]
  unfold Cursor.Ok at hc
  unfold Cursor.seek at h
  split at h
  · next hk =>
    simp only [Option.map_eq_none_iff] at h
    have := Path.seekLeft_none _ _ _ h
    omega
  · next hk =>
    split at h
    · cases h
    · next n hn =>
      simp only [Option.map_eq_none_iff] at h
      obtain ⟨e, l⟩ := Att.seekIn_inr _ _ _ hn
      have := Path.seekRight_none _ _ _ h
      omega

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.  `omega` is given one
-- comparison at a time: asked for a conjunction it negates it with
-- `Classical.propDecidable`, and `Classical.choice` comes in.
#axioms_within_file [propext, Quot.sound]
