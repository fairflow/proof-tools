/-
# `ProofTools.Explore.Motion`: moving the cursor in an attempt that is built

A cursor (`ProofTools.Explore.Cursor`) is a position in an attempt with its
count of the open goals left of the focus.  `run` moves it with `seek`, to
an open goal.  This file gives it the other motions, so that an attempt
that is built (by a script, by the tactic, by a search) can be walked:

    inductive Motion
      | up            to the node this one is a premise of
      | down (i)      to premise number `i` of the focus, numbered from 0
      | left          to the premise before this one, of the same node
      | right         to the premise after it
      | top           to the root
      | goal (k)      to open goal `k` of the whole attempt (`Cursor.seek`)

    Cursor.move m c      one motion: the cursor reached, if there is one
    Cursor.whyNot m c    why not, as text
    Cursor.moves c ms    motions in turn: the cursor reached, or the number
                         of the first motion that fails and why

A motion changes the position and nothing else (PROVED; `c.Ok` says that
`c.left` is the number of open goals left of the focus):

    c.Ok → c.move m = some c'   →  c'.toRoot = c.toRoot ∧ c'.Ok      (Cursor.move_some)
    c.Ok → c.moves ms = .ok c'  →  c'.toRoot = c.toRoot ∧ c'.Ok      (Cursor.moves_ok)
    c.down i = some c'  →  c'.up = some c                            (Cursor.up_down)

The name `Cursor.left` is the count of goals, so the motions to a sibling
have no function of their own: they are `Cursor.move .left` and
`Cursor.move .right`.

A derivation (`Der S j`) is walked as an attempt, through `Att.toAtt`
(`Cursor.ofAtt`).

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Explore.Cursor

namespace ProofTools.Explore

open ProofTools

variable {S : ProofSystem}

/-- **A motion of the cursor.** -/
inductive Motion where
  /-- To the node this one is a premise of. -/
  | up
  /-- To premise number `i` of the focus, numbered from 0. -/
  | down (i : Nat)
  /-- To the premise before this one, of the same node. -/
  | left
  /-- To the premise after this one, of the same node. -/
  | right
  /-- To the root. -/
  | top
  /-- To open goal `k` of the whole attempt, numbered from 0. -/
  | goal (k : Nat)
  deriving DecidableEq, Repr

/-- A motion as it is written. -/
def Motion.text : Motion → String
  | .up => "up"
  | .down i => s!"down {i}"
  | .left => "left"
  | .right => "right"
  | .top => "top"
  | .goal k => s!"goal {k}"

/-- The premises of the node at the root of an attempt; none for an open
goal. -/
def Att.premises {o : Bool} {j : S.Judg} : Att S o j → List S.Judg
  | .goal => []
  | .node _ ps _ _ => ps

/-- The cursor at the root of an attempt or of a derivation. -/
def Cursor.ofAtt {o : Bool} {j : S.Judg} (d : Att S o j) : Cursor S j := .ofRoot d.toAtt

/-- The attempt at the focus. -/
def Cursor.focus {j : S.Judg} (c : Cursor S j) : Att S true c.pos.i := c.pos.z.focus

/-- The address of the focus: the premise numbers from the root. -/
def Cursor.addr {j : S.Judg} (c : Cursor S j) : List Nat := c.pos.ds.reverse

/-! ## The motions -/

/-- **Up**: to the node the focus is a premise of.  The open goals of the
premises before the focus are no longer left of it. -/
def Cursor.up {j : S.Judg} : Cursor S j → Option (Cursor S j)
  | ⟨⟨_, _, ⟨_, .top⟩⟩, _⟩ => none
  | ⟨⟨_, _, ⟨w, .cons cr p⟩⟩, l⟩ =>
    some ⟨⟨_, _, ⟨cr.plug w, p⟩⟩, l - cr.left.goalsRev.length⟩

/-- **Down** to premise number `i` of the focus.  The open goals of the
premises before it are now left of the focus. -/
def Cursor.down {j : S.Judg} (i : Nat) (c : Cursor S j) : Option (Cursor S j) :=
  match Att.unplug c.pos.z.focus i with
  | none => none
  | some ⟨p, w, cr⟩ =>
    some ⟨⟨i :: c.pos.ds, p, ⟨w, .cons cr c.pos.z.path⟩⟩, c.left + cr.left.goalsRev.length⟩

/-- **To the root.** -/
def Cursor.top {j : S.Judg} (c : Cursor S j) : Cursor S j := .ofRoot c.toRoot

/-- **One motion.** -/
def Cursor.move {j : S.Judg} (m : Motion) (c : Cursor S j) : Option (Cursor S j) :=
  match m with
  | .up => c.up
  | .down i => c.down i
  | .left =>
    match c.pos.ds with
    | [] => none
    | 0 :: _ => none
    | (d + 1) :: _ => c.up.bind (·.down d)
  | .right =>
    match c.pos.ds with
    | [] => none
    | d :: _ => c.up.bind (·.down (d + 1))
  | .top => some c.top
  | .goal k => c.seek k

/-- Why a motion cannot be made, as text. -/
def Cursor.whyNot {j : S.Judg} (m : Motion) (c : Cursor S j) : String :=
  let n := c.pos.z.focus.premises.length
  match m with
  | .up => "the focus is the root"
  | .down i =>
    if c.pos.z.focus.isGoal then "the focus is an open goal: it has no premises"
    else if n = 0 then "the move at the focus has no premises"
    else s!"the focus has no premise {i}: its premises are numbered 0 to {n - 1}"
  | .left =>
    match c.pos.ds with
    | [] => "the focus is the root"
    | _ => "the focus is the first premise of its node"
  | .right =>
    match c.pos.ds with
    | [] => "the focus is the root"
    | _ => "the focus is the last premise of its node"
  | .top => "the motion can be made"
  | .goal k => s!"there is no goal {k}"

/-- **Motions in turn**: the cursor reached, or the number of the first
motion that cannot be made (from 0) and why. -/
def Cursor.movesFrom {j : S.Judg} : Nat → Cursor S j → List Motion →
    Except (Nat × String) (Cursor S j)
  | _, c, [] => .ok c
  | n, c, m :: ms =>
    match c.move m with
    | some c' => Cursor.movesFrom (n + 1) c' ms
    | none => .error (n, c.whyNot m)

/-- **Motions in turn**, numbered from 0. -/
def Cursor.moves {j : S.Judg} (c : Cursor S j) (ms : List Motion) :
    Except (Nat × String) (Cursor S j) := Cursor.movesFrom 0 c ms

/-! ## A motion changes the position and nothing else -/

theorem Cursor.up_some {j : S.Judg} {c c' : Cursor S j} (hc : c.Ok) (h : c.up = some c') :
    c'.toRoot = c.toRoot ∧ c'.Ok := by
  obtain ⟨⟨ds, i, ⟨w, p⟩⟩, l⟩ := c
  cases p with
  | top => simp [Cursor.up] at h
  | cons cr p =>
    simp only [Cursor.up, Option.some.injEq] at h
    subst h
    refine ⟨rfl, ?_⟩
    unfold Cursor.Ok at hc ⊢
    simp only [Path.goalsL, List.length_append] at hc
    simp only
    omega

theorem Cursor.down_some {j : S.Judg} {i : Nat} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.down i = some c') : c'.toRoot = c.toRoot ∧ c'.Ok := by
  unfold Cursor.down at h
  split at h
  · cases h
  · next p w cr hu =>
    simp only [Option.some.injEq] at h
    subst h
    have hp : cr.plug w = c.pos.z.focus :=
      Zip.Deriv.Unplug.plug_unplug (L := attDeriv S true) hu
    refine ⟨?_, ?_⟩
    · show Zip.Deriv.Path.plug c.pos.z.path (cr.plug w) = _
      rw [hp]
      rfl
    · unfold Cursor.Ok at hc ⊢
      simp only [Path.goalsL, List.length_append]
      omega

/-- **Up undoes down.** -/
theorem Cursor.up_down {j : S.Judg} {i : Nat} {c c' : Cursor S j} (h : c.down i = some c') :
    c'.up = some c := by
  unfold Cursor.down at h
  split at h
  · cases h
  · next p w cr hu =>
    simp only [Option.some.injEq] at h
    subst h
    have hp : cr.plug w = c.pos.z.focus :=
      Zip.Deriv.Unplug.plug_unplug (L := attDeriv S true) hu
    obtain ⟨⟨ds, k, ⟨f, path⟩⟩, l⟩ := c
    simp only at hp
    simp only [Cursor.up, hp, Nat.add_sub_cancel]

/-- **(L1), (L2) A motion keeps the attempt, and the count of goals stays
right.** -/
theorem Cursor.move_some {j : S.Judg} {m : Motion} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.move m = some c') : c'.toRoot = c.toRoot ∧ c'.Ok := by
  cases m with
  | up => exact Cursor.up_some hc h
  | down i => exact Cursor.down_some hc h
  | left =>
    simp only [Cursor.move] at h
    split at h
    · cases h
    · cases h
    · obtain ⟨c₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e₁, o₁⟩ := Cursor.up_some hc h₁
      obtain ⟨e₂, o₂⟩ := Cursor.down_some o₁ h₂
      exact ⟨e₂.trans e₁, o₂⟩
  | right =>
    simp only [Cursor.move] at h
    split at h
    · cases h
    · obtain ⟨c₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e₁, o₁⟩ := Cursor.up_some hc h₁
      obtain ⟨e₂, o₂⟩ := Cursor.down_some o₁ h₂
      exact ⟨e₂.trans e₁, o₂⟩
  | top =>
    simp only [Cursor.move, Option.some.injEq] at h
    subst h
    exact ⟨rfl, Cursor.ok_ofRoot _⟩
  | goal k =>
    obtain ⟨e, _, _, o⟩ := Cursor.seek_some hc h
    exact ⟨e, o⟩

theorem Cursor.movesFrom_ok {j : S.Judg} : ∀ (ms : List Motion) (n : Nat) {c c' : Cursor S j},
    c.Ok → Cursor.movesFrom n c ms = .ok c' → c'.toRoot = c.toRoot ∧ c'.Ok
  | [], _, _, _, hc, h => by
    simp only [Cursor.movesFrom, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, hc⟩
  | m :: ms, n, c, c', hc, h => by
    simp only [Cursor.movesFrom] at h
    split at h
    · next c₁ h₁ =>
      obtain ⟨e₁, o₁⟩ := Cursor.move_some hc h₁
      obtain ⟨e₂, o₂⟩ := Cursor.movesFrom_ok ms (n + 1) o₁ h
      exact ⟨e₂.trans e₁, o₂⟩
    · cases h

/-- **Motions in turn keep the attempt, and the count of goals stays
right.** -/
theorem Cursor.moves_ok {j : S.Judg} {ms : List Motion} {c c' : Cursor S j} (hc : c.Ok)
    (h : c.moves ms = .ok c') : c'.toRoot = c.toRoot ∧ c'.Ok :=
  Cursor.movesFrom_ok ms 0 hc h

/-- The cursor at the root of an attempt or of a derivation counts right. -/
theorem Cursor.ok_ofAtt {o : Bool} {j : S.Judg} (d : Att S o j) : (Cursor.ofAtt d).Ok :=
  Cursor.ok_ofRoot _

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
