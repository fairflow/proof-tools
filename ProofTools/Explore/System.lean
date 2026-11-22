/-
# `ProofTools.Explore.System`: proof systems, attempts, derivations

A **proof system** is a type of judgments, a type of moves (a rule, named by
its data) and one function, `step`: the premises a move asks for at a
judgment, or the reason it does not apply.

An **attempt** `Att S o j` is a tree of moves with conclusion `j`.  The
Boolean `o` says whether open goals are allowed; a **derivation** `Der S j`
is an attempt where they are not.  Each node writes its premises `ps` and
carries the equation `S.step m j = .ok ps`, which the kernel proves by
evaluating `step`.  The children are a list indexed by the premises
(`Atts`), so an attempt is first-order data.

The one thing an instance proves about its `step` is that its moves are
sound for its own notion of what holds.  That notion is a family `T` over
the judgments, into any sort: a proposition (validity, or that a derivation
exists), or a type, the derivations of the calculus as its source states
it.

    S.SoundT T  :=  ∀ m j ps, S.step m j = .ok ps → Each T ps → T j

`Each T ps` is one `T p` for each premise `p`, by position, so that two
premises with one judgment keep their own derivations.  Then (here):

    S.SoundT T → (d : Att S o j) → Each T d.goals → T j             (Att.mapOut)
    S.SoundT T → Der S j → T j                                       (Der.mapOut)

`Att.mapOut` says that an attempt is a derived rule, from its open goals to
its root; when `T` is a type it is a function, and a derivation of the
explorer gives a derivation of the calculus as data.

For a proposition `D` the same is said with the premises taken by
membership, which is what an instance proves when it has no more than a
proposition, and (PROVED here) it is the same notion:

    S.Sound D  :=  ∀ m j ps, S.step m j = .ok ps → (∀ p ∈ ps, D p) → D j
    S.SoundT D ↔ S.Sound D                                           (soundT_iff_sound)
    S.Sound D → (d : Att S o j) → (∀ g ∈ d.goals, D g) → D j        (Att.sound)
    S.Sound D → Der S j → D j                                        (Der.sound)
    S.SoundT T → S.Sound (fun j => Nonempty (T j))                   (SoundT.nonempty)

`Att.sound` and `Der.sound` are `Att.mapOut` and `Der.mapOut` at a
proposition: the recursion over an attempt is written once.  `Sound` is not
`SoundT` with another sort because its premises, taken by membership,
cannot be given from the premises of a node when `T` is data: that would
ask to tell two positions of one judgment apart by a proof of `p ∈ ps`.

Functions on attempts are written for every `o`, since Lean's structural
recursion needs the index to be a variable.

Core Lean only.
-/

import ProofTools.Audit.FileBound
namespace ProofTools.Explore

/-- **A proof system**: judgments, moves, and the premises a move asks for
at a judgment (or why it does not apply). -/
structure ProofSystem where
  /-- What is derived. -/
  Judg : Type
  /-- A rule, named by its data. -/
  Move : Type
  /-- The premises, or why the move does not apply. -/
  step : Move → Judg → Except String (List Judg)

mutual
/-- **An attempt** at `j`.  With `o = true` open goals are allowed. -/
inductive Att (S : ProofSystem) : Bool → S.Judg → Type
  /-- An open goal. -/
  | goal {j : S.Judg} : Att S true j
  /-- A move `m` at `j`, its premises `ps` as `S.step` gives them, and an
  attempt at each. -/
  | node {o : Bool} {j : S.Judg} (m : S.Move) (ps : List S.Judg)
      (h : S.step m j = .ok ps) (ds : Atts S o ps) : Att S o j
/-- Attempts at each judgment of a list. -/
inductive Atts (S : ProofSystem) : Bool → List S.Judg → Type
  | nil {o : Bool} : Atts S o []
  | cons {o : Bool} {p : S.Judg} {ps : List S.Judg} (d : Att S o p) (ds : Atts S o ps) :
      Atts S o (p :: ps)
end

/-- **A derivation**: an attempt with no open goal. -/
abbrev Der (S : ProofSystem) (j : S.Judg) : Type := Att S false j

universe u v

variable {S : ProofSystem}

mutual
/-- The open goals, leftmost first. -/
def Att.goals : {o : Bool} → {j : S.Judg} → Att S o j → List S.Judg
  | _, j, .goal => [j]
  | _, _, .node _ _ _ ds => ds.goals
/-- The open goals of a list of attempts, leftmost first. -/
def Atts.goals : {o : Bool} → {ps : List S.Judg} → Atts S o ps → List S.Judg
  | _, _, .nil => []
  | _, _, .cons d ds => d.goals ++ ds.goals
end

mutual
/-- The number of moves. -/
def Att.size : {o : Bool} → {j : S.Judg} → Att S o j → Nat
  | _, _, .goal => 0
  | _, _, .node _ _ _ ds => ds.size + 1
/-- The number of moves in a list of attempts. -/
def Atts.size : {o : Bool} → {ps : List S.Judg} → Atts S o ps → Nat
  | _, _, .nil => 0
  | _, _, .cons d ds => d.size + ds.size
end

@[simp] theorem Att.goals_goal {j : S.Judg} : (Att.goal : Att S true j).goals = [j] := by
  simp [Att.goals]

@[simp] theorem Att.goals_node {o : Bool} {j : S.Judg} (m : S.Move) (ps : List S.Judg)
    (h : S.step m j = .ok ps) (ds : Atts S o ps) : (Att.node m ps h ds).goals = ds.goals := by
  simp [Att.goals]

@[simp] theorem Atts.goals_nil {o : Bool} : (Atts.nil : Atts S o []).goals = [] := by
  simp [Atts.goals]

@[simp] theorem Atts.goals_cons {o : Bool} {p : S.Judg} {ps : List S.Judg} (d : Att S o p)
    (ds : Atts S o ps) : (Atts.cons d ds).goals = d.goals ++ ds.goals := by
  simp [Atts.goals]

/-- Every premise open. -/
def Atts.open : (ps : List S.Judg) → Atts S true ps
  | [] => .nil
  | _ :: ps => .cons .goal (Atts.open ps)

@[simp] theorem Atts.goals_open : (ps : List S.Judg) → (Atts.open ps : Atts S true ps).goals = ps
  | [] => by simp [Atts.open]
  | p :: ps => by simp [Atts.open, Atts.goals_open ps]

/-! ## A derivation is an attempt -/

mutual
/-- An attempt with or without open goals, as one where they are allowed. -/
def Att.toAtt : {o : Bool} → {j : S.Judg} → Att S o j → Att S true j
  | _, _, .goal => .goal
  | _, _, .node m ps h ds => .node m ps h ds.toAtts
/-- `Att.toAtt` on a list. -/
def Atts.toAtts : {o : Bool} → {ps : List S.Judg} → Atts S o ps → Atts S true ps
  | _, _, .nil => .nil
  | _, _, .cons d ds => .cons d.toAtt ds.toAtts
end

private theorem Att.node_heq {o o' : Bool} {j : S.Judg} (m : S.Move) (ps : List S.Judg)
    (h : S.step m j = .ok ps) (e : o = o') {ds : Atts S o ps} {ds' : Atts S o' ps}
    (hd : HEq ds ds') : HEq (Att.node m ps h ds) (Att.node m ps h ds') := by
  subst e
  cases hd
  rfl

private theorem Atts.cons_heq {o o' : Bool} {p : S.Judg} {ps : List S.Judg} (e : o = o')
    {d : Att S o p} {d' : Att S o' p} {ds : Atts S o ps} {ds' : Atts S o' ps}
    (hd : HEq d d') (hds : HEq ds ds') : HEq (Atts.cons d ds) (Atts.cons d' ds') := by
  subst e
  cases hd
  cases hds
  rfl

private theorem Atts.nil_heq {o o' : Bool} (e : o = o') :
    HEq (Atts.nil : Atts S o []) (Atts.nil : Atts S o' []) := by
  subst e
  rfl

mutual
private theorem Att.toAtt_heq : {o : Bool} → {j : S.Judg} → (d : Att S o j) → o = true →
    HEq d.toAtt d
  | _, _, .goal, _ => HEq.rfl
  | _, _, .node m ps h ds, ho => Att.node_heq m ps h ho.symm (Atts.toAtts_heq ds ho)
private theorem Atts.toAtts_heq : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    o = true → HEq ds.toAtts ds
  | _, _, .nil, ho => Atts.nil_heq ho.symm
  | _, _, .cons d ds, ho => Atts.cons_heq ho.symm (Att.toAtt_heq d ho) (Atts.toAtts_heq ds ho)
end

/-- On an attempt, `toAtt` changes nothing. -/
@[simp] theorem Att.toAtt_eq {j : S.Judg} (d : Att S true j) : d.toAtt = d :=
  eq_of_heq (Att.toAtt_heq d rfl)

@[simp] theorem Atts.toAtts_eq {ps : List S.Judg} (ds : Atts S true ps) : ds.toAtts = ds :=
  eq_of_heq (Atts.toAtts_heq ds rfl)

mutual
@[simp] theorem Att.goals_toAtt : {o : Bool} → {j : S.Judg} → (d : Att S o j) →
    d.toAtt.goals = d.goals
  | _, _, .goal => rfl
  | _, _, .node _ _ _ ds => by simp [Att.toAtt, Atts.goals_toAtts ds]
@[simp] theorem Atts.goals_toAtts : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    ds.toAtts.goals = ds.goals
  | _, _, .nil => rfl
  | _, _, .cons d ds => by simp [Atts.toAtts, Att.goals_toAtt d, Atts.goals_toAtts ds]
end

mutual
/-- An attempt with no open goal left, as a derivation. -/
def Att.toDer : {o : Bool} → {j : S.Judg} → (d : Att S o j) → d.goals = [] → Der S j
  | _, _, .goal, h => by simp at h
  | _, _, .node m ps hs ds, h => .node m ps hs (ds.toDers (by simpa using h))
/-- `Att.toDer` on a list. -/
def Atts.toDers : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) → ds.goals = [] →
    Atts S false ps
  | _, _, .nil, _ => .nil
  | _, _, .cons d ds, h =>
    .cons (d.toDer (by simp at h; exact h.1)) (ds.toDers (by simp at h; exact h.2))
end

mutual
/-- A derivation has no open goal. -/
theorem Att.goals_of_closed : {o : Bool} → {j : S.Judg} → (d : Att S o j) → o = false →
    d.goals = []
  | _, _, .goal, ho => by cases ho
  | _, _, .node _ _ _ ds, ho => by simp [Atts.goals_of_closed ds ho]
theorem Atts.goals_of_closed : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    o = false → ds.goals = []
  | _, _, .nil, _ => rfl
  | _, _, .cons d ds, ho => by simp [Att.goals_of_closed d ho, Atts.goals_of_closed ds ho]
end

@[simp] theorem Der.goals {j : S.Judg} (d : Der S j) : Att.goals d = [] :=
  Att.goals_of_closed d rfl

/-! ## One thing for each judgment of a list -/

/-- **One `T a` for each member `a` of a list, by position**: `Each T [a, b]`
is `T a ×' T b ×' PUnit`.  With `T` into `Prop` it says that `T` holds of
every member; with `T` into `Type` it holds one piece of data for each
position, so two positions with one member keep their own. -/
def Each {α : Type v} (T : α → Sort u) : List α → Sort (max 1 u)
  | [] => PUnit
  | a :: as => T a ×' Each T as

/-- One for each member of `xs ++ ys`, as one for each of `xs` and one for
each of `ys`. -/
def Each.split {α : Type v} {T : α → Sort u} : (xs : List α) → {ys : List α} →
    Each T (xs ++ ys) → Each T xs ×' Each T ys
  | [], _, e => ⟨⟨⟩, e⟩
  | _ :: xs, _, ⟨t, e⟩ => ⟨⟨t, (Each.split xs e).1⟩, (Each.split xs e).2⟩

/-- From one for each member, taken by membership.  (With `T` into `Type`,
two positions with one member are given the same.) -/
def Each.ofMem {α : Type v} {T : α → Sort u} : {as : List α} → (∀ a ∈ as, T a) → Each T as
  | [], _ => ⟨⟩
  | a :: _, h => ⟨h a List.mem_cons_self, Each.ofMem fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

/-- For a proposition: it holds of each member. -/
theorem Each.mem {α : Type v} {D : α → Prop} : {as : List α} → Each D as → ∀ a ∈ as, D a
  | [], _ => fun _ h => nomatch h
  | _ :: _, ⟨h, e⟩ => fun _ hb =>
    (List.mem_cons.mp hb).elim (fun eq => eq ▸ h) (Each.mem e _)

/-- Where each member has one, there is one for each. -/
theorem Each.nonempty {α : Type v} {T : α → Sort u} : {as : List α} →
    (∀ a ∈ as, Nonempty (T a)) → Nonempty (Each T as)
  | [], _ => ⟨⟨⟩⟩
  | a :: _, h =>
    let ⟨t⟩ := h a List.mem_cons_self
    let ⟨e⟩ := Each.nonempty fun b hb => h b (List.mem_cons_of_mem _ hb)
    ⟨⟨t, e⟩⟩

/-! ## Soundness of the moves, and the map out -/

/-- **Soundness of the moves** for a family `T` over the judgments, into any
sort: where a move applies, from one `T` for each premise, by position, a
`T` for its conclusion.  With `T` a type of derivations this is a function:
each rule of the calculus, applied. -/
def ProofSystem.SoundT (S : ProofSystem) (T : S.Judg → Sort u) :=
  ∀ m j ps, S.step m j = .ok ps → Each T ps → T j

/-- **Soundness of the moves** for a proposition `D`, the premises taken by
membership: where a move applies and its premises hold, its conclusion
holds.  It is `S.SoundT D` (`soundT_iff_sound`). -/
def ProofSystem.Sound (S : ProofSystem) (D : S.Judg → Prop) : Prop :=
  ∀ m j ps, S.step m j = .ok ps → (∀ p ∈ ps, D p) → D j

variable {D : S.Judg → Prop} {T : S.Judg → Sort u}

/-- Soundness by membership gives soundness by position. -/
theorem ProofSystem.Sound.soundT (hS : S.Sound D) : S.SoundT D :=
  fun m j ps h e => hS m j ps h e.mem

/-- For a proposition, soundness by position gives soundness by membership. -/
theorem ProofSystem.SoundT.sound (hS : S.SoundT D) : S.Sound D :=
  fun m j ps h hps => hS m j ps h (Each.ofMem hps)

/-- **For a proposition the two are one notion.** -/
theorem ProofSystem.soundT_iff_sound : S.SoundT D ↔ S.Sound D :=
  ⟨ProofSystem.SoundT.sound, ProofSystem.Sound.soundT⟩

/-- Moves sound for a family are sound for its being inhabited. -/
theorem ProofSystem.SoundT.nonempty (hS : S.SoundT T) : S.Sound (fun j => Nonempty (T j)) :=
  fun m j ps h hps =>
    let ⟨e⟩ := Each.nonempty hps
    ⟨hS m j ps h e⟩

mutual
/-- `Att.mapOut` with its result as a list of one.  (Lean asks the results
of a mutual definition to be in one universe; `T j` is in `Sort u` and
`Each T ps` in `Sort (max 1 u)`.) -/
def Att.mapOutAux (hS : S.SoundT T) : {o : Bool} → {j : S.Judg} → (d : Att S o j) →
    Each T d.goals → Each T [j]
  | _, _, .goal, g => g
  | _, _, .node m ps h ds, g => ⟨hS m _ ps h (Atts.mapOut hS ds g), ⟨⟩⟩
/-- `Att.mapOut` on a list: from one `T` for each open goal, one for each
premise. -/
def Atts.mapOut (hS : S.SoundT T) : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    Each T ds.goals → Each T ps
  | _, _, .nil, _ => ⟨⟩
  | _, _, .cons d ds, g =>
    ⟨(Att.mapOutAux hS d (Each.split d.goals g).1).1, Atts.mapOut hS ds (Each.split d.goals g).2⟩
end

/-- **An attempt is a derived rule**, from its open goals to its root: from
one `T` for each open goal, by position, a `T` for the root.  With `T` a
type of derivations, it carries the attempt into them. -/
def Att.mapOut (hS : S.SoundT T) {o : Bool} {j : S.Judg} (d : Att S o j) (g : Each T d.goals) :
    T j :=
  (Att.mapOutAux hS d g).1

@[simp] theorem Att.mapOut_goal (hS : S.SoundT T) {j : S.Judg} (g : Each T [j]) :
    Att.mapOut hS (Att.goal : Att S true j) g = g.1 := rfl

@[simp] theorem Att.mapOut_node (hS : S.SoundT T) {o : Bool} {j : S.Judg} (m : S.Move)
    (ps : List S.Judg) (h : S.step m j = .ok ps) (ds : Atts S o ps) (g : Each T ds.goals) :
    Att.mapOut hS (Att.node m ps h ds) g = hS m j ps h (Atts.mapOut hS ds g) := rfl

@[simp] theorem Atts.mapOut_nil (hS : S.SoundT T) {o : Bool} (g : Each T ([] : List S.Judg)) :
    Atts.mapOut hS (Atts.nil : Atts S o []) g = ⟨⟩ := rfl

@[simp] theorem Atts.mapOut_cons (hS : S.SoundT T) {o : Bool} {p : S.Judg} {ps : List S.Judg}
    (d : Att S o p) (ds : Atts S o ps) (g : Each T (d.goals ++ ds.goals)) :
    Atts.mapOut hS (Atts.cons d ds) g =
      ⟨Att.mapOut hS d (Each.split d.goals g).1, Atts.mapOut hS ds (Each.split d.goals g).2⟩ :=
  rfl

/-- **What a derivation derives, mapped out**: with `T` a type of
derivations, the derivation in `T`. -/
def Der.mapOut (hS : S.SoundT T) {j : S.Judg} (d : Der S j) : T j :=
  Att.mapOut hS d ((Der.goals d).symm ▸ PUnit.unit)

/-! ## At a proposition -/

/-- **An attempt is a derived rule**, from its open goals to its root:
`Att.mapOut` at a proposition, the goals taken by membership. -/
theorem Att.sound (hS : S.Sound D) : {o : Bool} → {j : S.Judg} → (d : Att S o j) →
    (∀ g ∈ d.goals, D g) → D j :=
  fun d hg => Att.mapOut hS.soundT d (Each.ofMem hg)

theorem Atts.sound (hS : S.Sound D) : {o : Bool} → {ps : List S.Judg} → (ds : Atts S o ps) →
    (∀ g ∈ ds.goals, D g) → ∀ p ∈ ps, D p :=
  fun ds hg => (Atts.mapOut hS.soundT ds (Each.ofMem hg)).mem

/-- **What a derivation derives holds**: `Der.mapOut` at a proposition. -/
theorem Der.sound (hS : S.Sound D) {j : S.Judg} (d : Der S j) : D j :=
  Der.mapOut hS.soundT d

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
