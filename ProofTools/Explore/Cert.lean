/-
# `ProofTools.Explore.Cert`: a tree of moves as a certificate

A derivation `Der S j` writes, at each node, the move, the premises and the
equation `S.step m j = .ok ps`.  Its **tree of moves** keeps the moves and
the shape and nothing else: no judgment, no index, no proof.  It is a rose
tree of the library (`ProofTools.Zipper.Rose`) with the moves at its nodes
and nothing on its edges,

    Cert S := Zip.RTree Unit S.Move

so it is compared, printed, drawn and walked by what the library has for
rose trees (`RTree.beq`, proved lawful; `Repr`; `RTree.drawWith`; Huet's
zipper), with nothing written here.  `Cert.mk m cs` is a node from a list of
trees.

**The checker** is `step` at the root, then each child at its premise:

    Cert.check : S.Judg → Cert S → Bool

structural in the tree, so the kernel evaluates it; it builds nothing, and
keeps no position.  A tree that checks is a derivation, and a derivation's
tree checks (PROVED here, for every proof system):

    Der.ofCert j c h : Der S j                 for h : c.check j = true
    Att.cert d : Cert S                        for d : Der S j
    d.cert.check j = true                                            (Att.check_cert)
    (Der.ofCert j c h).cert = c                                      (Att.cert_ofCert)
    Der.ofCert j d.cert h = d                                        (Der.ofCert_cert)
    d.cert = d'.cert → d = d'                  for d d' : Der S j    (Att.cert_inj)

So the derivations of `j` and the trees of moves that check at `j` are the
same things, each computed from the other.  With the soundness of the moves
for a family `T`, into any sort, a tree that checks gives `T j`: the
certifier `Cert.certifier` of `ProofTools.Explore.Certify`, beside the one
whose certificate is a script.

**No recursion over attempts is written here.**  `Att.cert` is the library's
map out (`Der.mapOut`) at the constant family `fun _ => Cert S`, the moves
being sound for it by `Cert.moves`: a move over the trees of its premises is
a node.  That the tree checks is read off the map out at the family of the
trees that check (`Cert.checked`), by the naturality of the map out
(`Der.mapOut_map`).  An attempt with open goals has no tree of its own, and
`Cert` no leaf for an open goal: it is `Att.mapOut Cert.moves d`, a function
from one tree for each open goal to the tree of the whole.

`Cert.moves` makes no use of the node's equation, so the kernel evaluates
`d.cert` on every derivation, also where an instance's soundness into a type
is stopped by a cast (`eqByDecide`, `ProofTools.Explore.Tactic`).

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Explore.System
import ProofTools.Zipper.RoseRender

namespace ProofTools.Explore

universe u

variable {S : ProofSystem}

/-- **A tree of moves**: a rose tree with a move at each node and nothing on
its edges. -/
abbrev Cert (S : ProofSystem) : Type := Zip.RTree Unit S.Move

/-- A tree of moves from the move at its root and the trees of its premises. -/
def Cert.mk (m : S.Move) (cs : List (Cert S)) : Cert S := .node m (cs.map fun c => ((), c))

/-! ## The checker -/

mutual
/-- **The checker of trees of moves**: `step` at the root, then each child at
its premise, as many children as premises. -/
def Cert.check : (j : S.Judg) → Cert S → Bool
  | j, .node m cs =>
    match S.step m j with
    | .ok ps => Cert.checkL ps cs
    | .error _ => false
/-- `Cert.check` on a list: each tree at its judgment, by position. -/
def Cert.checkL : List S.Judg → List (Unit × Cert S) → Bool
  | [], [] => true
  | p :: ps, (_, c) :: cs => Cert.check p c && Cert.checkL ps cs
  | _, _ => false
end

theorem Cert.check_node {m : S.Move} {j : S.Judg} {ps : List S.Judg} (hs : S.step m j = .ok ps)
    (cs : List (Unit × Cert S)) : Cert.check j (.node m cs) = Cert.checkL ps cs := by
  rw [Cert.check, hs]

theorem Cert.checkL_of_check {m : S.Move} {j : S.Judg} {ps : List S.Judg}
    {cs : List (Unit × Cert S)} (hs : S.step m j = .ok ps)
    (h : Cert.check j (.node m cs) = true) : Cert.checkL ps cs = true :=
  (Cert.check_node hs cs).symm.trans h

theorem Cert.not_check_of_error {m : S.Move} {j : S.Judg} {e : String}
    {cs : List (Unit × Cert S)} (hs : S.step m j = .error e) :
    ¬ Cert.check j (.node m cs) = true := by
  rw [Cert.check, hs]
  exact Bool.false_ne_true

theorem Cert.checkL_head {p : S.Judg} {ps : List S.Judg} {u : Unit} {c : Cert S}
    {cs : List (Unit × Cert S)} (h : Cert.checkL (p :: ps) ((u, c) :: cs) = true) :
    Cert.check p c = true := by
  rw [Cert.checkL] at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem Cert.checkL_tail {p : S.Judg} {ps : List S.Judg} {u : Unit} {c : Cert S}
    {cs : List (Unit × Cert S)} (h : Cert.checkL (p :: ps) ((u, c) :: cs) = true) :
    Cert.checkL ps cs = true := by
  rw [Cert.checkL] at h
  exact (Bool.and_eq_true_iff.mp h).2

/-! ## From a tree that checks, the derivation -/

mutual
/-- **The derivation a tree of moves is**, where `Cert.check` accepts it:
at each node the premises `step` computes, and its equation. -/
def Der.ofCert : (j : S.Judg) → (c : Cert S) → Cert.check j c = true → Der S j
  | j, .node m cs, h =>
    match hs : S.step m j with
    | .ok ps => .node m ps hs (Atts.ofCerts ps cs (Cert.checkL_of_check hs h))
    | .error _ => absurd h (Cert.not_check_of_error hs)
/-- `Der.ofCert` on a list. -/
def Atts.ofCerts : (ps : List S.Judg) → (cs : List (Unit × Cert S)) → Cert.checkL ps cs = true →
    Atts S false ps
  | [], [], _ => .nil
  | p :: ps, (_, c) :: cs, h =>
    .cons (Der.ofCert p c (Cert.checkL_head h)) (Atts.ofCerts ps cs (Cert.checkL_tail h))
  | [], _ :: _, h => absurd h (by simp [Cert.checkL])
  | _ :: _, [], h => absurd h (by simp [Cert.checkL])
end

/-- `Der.ofCert` at a node, with the premises named. -/
theorem Der.ofCert_node {m : S.Move} {j : S.Judg} {ps : List S.Judg} {cs : List (Unit × Cert S)}
    (hs : S.step m j = .ok ps) (h : Cert.check j (.node m cs) = true) :
    Der.ofCert j (.node m cs) h =
      .node m ps hs (Atts.ofCerts ps cs (Cert.checkL_of_check hs h)) := by
  unfold Der.ofCert
  split
  · next ps' hs' =>
    cases Except.ok.inj (hs.symm.trans hs')
    rfl
  · next e hs' => cases hs.symm.trans hs'

/-- `Der.ofCert` at equal trees. -/
theorem Der.ofCert_congr {j : S.Judg} {c c' : Cert S} (e : c = c') (h : Cert.check j c = true)
    (h' : Cert.check j c' = true) : Der.ofCert j c h = Der.ofCert j c' h' := by
  subst e
  rfl

/-! ## From a derivation, its tree: the map out at a constant family -/

/-- **The moves are sound for trees of moves**: a move over the trees of its
premises is a node.  (The soundness of the library, `SoundT`, at the
constant family; it makes no use of the equation.) -/
def Cert.moves : S.SoundT (fun _ => Cert S) :=
  fun m _ _ _ e => .node m (e.list fun _ c => ((), c))

/-- **The tree of moves of a derivation**: the library's map out at
`Cert.moves`. -/
def Att.cert {j : S.Judg} (d : Der S j) : Cert S := Der.mapOut Cert.moves d

/-- The tree of moves of a node, whatever is given for the open goals of
its premises (they have none). -/
theorem Att.cert_node {m : S.Move} {j : S.Judg} {ps : List S.Judg} (hs : S.step m j = .ok ps)
    (ds : Atts S false ps) (g : Each (fun _ => Cert S) ds.goals) :
    Att.cert (.node m ps hs ds) =
      .node m ((Atts.mapOut Cert.moves ds g).list fun _ c => ((), c)) :=
  (Der.mapOut_eq Cert.moves (.node m ps hs ds) g).symm

/-! ## A derivation's tree checks -/

theorem Cert.checkL_list : {ps : List S.Judg} →
    (e : Each (fun j => {c : Cert S // Cert.check j c = true}) ps) →
    Cert.checkL ps ((e.map fun _ c => c.1).list fun _ c => ((), c)) = true
  | [], _ => by simp [Each.list, Cert.checkL]
  | _ :: _, ⟨c, e⟩ => by simp [Each.map, Each.list, Cert.checkL, c.2, Cert.checkL_list e]

/-- **The moves are sound for the trees that check**: the node of
`Cert.moves`, with the proof that it checks. -/
def Cert.checked : S.SoundT (fun j => {c : Cert S // Cert.check j c = true}) :=
  fun m j ps h e =>
    ⟨Cert.moves m j ps h (e.map fun _ c => c.1), (Cert.check_node h _).trans (Cert.checkL_list e)⟩

/-- **A derivation's tree of moves checks.**  No recursion over the
derivation: the map out at `Cert.checked` gives a tree that checks, and by
naturality (`Der.mapOut_map`) it is `d.cert`. -/
theorem Att.check_cert {j : S.Judg} (d : Der S j) : Cert.check j d.cert = true :=
  have e : (Der.mapOut Cert.checked d).1 = d.cert :=
    Der.mapOut_map (hS := Cert.checked) (hS' := Cert.moves) (f := fun _ c => c.1)
      (fun _ _ _ _ _ => rfl) d
  e ▸ (Der.mapOut Cert.checked d).2

/-! ## The two round trips -/

mutual
/-- **A tree that checks is the tree of its derivation.** -/
theorem Att.cert_ofCert : (c : Cert S) → (j : S.Judg) → (h : Cert.check j c = true) →
    (Der.ofCert j c h).cert = c
  | .node m cs, j, h => by
    match hs : S.step m j with
    | .ok ps =>
      rw [Der.ofCert_node hs h, Att.cert_node hs _ (Each.ofMem fun _ _ => .node m [])]
      exact congrArg (Zip.RTree.node m) (Atts.certs_ofCerts cs ps _ _)
    | .error _ => exact absurd h (Cert.not_check_of_error hs)
/-- `Att.cert_ofCert` on a list. -/
theorem Atts.certs_ofCerts : (cs : List (Unit × Cert S)) → (ps : List S.Judg) →
    (h : Cert.checkL ps cs = true) → (g : Each (fun _ => Cert S) (Atts.ofCerts ps cs h).goals) →
    (Atts.mapOut Cert.moves (Atts.ofCerts ps cs h) g).list (fun _ c => ((), c)) = cs
  | [], [], _, _ => rfl
  | (u, c) :: cs, p :: ps, h, g => by
    have key : ∀ g : Each (fun _ => Cert S) (Att.goals (Der.ofCert p c (Cert.checkL_head h)) ++
          (Atts.ofCerts ps cs (Cert.checkL_tail h)).goals),
        (Atts.mapOut Cert.moves (.cons (Der.ofCert p c (Cert.checkL_head h))
          (Atts.ofCerts ps cs (Cert.checkL_tail h))) g).list (fun _ c => ((), c)) =
            (u, c) :: cs := by
      intro g
      simp only [Atts.mapOut_cons, Each.list, Der.mapOut_eq, Atts.certs_ofCerts cs ps]
      exact congrArg (fun x => ((), x) :: cs) (Att.cert_ofCert c p _)
    exact key g
  | _ :: _, [], h, _ => absurd h (by simp [Cert.checkL])
  | [], _ :: _, h, _ => absurd h (by simp [Cert.checkL])
end

private theorem Atts.cons_congr {o : Bool} {p : S.Judg} {ps : List S.Judg} {d d' : Att S o p}
    {ds ds' : Atts S o ps} (h₁ : d = d') (h₂ : ds = ds') : Atts.cons d ds = Atts.cons d' ds' :=
  h₁ ▸ h₂ ▸ rfl

/-- `Der.ofCert_cert`, by induction on a bound on the number of moves.  (A
derivation is matched as it stands: only a structural recursion needs the
index `o` of `Att S o j` to be a variable.) -/
theorem Der.ofCert_cert_aux : (n : Nat) → {j : S.Judg} → (d : Der S j) → Att.size d ≤ n →
    (g : Each (fun _ => Cert S) (Att.goals d)) →
    (h : Cert.check j (Att.mapOut Cert.moves d g) = true) →
    Der.ofCert j (Att.mapOut Cert.moves d g) h = d
  | 0, _, .node _ _ _ _, hn, _, _ => absurd hn (Nat.not_succ_le_zero _)
  | n + 1, j, .node m ps hs ds, hn, g, h => by
    have inner : ∀ (qs : List S.Judg) (es : Atts S false qs), es.size ≤ n →
        ∀ (g : Each (fun _ => Cert S) es.goals)
          (h' : Cert.checkL qs ((Atts.mapOut Cert.moves es g).list fun _ c => ((), c)) = true),
          Atts.ofCerts qs ((Atts.mapOut Cert.moves es g).list fun _ c => ((), c)) h' = es := by
      intro qs
      induction qs with
      | nil =>
        intro es _ g h'
        match es with
        | .nil => rfl
      | cons q qs ih =>
        intro es hes g h'
        match es, hes, g, h' with
        | .cons e es', hes, g, h' =>
          exact Atts.cons_congr
            (Der.ofCert_cert_aux n e (Nat.le_trans (Nat.le_add_right _ _) hes) _ _)
            (ih es' (Nat.le_trans (Nat.le_add_left _ _) hes) _ _)
    have e := Der.ofCert_node hs (cs := (Atts.mapOut Cert.moves ds g).list fun _ c => ((), c)) h
    exact e.trans (congrArg (Att.node m ps hs) (inner ps ds (Nat.le_of_succ_le_succ hn) g _))

/-- **A derivation is the derivation of its tree of moves.** -/
theorem Der.ofCert_cert {j : S.Judg} (d : Der S j) (h : Cert.check j d.cert = true) :
    Der.ofCert j d.cert h = d :=
  Der.ofCert_cert_aux (Att.size d) d (Nat.le_refl _) _ h

/-- **A derivation is determined by its tree of moves.** -/
theorem Att.cert_inj {j : S.Judg} {d d' : Der S j} (h : d.cert = d'.cert) : d = d' :=
  (Der.ofCert_cert d (Att.check_cert d)).symm.trans
    ((Der.ofCert_congr h _ _).trans (Der.ofCert_cert d' (Att.check_cert d')))

end ProofTools.Explore

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
