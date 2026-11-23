/-
# `ProofTools.Zipper.RoseUpdate`: changing a rose tree at an address

`t.updateAt g a` replaces the subtree at address `a` (first child along each
edge, as `get?`) by `g` of it; if there is no node at `a`, nothing changes.
`t.at? a` is the label at `a`.

Results (all PROVED):

    t.get? (a ++ c) = (t.get? a).bind fun s => s.get? c            (RTree.get?_append)
    (t.updateAt g a).get? (a ++ c) = (t.get? a).bind fun s => (g s).get? c
                                                                   (RTree.get?_updateAt_append)
    ¬ a <+: b  →  (t.updateAt g a).at? b = t.at? b                 (RTree.at_updateAt_of_not_prefix)

Walking `a ++ c` is walking `a`, then `c`; below `a`, the new tree is `g` of
the old subtree; away from `a`, labels are unchanged.  And, for a list of
children (`updFirst k g` applies `g` to the value of the first pair with key
`k`):

    find? k (updFirst k g cs) = (find? k cs).map g                 (find?_updFirst_self)
    k' ≠ k  →  find? k' (updFirst k g cs) = find? k' cs            (find?_updFirst_ne)
    find? k cs = none  →
      find? k' (cs ++ [(k, b)]) = if k' = k then some b else find? k' cs
                                                                   (find?_append_new)

Core Lean only.
-/
import ProofTools.Audit.FileBound
import ProofTools.Zipper.Rose

namespace ProofTools.Zip

universe u v w

section Upd

variable {κ : Type u} {β : Type w} [DecidableEq κ]

/-- Apply `g` to the value of the first pair with key `k`. -/
def updFirst (k : κ) (g : β → β) : List (κ × β) → List (κ × β)
  | [] => []
  | (k', b) :: cs => if k' = k then (k', g b) :: cs else (k', b) :: updFirst k g cs

theorem find?_updFirst_self {k : κ} {g : β → β} :
    ∀ cs : List (κ × β), find? k (updFirst k g cs) = (find? k cs).map g
  | [] => rfl
  | (k', b) :: cs => by
    by_cases h : k' = k
    · simp [updFirst, find?, h]
    · simp [updFirst, find?, h, find?_updFirst_self cs]

theorem find?_updFirst_ne {k k' : κ} {g : β → β} (hk : k' ≠ k) :
    ∀ cs : List (κ × β), find? k' (updFirst k g cs) = find? k' cs
  | [] => rfl
  | (k'', b) :: cs => by
    by_cases h : k'' = k
    · subst h
      have : k'' ≠ k' := fun e => hk e.symm
      simp [updFirst, find?, this]
    · by_cases h' : k'' = k'
      · subst h'
        simp [updFirst, find?, hk]
      · simp [updFirst, find?, h, h', find?_updFirst_ne hk cs]

/-- Appending a pair with a new key `k` makes `k` found, and changes nothing else. -/
theorem find?_append_new {k : κ} {b : β} :
    ∀ {cs : List (κ × β)}, find? k cs = none → ∀ k', find? k' (cs ++ [(k, b)]) =
      if k' = k then some b else find? k' cs
  | [], _, k' => by by_cases h : k = k' <;> simp [find?, h, eq_comm]
  | (k'', b') :: cs, h, k' => by
    simp only [find?] at h
    by_cases hk : k'' = k
    · simp [hk] at h
    · simp only [hk, if_false] at h
      by_cases hk' : k'' = k'
      · subst hk'
        rw [if_neg hk]
        simp [find?]
      · simp only [List.cons_append, find?, hk', if_false]
        exact find?_append_new h k'

end Upd

namespace RTree

variable {κ : Type u} {α : Type v} [DecidableEq κ]

/-- Replace the subtree at address `a` by `g` of it. -/
def updateAt (g : RTree κ α → RTree κ α) : RTree κ α → List κ → RTree κ α
  | t, [] => g t
  | .node x cs, k :: a => .node x (updFirst k (fun s => updateAt g s a) cs)

/-- The label at an address. -/
def at? (t : RTree κ α) (a : List κ) : Option α := (t.get? a).map label

theorem get?_append : ∀ (t : RTree κ α) (a c : List κ),
    t.get? (a ++ c) = (t.get? a).bind fun s => s.get? c
  | t, [], c => rfl
  | .node x cs, k :: a, c => by
    simp only [List.cons_append, get?, children, Option.bind_assoc]
    congr 1
    funext s
    exact get?_append s a c

theorem get?_updateAt_append (g : RTree κ α → RTree κ α) :
    ∀ (t : RTree κ α) (a c : List κ),
      (t.updateAt g a).get? (a ++ c) = (t.get? a).bind fun s => (g s).get? c
  | t, [], c => rfl
  | .node x cs, k :: a, c => by
    simp only [updateAt, List.cons_append, get?, children, find?_updFirst_self,
      Option.bind_map, Option.bind_assoc]
    congr 1
    funext s
    exact get?_updateAt_append g s a c

/-- Away from `a`, labels are unchanged (`g` may change the subtree at `a`). -/
theorem at_updateAt_of_not_prefix (g : RTree κ α → RTree κ α) :
    ∀ (t : RTree κ α) (a b : List κ), ¬ a <+: b → (t.updateAt g a).at? b = t.at? b
  | _, [], b, h => absurd (List.nil_prefix) h
  | .node x cs, k :: a, [], _ => rfl
  | .node x cs, k :: a, k' :: b, h => by
    simp only [at?, updateAt, get?, children]
    by_cases hk : k' = k
    · subst hk
      have h' : ¬ a <+: b := fun hp => h (List.prefix_cons_inj _ |>.2 hp)
      rw [find?_updFirst_self]
      cases hf : find? k' cs with
      | none => rfl
      | some s => exact at_updateAt_of_not_prefix g s a b h'
    · rw [find?_updFirst_ne hk]

end RTree

end ProofTools.Zip

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
