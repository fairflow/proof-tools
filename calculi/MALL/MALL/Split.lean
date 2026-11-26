/-
Two divisions of one multiset, refined: where `Γ ++ Δ` is a permutation of
`Θ₁ ++ Θ₂`, the four parts `Γ ∩ Θ₁`, `Γ ∩ Θ₂`, `Δ ∩ Θ₁`, `Δ ∩ Θ₂`, computed.
Used where a rule that divides its context (⊗) meets a sequent that is
itself divided in two (interpolation).  Theory file: it ends with its
bound on axioms.
-/
import MALL.Perm

namespace MALL

open List

/-- The four parts of two divisions of one multiset. -/
structure Split4 (Γ Δ Θ₁ Θ₂ : List Form) where
  /-- The part of `Γ` in `Θ₁`. -/
  Γ₁ : List Form
  /-- The part of `Γ` in `Θ₂`. -/
  Γ₂ : List Form
  /-- The part of `Δ` in `Θ₁`. -/
  Δ₁ : List Form
  /-- The part of `Δ` in `Θ₂`. -/
  Δ₂ : List Form
  hΓ : Γ ~ Γ₁ ++ Γ₂
  hΔ : Δ ~ Δ₁ ++ Δ₂
  h₁ : Θ₁ ~ Γ₁ ++ Δ₁
  h₂ : Θ₂ ~ Γ₂ ++ Δ₂

/-- **The four parts, computed**: each formula of `Γ` goes to `Θ₁` if it
is there, and otherwise to `Θ₂`. -/
def split4 : (Γ Δ Θ₁ Θ₂ : List Form) → Γ ++ Δ ~ Θ₁ ++ Θ₂ → Split4 Γ Δ Θ₁ Θ₂
  | [], _, Θ₁, Θ₂, h => ⟨[], [], Θ₁, Θ₂, .refl _, h, .refl _, .refl _⟩
  | a :: Γ, Δ, Θ₁, Θ₂, h =>
    if ha : a ∈ Θ₁ then
      have hp := perm_cons_erase ha
      let s := split4 Γ Δ (Θ₁.erase a) Θ₂ (by
        have h' : a :: (Γ ++ Δ) ~ Θ₁ ++ Θ₂ := h
        perm_count [h', hp])
      ⟨a :: s.Γ₁, s.Γ₂, s.Δ₁, s.Δ₂,
        by have := s.hΓ; show a :: Γ ~ a :: s.Γ₁ ++ s.Γ₂; perm_count [this],
        s.hΔ,
        by have := s.h₁; show Θ₁ ~ a :: s.Γ₁ ++ s.Δ₁; perm_count [this, hp],
        s.h₂⟩
    else
      have ha₂ : a ∈ Θ₂ := by
        have : a ∈ Θ₁ ++ Θ₂ := h.mem_iff.1 (mem_cons_self ..)
        exact (mem_append.1 this).resolve_left ha
      have hp := perm_cons_erase ha₂
      let s := split4 Γ Δ Θ₁ (Θ₂.erase a) (by
        have h' : a :: (Γ ++ Δ) ~ Θ₁ ++ Θ₂ := h
        perm_count [h', hp])
      ⟨s.Γ₁, a :: s.Γ₂, s.Δ₁, s.Δ₂,
        by have := s.hΓ; show a :: Γ ~ s.Γ₁ ++ a :: s.Γ₂; perm_count [this],
        s.hΔ,
        s.h₁,
        by have := s.h₂; show Θ₂ ~ a :: s.Γ₂ ++ s.Δ₂; perm_count [this, hp]⟩

end MALL

#axioms_within_file [propext, Quot.sound]
