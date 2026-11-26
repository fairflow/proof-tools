/-
The translation between the two-zone calculus and one-zone
intuitionistic linear logic, in both directions, as functions on
derivations.

Source: CCP (Chang, Chaudhuri, Pfenning, CMU-CS-03-131R), Theorem 7,
p. 20, items 3 ("If `Γ ; Δ ⟹ C` then `!Γ, Δ ⟶ C` in ILL") and 1 ("If
`!Γ, Δ ⟶ C` in ILL then `Γ ; Δ ⟹ C`").  Theory file: it ends with its
bound on axioms.

* `toILL` (item 3), with cut and without: by recursion on the two-zone
  derivation.  A rule with no premise weakens every `!G` (!W); copy is
  !D then !C; a rule with two premises that share `Γ` contracts every
  `!G` after the rule (`Tr.contractAll`); !L adds nothing; !R is !r; cut
  is Cut, and the cut on a valid hypothesis is !r on its first premise,
  then Cut.
* `ofILL` (item 1), with cut: first every one-zone derivation of `Θ ⊢ C`
  is read as one of `· ; Θ ⟹ C` (`Tr.ofILL0`), then the formulas `!G` of
  the linear zone are moved into the unrestricted zone, by the inversion
  of !L (`Tr.bangLInv`: a cut against `Γ ; · ⟹ !G`, which is !R, copy,
  init where `G ∈ Γ`).
-/
import DILL.Statements

namespace DILL

open List

namespace Tr

/-- A permutation by counting, after `List.map` is taken through `::`. -/
local macro "pc" "[" hs:term,* "]" : tactic =>
  `(tactic| ((try simp only [List.map_cons, List.map_nil]); perm_count [$hs,*]))

/-! ## One-zone ILL: exchange, and weakening and contraction of `!Γ` -/

/-- **Exchange in ILL**: the same rules, at the permuted context. -/
def illExch {c : Bool} : {Ξ Ξ' : List Form} → {C : Form} → Ξ ~ Ξ' → ILL c Ξ C → ILL c Ξ' C
  | _, _, _, e, .id A h => .id A (e.symm.trans h)
  | _, _, _, e, .cut hc A Γ₁ Γ₂ h d₁ d₂ => .cut hc A Γ₁ Γ₂ (e.symm.trans h) d₁ d₂
  | _, _, _, e, .tensorL A B Γ h d => .tensorL A B Γ (e.symm.trans h) d
  | _, _, _, e, .tensorR Γ₁ Γ₂ h d₁ d₂ => .tensorR Γ₁ Γ₂ (e.symm.trans h) d₁ d₂
  | _, _, _, e, .oneL Γ h d => .oneL Γ (e.symm.trans h) d
  | _, _, _, e, .oneR h => .oneR (e.symm.trans h)
  | _, _, _, e, .lolliL A B Γ₁ Γ₂ h d₁ d₂ => .lolliL A B Γ₁ Γ₂ (e.symm.trans h) d₁ d₂
  | _, _, _, e, .lolliR d => .lolliR (illExch (e.cons _) d)
  | _, _, _, e, .plusL A B Γ h d₁ d₂ => .plusL A B Γ (e.symm.trans h) d₁ d₂
  | _, _, _, e, .plusR₁ d => .plusR₁ (illExch e d)
  | _, _, _, e, .plusR₂ d => .plusR₂ (illExch e d)
  | _, _, _, e, .zeroL Γ h => .zeroL Γ (e.symm.trans h)
  | _, _, _, e, .withL₁ A B Γ h d => .withL₁ A B Γ (e.symm.trans h) d
  | _, _, _, e, .withL₂ A B Γ h d => .withL₂ A B Γ (e.symm.trans h) d
  | _, _, _, e, .withR d₁ d₂ => .withR (illExch e d₁) (illExch e d₂)
  | _, _, _, _, .topR => .topR
  | _, _, _, e, .bangD A Γ h d => .bangD A Γ (e.symm.trans h) d
  | _, _, _, e, .bangC A Γ h d => .bangC A Γ (e.symm.trans h) d
  | _, _, _, e, .bangW A Γ h d => .bangW A Γ (e.symm.trans h) d
  | _, _, _, e, .bangR Γ h d => .bangR Γ (e.symm.trans h) d

/-- **Weakening by `!Γ`**: !W for each formula of `Γ`. -/
def weakenAll {c : Bool} : (Γ : List Form) → {Θ : List Form} → {C : Form} →
    ILL c Θ C → ILL c (Γ.map Form.bang ++ Θ) C
  | [], _, _, d => d
  | G :: Γ, Θ, _, d => .bangW G (Γ.map Form.bang ++ Θ) (.refl _) (weakenAll Γ d)

/-- **Contraction of `!Γ`**: !C for each formula of `Γ`. -/
def contractAll {c : Bool} : (Γ : List Form) → {Θ : List Form} → {C : Form} →
    ILL c (Γ.map Form.bang ++ (Γ.map Form.bang ++ Θ)) C → ILL c (Γ.map Form.bang ++ Θ) C
  | [], _, _, d => d
  | G :: Γ, Θ, C, d =>
    let d₁ : ILL c ((!G) :: (!G) :: (Γ.map Form.bang ++ (Γ.map Form.bang ++ Θ))) C :=
      illExch (by pc []) d
    let d₂ : ILL c (Γ.map Form.bang ++ (Γ.map Form.bang ++ (!G) :: Θ)) C :=
      illExch (by pc []) (ILL.bangC G _ (.refl _) d₁)
    illExch (by pc []) (contractAll Γ d₂)

/-! ## From two zones to one -/

/-- **From two zones to one** (CCP Theorem 7.3), with the sequent taken
apart. -/
def toILLAux {c : Bool} : (Γ Ξ : List Form) → (C : Form) →
    Fam c (Γ ⨾ Ξ ⟹ C) → ILL c (Γ.map Form.bang ++ Ξ) C
  | Γ, _, _, .init A h => weakenAll Γ (.id A h)
  | Γ, Ξ, C, .copy A hΓ d =>
    let d₁ : ILL c (A :: (Γ.map Form.bang ++ Ξ)) C := illExch (by pc []) (toILLAux Γ (A :: Ξ) C d)
    have hm : (!A) ∈ Γ.map Form.bang ++ Ξ :=
      List.mem_append.2 (.inl (List.mem_map.2 ⟨A, hΓ, rfl⟩))
    have hp := DILL.perm_cons_erase hm
    .bangC A ((Γ.map Form.bang ++ Ξ).erase (!A)) hp
      (illExch (hp.cons _) (.bangD A (Γ.map Form.bang ++ Ξ) (.refl _) d₁))
  | Γ, _, C, .tensorL A B Δ h d =>
    .tensorL A B (Γ.map Form.bang ++ Δ) (by pc [h])
      (illExch (by pc []) (toILLAux Γ (A :: B :: Δ) C d))
  | Γ, _, _, .tensorR (A := A) (B := B) Δ Δ' h d₁ d₂ =>
    illExch (by pc [h]) (contractAll Γ (Θ := Δ ++ Δ')
      (.tensorR (Γ.map Form.bang ++ Δ) (Γ.map Form.bang ++ Δ') (by pc [])
        (toILLAux Γ Δ A d₁) (toILLAux Γ Δ' B d₂)))
  | Γ, _, C, .oneL Δ h d => .oneL (Γ.map Form.bang ++ Δ) (by pc [h]) (toILLAux Γ Δ C d)
  | Γ, _, _, .oneR h => weakenAll Γ (.oneR h)
  | Γ, _, C, .lolliL A B Δ Δ' h d₁ d₂ =>
    illExch (by pc [h]) (contractAll Γ (Θ := (A ⊸ B) :: (Δ ++ Δ'))
      (.lolliL A B (Γ.map Form.bang ++ Δ) (Γ.map Form.bang ++ Δ') (by pc [])
        (toILLAux Γ Δ A d₁) (illExch (by pc []) (toILLAux Γ (B :: Δ') C d₂))))
  | Γ, Ξ, _, .lolliR (A := A) (B := B) d =>
    .lolliR (illExch (by pc []) (toILLAux Γ (A :: Ξ) B d))
  | Γ, _, C, .withL₁ A B Δ h d =>
    .withL₁ A B (Γ.map Form.bang ++ Δ) (by pc [h]) (illExch (by pc []) (toILLAux Γ (A :: Δ) C d))
  | Γ, _, C, .withL₂ A B Δ h d =>
    .withL₂ A B (Γ.map Form.bang ++ Δ) (by pc [h]) (illExch (by pc []) (toILLAux Γ (B :: Δ) C d))
  | Γ, Ξ, _, .withR (A := A) (B := B) d₁ d₂ => .withR (toILLAux Γ Ξ A d₁) (toILLAux Γ Ξ B d₂)
  | _, _, _, .topR => .topR
  | Γ, _, _, .zeroL Δ h => .zeroL (Γ.map Form.bang ++ Δ) (by pc [h])
  | Γ, _, C, .plusL A B Δ h d₁ d₂ =>
    .plusL A B (Γ.map Form.bang ++ Δ) (by pc [h])
      (illExch (by pc []) (toILLAux Γ (A :: Δ) C d₁))
      (illExch (by pc []) (toILLAux Γ (B :: Δ) C d₂))
  | Γ, Ξ, _, .plusR₁ (A := A) d => .plusR₁ (toILLAux Γ Ξ A d)
  | Γ, Ξ, _, .plusR₂ (B := B) d => .plusR₂ (toILLAux Γ Ξ B d)
  | Γ, _, C, .bangL A Δ h d => illExch (by pc [h]) (toILLAux (A :: Γ) Δ C d)
  | Γ, _, _, .bangR (A := A) h d =>
    .bangR Γ (by pc [h]) (illExch (by pc []) (toILLAux Γ [] A d))
  | Γ, _, C, .cut hc A Δ Δ' h d₁ d₂ =>
    illExch (by pc [h]) (contractAll Γ (Θ := Δ ++ Δ')
      (.cut hc A (Γ.map Form.bang ++ Δ) (Γ.map Form.bang ++ Δ') (by pc [])
        (toILLAux Γ Δ A d₁) (illExch (by pc []) (toILLAux Γ (A :: Δ') C d₂))))
  | Γ, Ξ, C, .cutU hc A d₁ d₂ =>
    contractAll Γ
      (.cut hc (!A) (Γ.map Form.bang) (Γ.map Form.bang ++ Ξ) (.refl _)
        (.bangR Γ (.refl _) (illExch (by pc []) (toILLAux Γ [] A d₁)))
        (toILLAux (A :: Γ) Ξ C d₂))

/-! ## From one zone to two -/

/-- **The inversion of !L, in the calculus with cut**: a linear `!A`
whose `A` is a valid hypothesis may be dropped.  A cut against
`Γ ; · ⟹ !A`, which is !R, copy, init. -/
def bangLInv {Γ Δ : List Form} {C A : Form} (hA : A ∈ Γ)
    (d : Fam true (Γ ⨾ (!A) :: Δ ⟹ C)) : Fam true (Γ ⨾ Δ ⟹ C) :=
  .cut rfl (!A) [] Δ (.refl _) (.bangR (.refl _) (.copy A hA (.init A (.refl _)))) d

/-- The inversion of !L for each formula of a list of valid hypotheses. -/
def unbangAll : (Γ' : List Form) → {Γ Δ : List Form} → {C : Form} → (∀ B, B ∈ Γ' → B ∈ Γ) →
    Fam true (Γ ⨾ Γ'.map Form.bang ++ Δ ⟹ C) → Fam true (Γ ⨾ Δ ⟹ C)
  | [], _, _, _, _, d => d
  | G :: Γ', _, _, _, s, d =>
    unbangAll Γ' (fun B h => s B (.tail _ h)) (bangLInv (s G (.head _)) d)

theorem nil_sub {Γ : List Form} : ∀ B, B ∈ ([] : List Form) → B ∈ Γ :=
  fun _ h => nomatch h

theorem mem_shift {G : Form} {Γ Γ₀ : List Form} :
    ∀ B, B ∈ G :: Γ ++ Γ₀ → B ∈ Γ ++ G :: Γ₀ := by
  intro B hB
  rcases List.mem_cons.1 hB with e | e
  · exact List.mem_append.2 (.inr (e ▸ .head _))
  · rcases List.mem_append.1 e with e | e
    · exact List.mem_append.2 (.inl e)
    · exact List.mem_append.2 (.inr (.tail _ e))

/-- !L for each formula of a list of valid hypotheses. -/
def bangAll {c : Bool} : (Γ : List Form) → {Γ₀ Δ : List Form} → {C : Form} →
    Fam c (Γ ++ Γ₀ ⨾ Δ ⟹ C) → Fam c (Γ₀ ⨾ Γ.map Form.bang ++ Δ ⟹ C)
  | [], _, _, _, d => d
  | G :: Γ, Γ₀, Δ, _, d =>
    .bangL G (Γ.map Form.bang ++ Δ) (.refl _) (bangAll Γ (Γ₀ := G :: Γ₀) (d.mono mem_shift))

/-- **A one-zone derivation is a two-zone derivation with the
unrestricted zone empty.**  !D is weakening of `Γ`, copy, !L; !W is
weakening of `Γ`, !L; !C is the inversion of !L twice, then !L; !r is the
inversion of !L for each formula of the context, !R, then !L for each. -/
def ofILL0 : {Θ : List Form} → {C : Form} → ILL true Θ C → Fam true ([] ⨾ Θ ⟹ C)
  | _, _, .id A h => .init A h
  | _, _, .cut _ A Γ₁ Γ₂ h d₁ d₂ => .cut rfl A Γ₁ Γ₂ h (ofILL0 d₁) (ofILL0 d₂)
  | _, _, .tensorL A B Γ h d => .tensorL A B Γ h (ofILL0 d)
  | _, _, .tensorR Γ₁ Γ₂ h d₁ d₂ => .tensorR Γ₁ Γ₂ h (ofILL0 d₁) (ofILL0 d₂)
  | _, _, .oneL Γ h d => .oneL Γ h (ofILL0 d)
  | _, _, .oneR h => .oneR h
  | _, _, .lolliL A B Γ₁ Γ₂ h d₁ d₂ => .lolliL A B Γ₁ Γ₂ h (ofILL0 d₁) (ofILL0 d₂)
  | _, _, .lolliR d => .lolliR (ofILL0 d)
  | _, _, .plusL A B Γ h d₁ d₂ => .plusL A B Γ h (ofILL0 d₁) (ofILL0 d₂)
  | _, _, .plusR₁ d => .plusR₁ (ofILL0 d)
  | _, _, .plusR₂ d => .plusR₂ (ofILL0 d)
  | _, _, .zeroL Γ h => .zeroL Γ h
  | _, _, .withL₁ A B Γ h d => .withL₁ A B Γ h (ofILL0 d)
  | _, _, .withL₂ A B Γ h d => .withL₂ A B Γ h (ofILL0 d)
  | _, _, .withR d₁ d₂ => .withR (ofILL0 d₁) (ofILL0 d₂)
  | _, _, .topR => .topR
  | _, _, .bangD A Γ h d => .bangL A Γ h (.copy A (.head _) ((ofILL0 d).weakenU A))
  | _, _, .bangC A Γ h d =>
    .bangL A Γ h (bangLInv (.head _) (bangLInv (.head _) ((ofILL0 d).weakenU A)))
  | _, _, .bangW A Γ h d => .bangL A Γ h ((ofILL0 d).weakenU A)
  | _, _, .bangR (A := A) Γ h d =>
    let d₁ : Fam true (Γ ⨾ Γ.map Form.bang ++ [] ⟹ A) :=
      ((ofILL0 d).mono nil_sub).exch (by pc [])
    let d₂ : Fam true (Γ ++ [] ⨾ [] ⟹ !A) :=
      (Fam.bangR (.refl _) (unbangAll Γ (fun _ h => h) d₁)).mono
        (fun _ h => List.mem_append.2 (.inl h))
    (bangAll Γ d₂).exch (by pc [h])

end Tr

/-! ## The goals -/

/-- **From two zones to one** (CCP Theorem 7.3), with cut and without. -/
def toILL : ToILL := fun _ Γ Δ C d => Tr.toILLAux Γ Δ C d

/-- **From one zone to two** (CCP Theorem 7.1). -/
def ofILL : OfILL := fun Γ _ _ d =>
  Tr.unbangAll Γ (fun _ h => h) ((Tr.ofILL0 d).mono Tr.nil_sub)

/-- **The two calculi derive the same.** -/
theorem illEquivalence : ILLEquivalence := fun Γ Δ C =>
  ⟨fun ⟨d⟩ => ⟨toILL true Γ Δ C d⟩, fun ⟨d⟩ => ⟨ofILL Γ Δ C d⟩⟩

/-! ## Tests: small derivations, taken across and back -/

/-- `a ; · ⟹ a ⊗ a`, by copy twice: the unrestricted zone is shared by
the two premises of ⊗R. -/
def Tr.testCopy : CF ([.atom 0] ⨾ [] ⟹ .atom 0 ⊗ .atom 0) :=
  .copy (.atom 0) (.head _) (.copy (.atom 0) (.head _)
    (.tensorR [.atom 0] [.atom 0] (.refl _) (.init _ (.refl _)) (.init _ (.refl _))))

/-- `!a ⊢ a ⊗ a` in ILL without Cut. -/
example : ILL false [!(.atom 0)] (.atom 0 ⊗ .atom 0) := toILL false [.atom 0] [] _ Tr.testCopy

/-- Across and back, with the formula `!a` left in the linear zone. -/
example : Fam true ([] ⨾ [!(.atom 0)] ⟹ .atom 0 ⊗ .atom 0) :=
  ofILL [] [!(.atom 0)] _ (toILL true [.atom 0] [] _ Tr.testCopy.lift)

/-- Across and back, to the sequent it came from. -/
example : Fam true ([.atom 0] ⨾ [] ⟹ .atom 0 ⊗ .atom 0) :=
  ofILL [.atom 0] [] _ (toILL true [.atom 0] [] _ Tr.testCopy.lift)

/-- `· ; · ⟹ !(a ⊸ a)` by the cut on a valid hypothesis, and its
image. -/
example : ILL true [] (!(.atom 0 ⊸ .atom 0)) :=
  toILL true [] [] _
    (.cutU rfl (.atom 0 ⊸ .atom 0) (.lolliR (.init _ (.refl _)))
      (.bangR (.refl _) (.copy _ (.head _) (.init _ (.refl _)))))

end DILL

#axioms_within_file [propext, Quot.sound]
