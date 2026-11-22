/-
Tests of the map out of `ProofTools.Explore.System` on the example calculus
(`ProofToolsTest/Explore/Calculus.lean`): soundness of the moves for a
family into `Type`, a derivation of the explorer carried to a derivation of
the calculus as data, an attempt as a derived rule on derivations, the
certifier whose property is a type, and the same notion at a proposition.

The calculus is stated here a second time, as its source would state it: an
inductive family `G3 : Seq → Type` with one constructor for each rule of the
table in `Calculus.lean`.  `soundT` says that each move is one of them.
-/
import ProofToolsTest.Explore.Calculus
import ProofToolsTest.Explore.Tactic

namespace ProofToolsTest.Explore.MapOutTest

open ProofTools ProofTools.Explore ProofToolsTest.Explore

/-- The atom `p`. -/
abbrev p : Form := .atom 0
/-- The atom `q`. -/
abbrev q : Form := .atom 1

/-! ## The calculus as an inductive family -/

/-- **Derivations of the example calculus**, a rule a constructor. -/
inductive G3 : Seq → Type where
  | ax {Γ : List Form} {C : Form} (h : C ∈ Γ) : G3 (Γ ⊢ C)
  | botL {Γ : List Form} {C : Form} (h : ⊥' ∈ Γ) : G3 (Γ ⊢ C)
  | impR {Γ : List Form} {a b : Form} (d : G3 ((a :: Γ) ⊢ b)) : G3 (Γ ⊢ a ⟶ b)
  | impL {Γ : List Form} {C : Form} (a b : Form) (h : (a ⟶ b) ∈ Γ) (d₁ : G3 (Γ ⊢ a))
      (d₂ : G3 ((b :: Γ) ⊢ C)) : G3 (Γ ⊢ C)
  | andR {Γ : List Form} {a b : Form} (d₁ : G3 (Γ ⊢ a)) (d₂ : G3 (Γ ⊢ b)) : G3 (Γ ⊢ a ⋏ b)
  | andL {Γ : List Form} {C : Form} (a b : Form) (h : (a ⋏ b) ∈ Γ)
      (d : G3 ((a :: b :: Γ) ⊢ C)) : G3 (Γ ⊢ C)
  | orR1 {Γ : List Form} {a b : Form} (d : G3 (Γ ⊢ a)) : G3 (Γ ⊢ a ⋎ b)
  | orR2 {Γ : List Form} {a b : Form} (d : G3 (Γ ⊢ b)) : G3 (Γ ⊢ a ⋎ b)
  | orL {Γ : List Form} {C : Form} (a b : Form) (h : (a ⋎ b) ∈ Γ) (d₁ : G3 ((a :: Γ) ⊢ C))
      (d₂ : G3 ((b :: Γ) ⊢ C)) : G3 (Γ ⊢ C)

/-- The rules of a derivation, the conclusion's first, then those of each
premise in turn. -/
def G3.rules : {s : Seq} → G3 s → List String
  | _, .ax _ => ["ax"]
  | _, .botL _ => ["botL"]
  | _, .impR d => "impR" :: d.rules
  | _, .impL _ _ _ d₁ d₂ => "impL" :: d₁.rules ++ d₂.rules
  | _, .andR d₁ d₂ => "andR" :: d₁.rules ++ d₂.rules
  | _, .andL _ _ _ d => "andL" :: d.rules
  | _, .orR1 d => "orR1" :: d.rules
  | _, .orR2 d => "orR2" :: d.rules
  | _, .orL _ _ _ d₁ d₂ => "orL" :: d₁.rules ++ d₂.rules

/-- The premises a step names, for the list a node writes. -/
def prems {ps qs : List Seq} (h : (Except.ok qs : Except String (List Seq)) = .ok ps)
    (e : Each G3 ps) : Each G3 qs :=
  (Except.ok.inj h).symm ▸ e

/-- **The moves are sound for the derivations of the calculus**: each move
that applies is a rule, applied to the derivations of its premises. -/
def soundT : IPC.SoundT G3 := fun m s ps h e =>
  match m, s, h with
  | .ax, ⟨Γ, C⟩, h =>
    if hm : C ∈ Γ then .ax hm else absurd h (by simp [step, hm])
  | .botL, ⟨Γ, _⟩, h =>
    if hm : Form.bot ∈ Γ then .botL hm else absurd h (by simp [step, hm])
  | .impR, ⟨_, .imp _ _⟩, h => .impR (prems h e).1
  | .impR, ⟨_, .atom _⟩, h | .impR, ⟨_, .bot⟩, h | .impR, ⟨_, .and _ _⟩, h
  | .impR, ⟨_, .or _ _⟩, h => absurd h (by simp [step])
  | .impL a b, ⟨Γ, C⟩, h =>
    if hm : Form.imp a b ∈ Γ then
      let e' : Each G3 [Γ ⊢ a, (b :: Γ) ⊢ C] := prems (by simpa [step, hm] using h) e
      .impL a b hm e'.1 e'.2.1
    else absurd h (by simp [step, hm])
  | .andR, ⟨_, .and _ _⟩, h => .andR (prems h e).1 (prems h e).2.1
  | .andR, ⟨_, .atom _⟩, h | .andR, ⟨_, .bot⟩, h | .andR, ⟨_, .imp _ _⟩, h
  | .andR, ⟨_, .or _ _⟩, h => absurd h (by simp [step])
  | .andL a b, ⟨Γ, C⟩, h =>
    if hm : Form.and a b ∈ Γ then
      let e' : Each G3 [(a :: b :: Γ) ⊢ C] := prems (by simpa [step, hm] using h) e
      .andL a b hm e'.1
    else absurd h (by simp [step, hm])
  | .orR1, ⟨_, .or _ _⟩, h => .orR1 (prems h e).1
  | .orR1, ⟨_, .atom _⟩, h | .orR1, ⟨_, .bot⟩, h | .orR1, ⟨_, .imp _ _⟩, h
  | .orR1, ⟨_, .and _ _⟩, h => absurd h (by simp [step])
  | .orR2, ⟨_, .or _ _⟩, h => .orR2 (prems h e).1
  | .orR2, ⟨_, .atom _⟩, h | .orR2, ⟨_, .bot⟩, h | .orR2, ⟨_, .imp _ _⟩, h
  | .orR2, ⟨_, .and _ _⟩, h => absurd h (by simp [step])
  | .orL a b, ⟨Γ, C⟩, h =>
    if hm : Form.or a b ∈ Γ then
      let e' : Each G3 [(a :: Γ) ⊢ C, (b :: Γ) ⊢ C] := prems (by simpa [step, hm] using h) e
      .orL a b hm e'.1 e'.2.1
    else absurd h (by simp [step, hm])

/-! ## The notion, at a type and at a proposition -/

-- one for each premise, by position
example (a b : Seq) : Each G3 [a, b] = (G3 a ×' G3 b ×' PUnit.{1}) := rfl
example : IPC.SoundT G3 = (∀ m j ps, IPC.step m j = .ok ps → Each G3 ps → G3 j) := rfl

-- `Sound` is as it was: the premises by membership
example : IPC.Sound Valid = (∀ m j ps, IPC.step m j = .ok ps → (∀ p ∈ ps, Valid p) → Valid j) :=
  rfl

-- at a proposition the two are one notion (PROVED: `soundT_iff_sound`)
example : IPC.SoundT Valid := sound.soundT
example : IPC.SoundT Valid ↔ IPC.Sound Valid := ProofSystem.soundT_iff_sound

-- moves sound for the derivations are sound for there being one
example : IPC.Sound (fun s => Nonempty (G3 s)) := soundT.nonempty

/-! ## Why the premises are by position

Taken by membership, two premises with one judgment get one piece of data:
no proof of `a ∈ [a, a]` says which position it is.  So `Sound`, whose
premises are by membership, is not the notion for a type. -/

-- PROVED: what is given by membership is the same at two positions of one member
example {T : Seq → Type} (a : Seq) (h : ∀ x ∈ [a, a], T x) :
    (Each.ofMem h).1 = (Each.ofMem h).2.1 := rfl

-- by position, the two differ where they are made to
example (a : Seq) : ∃ e : Each (fun _ => Nat) [a, a], e.1 ≠ e.2.1 := ⟨⟨0, 1, ⟨⟩⟩, Nat.zero_ne_one⟩

/-! ## A derivation, mapped out -/

/-- A derivation of `(p ∧ q) → (q ∧ p)`. -/
def swap : Der IPC ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move impR
  apply_move andL p q
  apply_move andR
  apply_move ax
  apply_move ax

/-- The same, in the calculus, by hand. -/
def swapG3 : G3 ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) :=
  .impR (.andL p q (by decide) (.andR (.ax (by decide)) (.ax (by decide))))

-- the map out is that derivation: the kernel evaluates `Der.mapOut`
example : Der.mapOut soundT swap = swapG3 := rfl
#guard (Der.mapOut soundT swap).rules == ["impR", "andL", "andR", "ax", "ax"]

/-- `p, p → p ⊢ p ∧ p`: the two premises of `andR` are one judgment, derived
in two ways. -/
def twice : Der IPC ([p, p ⟶ p] ⊢ p ⋏ p) := by
  apply_move andR
  apply_move ax
  apply_move impL p p
  apply_move ax
  apply_move ax

-- each premise keeps its own derivation
example : Der.mapOut soundT twice =
    .andR (.ax (by decide)) (.impL p p (by decide) (.ax (by decide)) (.ax (by decide))) := rfl
#guard (Der.mapOut soundT twice).rules == ["andR", "ax", "impL", "ax", "ax"]

/-! ## An attempt is a derived rule on derivations -/

/-- `swap`, stopped after `andR`: two open goals. -/
def swapAtt : Att IPC true ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := by
  apply_move impR
  apply_move andL p q
  apply_move andR
  all_goals leave_open

example : swapAtt.goals = [[p, q, p ⋏ q] ⊢ q, [p, q, p ⋏ q] ⊢ p] := rfl

-- from a derivation of each open goal, by position, a derivation of the root
example : Att.mapOut soundT swapAtt ⟨.ax (by decide), .ax (by decide), ⟨⟩⟩ = swapG3 := rfl

-- the equations of `Att.mapOut`, as the library states them
example (g : Each G3 [[p] ⊢ p]) : Att.mapOut soundT (Att.goal : Att IPC true ([p] ⊢ p)) g = g.1 := by
  simp

/-! ## The certifier, at a type and at a proposition -/

/-- A script certifies a derivation of the calculus, as data: the kernel
runs the script, and the certifier's `sound` builds the derivation. -/
def swapByScript : G3 ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) :=
  (certifier soundT).verdict _ swap.script

#guard swapByScript.rules == swapG3.rules
example : swapByScript.rules = ["impR", "andL", "andR", "ax", "ax"] := by decide +kernel

-- the same certifier at a proposition: from `Sound`, through `soundT`
example : Valid ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p)) := (certifier sound.soundT).verdict _ swap.script
example : Nonempty (G3 ([] ⊢ (p ⋏ q) ⟶ (q ⋏ p))) := Der.sound soundT.nonempty swap

/-! ## In the kernel: where a node's equation is decided

`Swap` (`Tactic.lean`) is the system whose judgments hold functions.  A
soundness definition carries what it is given for the premises a node
writes to the premises `step` computes, by a cast along the node's
equation.  The kernel reduces the cast when the two are equal by
definition: so on an attempt that `run` built, which writes the premises as
`step` computes them, and not on one the tactic built, which writes them
quoted.  Compiled code runs on both. -/

open TacticTest in
/-- Swaps, counted: a family over the judgments of `Swap`. -/
inductive Sw : Pair → Type where
  | leaf (j : Pair) : Sw j
  | swap {j : Pair} (d : Sw ⟨fun b => j.f (!b)⟩) : Sw j

open TacticTest in
/-- The number of swaps. -/
def Sw.depth : {j : Pair} → Sw j → Nat
  | _, .leaf _ => 0
  | _, .swap d => d.depth + 1

open TacticTest in
/-- The one move is the one rule. -/
def soundSw : Swap.SoundT Sw := fun _ _ _ h e =>
  .swap (show Each Sw [_] from (Except.ok.inj h).symm ▸ e).1

open TacticTest in
/-- The attempt the tactic built (`swapped`), mapped out from a leaf at its
open goal. -/
def swByTactic : Sw ⟨fun b => cond b 1 2⟩ := Att.mapOut soundSw swapped ⟨.leaf _, ⟨⟩⟩

open TacticTest in
/-- The same attempt as `run` builds it, mapped out. -/
def swByRun : Sw ⟨fun b => cond b 1 2⟩ :=
  Att.mapOut soundSw (run Swap ⟨fun b => cond b 1 2⟩ [⟨0, ()⟩]).att ⟨.leaf _, ⟨⟩⟩

#guard swByTactic.depth == 1
#guard swByRun.depth == 1

-- the kernel evaluates the second
example : swByRun.depth = 1 := by decide +kernel

-- and not the first: the cast is along an equation that holds, but not by definition
example : True := by
  fail_if_success
    have : swByTactic.depth = 1 := by decide +kernel
  trivial

end ProofToolsTest.Explore.MapOutTest
