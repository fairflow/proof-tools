/-
Proof search for DILL without cut, by lazy division of the linear zone
and a budget on copy: a producer of trees of moves, which is not trusted.

**The division of the linear zone.**  At ⊗R and ⊸L the search does not
choose how the zone divides.  It gives the whole zone to one premise,
which returns what it did not use; that goes to the other premise (the
input and output contexts of Hodas and Miller, *Logic programming in a
fragment of intuitionistic linear logic*, 1994, section 5).  ⊤R and 0L
may use any part of what they are given, so they return everything with
a flag ("slack": Cervesato, Hodas and Pfenning, *Efficient resource
management for linear logic proof search*, 2000, have it as the ⊤-flag),
and a solution with the flag can take back, later, whatever nobody else
used.  The tree of moves is therefore built last, as a function of what
is taken back: the checker sees every division, named in the moves
`tensorR A B Δ` and `lolliL A B Δ`.

**The order of the rules.**  The invertible rules first (CCP Lemma 6):
on the right ⊸R, &R, ⊤R; on the left ⊗L, 1L, ⊕L, 0L, !L, applied to a
formula at the moment it enters the linear zone (`add`), so that the
zone handed from premise to premise holds only atoms, implications,
`&`-formulas and ⊤.  A formula that enters inside a branch is used
inside it (`Sol.within`).  Then the choices (`solve`): init, 1R, !R,
⊕R₁, ⊕R₂, ⊗R; a left rule on a formula of the linear zone; copy.

**copy** is what makes the search endless.  It is taken only together
with the rule that uses the copied formula (a copy is permuted upwards
to that rule in any derivation, so nothing is lost), and each use costs
one of a budget `n` that is counted along a branch.  When the budget is
spent the copy is refused and counted (`Stats.cuts`): a failure with
refusals is a `flag`, not a "no".

**Two ways to take a left rule** (`Cfg.focus`).
* `focus := false`: ⊸L and &L as the figure has them: the premise for
  `A` is searched, then `B` enters the zone of the second premise and
  any rule may follow.
* `focus := true` (the default): the left rules are chained on the one
  formula down to an atom, which must then be the conclusion, by init
  (Andreoli, *Logic programming with focusing proofs in linear logic*,
  1992, with every atom negative; for a clause `A₁ ⊸ … ⊸ a` this is
  backward chaining, as in Hodas and Miller).  The second premise of ⊸L
  is searched first, so a clause whose head is not the conclusion fails
  at once (`canHead`).  That nothing derivable without cut is lost is
  the completeness of focusing, which is not proved here: a failure of
  this search is a `flag` in either case.

Code, not theory: nothing here is trusted or proved, the functions are
`partial`, and the file carries no bound on axioms.  Every tree it gives
is checked (`DILL/Run.lean`).
-/
import DILL.Proof

namespace DILL.Lazy

open ProofTools ProofTools.Explore DILL

/-- **A solution** of "derive `Γ ; Δ ⟹ C` for a part `Δ` of the zone
`ctx`". -/
structure Sol where
  /-- What of the zone was not used. -/
  left : List Form
  /-- Some ⊤R or 0L of the derivation can use more. -/
  slack : Bool
  /-- The tree of moves, given the formulas taken back (none unless
  `slack`). -/
  build : List Form → Cert S

/-- How the search is run. -/
structure Cfg where
  /-- Chain the left rules on one formula down to its head (see the
  header). -/
  focus : Bool := true
  /-- A cap on the number of calls of `solve`; 0 is no cap.  Past it
  every branch fails and `Stats.capped` is set. -/
  maxCalls : Nat := 0

/-- What a run did. -/
structure Stats where
  /-- The calls of `solve`. -/
  calls : Nat := 0
  /-- The copies refused because the budget was spent. -/
  cuts : Nat := 0
  /-- The cap on calls was reached. -/
  capped : Bool := false
  deriving Repr

/-- The search keeps its counts in a state. -/
abbrev M := StateM Stats

/-- `L` is part of `M`, as multisets. -/
def subM (L M : List Form) : Bool := L.all fun x => L.count x ≤ M.count x

/-- The common part of two multisets. -/
def interM (L M : List Form) : List Form := sub L (sub L M)

/-- The solution, made to leave only formulas of `bound`: possible when it
does so already, or has slack to take the others back. -/
def Sol.within (s : Sol) (bound : List Form) : Option Sol :=
  if subM s.left bound then some s
  else if s.slack then
    let keep := interM s.left bound
    some ⟨keep, true, fun extra => s.build (extra ++ sub s.left keep)⟩
  else none

/-- The solution under a rule of one premise that leaves the zone as it
is, or acts on a formula that is not of the zone handed on. -/
def under (m : Move) (s : Sol) : Sol := ⟨s.left, s.slack, fun e => .mk m [s.build e]⟩

/-- The two premises of &R, and of ⊕L, must use the same part of the
zone. -/
def reconcile (m : Move) (s₁ s₂ : Sol) : Option Sol :=
  let mk (L : List Form) (k : Bool) (e₁ e₂ : List Form) : Sol :=
    ⟨L, k, fun extra => .mk m [s₁.build (extra ++ e₁), s₂.build (extra ++ e₂)]⟩
  match s₁.slack, s₂.slack with
  | false, false => if permB s₁.left s₂.left then some (mk s₁.left false [] []) else none
  | true, false =>
      if subM s₂.left s₁.left then some (mk s₂.left false (sub s₁.left s₂.left) []) else none
  | false, true =>
      if subM s₁.left s₂.left then some (mk s₁.left false [] (sub s₂.left s₁.left)) else none
  | true, true =>
      let L := interM s₁.left s₂.left
      some (mk L true (sub s₁.left L) (sub s₂.left L))

/-- The first of the alternatives that succeeds. -/
def firstOf {α β : Type} (l : List α) (f : α → M (Option β)) : M (Option β) :=
  match l with
  | [] => pure none
  | a :: l => do
    match ← f a with
    | some b => pure (some b)
    | none => firstOf l f

/-- A chain of left rules on the formula can end at init with the
conclusion `C`, or reaches a formula whose left rule is invertible. -/
def canHead (C : Form) : Form → Bool
  | .atom n => C == .atom n
  | .lolli _ B => canHead C B
  | .wth A B => canHead C A || canHead C B
  | .top => false
  | _ => true

/-- The formulas of the linear zone on which a left rule is tried. -/
def linCands (cfg : Cfg) (ctx : List Form) (C : Form) : List Form :=
  (ctx.filter fun X =>
    match X with
    | .lolli _ _ | .wth _ _ => !cfg.focus || canHead C X
    | _ => false).eraseDups

/-- The formulas of the unrestricted zone of which a copy is tried: not
⊤ and not 1, whose copies do nothing; an atom only where it is the
conclusion; `!A` only where `A` is not there already. -/
def copyCands (cfg : Cfg) (Γ : List Form) (C : Form) : List Form :=
  Γ.filter fun X =>
    match X with
    | .atom _ => X == C
    | .top | .one => false
    | .bang A => !Γ.contains A
    | .lolli _ _ | .wth _ _ => !cfg.focus || canHead C X
    | _ => true

mutual

/-- Derivations of `Γ ; Δ ⟹ C` for a part `Δ` of `ctx`, a zone of atoms,
implications, `&`-formulas and ⊤.  `n` copies may still be made along
the branch.  Each solution is handed to `k`, and the first for which `k`
succeeds is the answer. -/
partial def solve {α : Type} (cfg : Cfg) (Γ ctx : List Form) (C : Form) (n : Nat)
    (k : Sol → M (Option α)) : M (Option α) := do
  let st ← get
  if cfg.maxCalls != 0 && st.calls ≥ cfg.maxCalls then
    set { st with capped := true }
    return none
  set { st with calls := st.calls + 1 }
  -- init, at any formula but ⊤ (⊤R does as much, and has slack)
  let viaInit ← (if C != .top && ctx.contains C then
      k ⟨ctx.erase C, false, fun _ => .mk .init []⟩ else pure none)
  if let some r := viaInit then return some r
  match C with
  -- the invertible rules on the right
  | .top => k ⟨ctx, true, fun _ => .mk .topR []⟩
  | .lolli A B => add cfg Γ ctx ctx [A] B n fun s => k (under (.lolliR A B) s)
  | .wth A B =>
    solve cfg Γ ctx A n fun s₁ => solve cfg Γ ctx B n fun s₂ =>
      match reconcile (.withR A B) s₁ s₂ with
      | some s => k s
      | none => pure none
  | _ =>
    -- the choices: a right rule
    let viaRight ← (match C with
      | .one => k ⟨ctx, false, fun _ => .mk .oneR []⟩
      | .bang A => do
        -- the premise has an empty linear zone: one derivation of it serves
        match ← solve cfg Γ [] A n (fun s => pure (some s)) with
        | some s => k ⟨ctx, false, fun _ => .mk (.bangR A) [s.build []]⟩
        | none => pure none
      | .plus A B => do
        match ← solve cfg Γ ctx A n (fun s => k (under (.plusR₁ A B) s)) with
        | some r => pure (some r)
        | none => solve cfg Γ ctx B n fun s => k (under (.plusR₂ A B) s)
      | .tensor A B =>
        solve cfg Γ ctx A n fun s₁ => solve cfg Γ s₁.left B n fun s₂ =>
          k ⟨s₂.left, s₁.slack || s₂.slack, fun e =>
            let e₁ := if s₁.slack then e else []
            let e₂ := if s₁.slack then [] else e
            .mk (.tensorR A B (sub ctx s₁.left ++ e₁)) [s₁.build e₁, s₂.build e₂]⟩
      | _ => pure none)
    if let some r := viaRight then return some r
    -- a left rule on a formula of the linear zone
    let viaLeft ← firstOf (linCands cfg ctx C) fun X => leftOn cfg Γ (ctx.erase X) X C n k
    if let some r := viaLeft then return some r
    -- copy, with the rule that uses the copy
    let cands := copyCands cfg Γ C
    if cands.isEmpty then return none
    match n with
    | 0 =>
      modify fun st => { st with cuts := st.cuts + 1 }
      return none
    | n' + 1 => firstOf cands fun A => leftOn cfg Γ ctx A C n' fun s => k (under (.copy A) s)

/-- Derivations of `Γ ; Δ, X ⟹ C` for a part `Δ` of `ctx` whose last rule
is on `X` (init, where `X` is an atom). -/
partial def leftOn {α : Type} (cfg : Cfg) (Γ ctx : List Form) (X C : Form) (n : Nat)
    (k : Sol → M (Option α)) : M (Option α) :=
  match X with
  | .atom _ => if X == C then k ⟨ctx, false, fun _ => .mk .init []⟩ else pure none
  | .top => pure none
  | .lolli A B =>
    if cfg.focus then
      -- the premise with `B` first: its head must be the conclusion
      leftOn cfg Γ ctx B C n fun s₂ => solve cfg Γ s₂.left A n fun s₁ =>
        k ⟨s₁.left, s₁.slack || s₂.slack, fun e =>
          let e₂ := if s₂.slack then e else []
          let e₁ := if s₂.slack then [] else e
          .mk (.lolliL A B (sub s₂.left s₁.left ++ e₁)) [s₁.build e₁, s₂.build e₂]⟩
    else
      solve cfg Γ ctx A n fun s₁ => add cfg Γ s₁.left s₁.left [B] C n fun s₂ =>
        k ⟨s₂.left, s₁.slack || s₂.slack, fun e =>
          let e₁ := if s₁.slack then e else []
          let e₂ := if s₁.slack then [] else e
          .mk (.lolliL A B (sub ctx s₁.left ++ e₁)) [s₁.build e₁, s₂.build e₂]⟩
  | .wth A B => do
    let first ← (if cfg.focus then leftOn cfg Γ ctx A C n fun s => k (under (.withL₁ A B) s)
      else add cfg Γ ctx ctx [A] C n fun s => k (under (.withL₁ A B) s))
    if let some r := first then return some r
    if cfg.focus then leftOn cfg Γ ctx B C n fun s => k (under (.withL₂ A B) s)
    else add cfg Γ ctx ctx [B] C n fun s => k (under (.withL₂ A B) s)
  -- ⊗, 1, ⊕, 0, !: the left rule is invertible
  | _ => add cfg Γ ctx ctx [X] C n k

/-- Derivations of `Γ ; Δ, new ⟹ C` for a part `Δ` of `bound`, where
`ctx` is `bound` and the formulas that have entered since.  The
invertible left rules are applied to each formula of `new` as it
enters; a solution leaves only formulas of `bound`. -/
partial def add {α : Type} (cfg : Cfg) (Γ ctx bound new : List Form) (C : Form) (n : Nat)
    (k : Sol → M (Option α)) : M (Option α) :=
  match new with
  | [] =>
    solve cfg Γ ctx C n fun s =>
      match s.within bound with
      | some s' => k s'
      | none => pure none
  | X :: rest =>
    match X with
    | .tensor A B => add cfg Γ ctx bound (A :: B :: rest) C n fun s => k (under (.tensorL A B) s)
    | .one => add cfg Γ ctx bound rest C n fun s => k (under .oneL s)
    | .zero => k ⟨bound, true, fun _ => .mk .zeroL []⟩
    | .plus A B =>
      add cfg Γ ctx bound (A :: rest) C n fun s₁ => add cfg Γ ctx bound (B :: rest) C n fun s₂ =>
        match reconcile (.plusL A B) s₁ s₂ with
        | some s => k s
        | none => pure none
    | .bang A =>
      add cfg (if Γ.contains A then Γ else A :: Γ) ctx bound rest C n fun s =>
        k (under (.bangL A) s)
    | _ => add cfg Γ (X :: ctx) bound rest C n k

end

/-- **The search**, with what it did: a tree of moves for the sequent, or
nothing, at the budget `n` of copies along a branch.  The whole linear
zone must be used. -/
def proveWith (cfg : Cfg) (j : Seq) (n : Nat) : Option (Cert S) × Stats :=
  (add cfg j.unr.eraseDups [] [] j.lin j.goal n (fun s => pure (some (s.build [])))).run {}

/-- **The search**, with the left rules chained. -/
def prove (j : Seq) (n : Nat) : Option (Cert S) := (proveWith {} j n).1

end DILL.Lazy
