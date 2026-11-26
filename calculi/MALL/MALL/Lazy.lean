/-
Proof search by lazy splitting: an untrusted producer of trees of moves.

At a ⊗ the search does not choose how the context splits.  It gives the
whole context to the first premise, which returns what it did not use;
that goes to the second premise (the input and output contexts of Hodas
and Miller, *Logic programming in a fragment of intuitionistic linear
logic*, 1994, section 5).  A ⊤ may use any part of what it is given, so it
returns everything with a flag ("slack": Cervesato, Hodas and Pfenning,
*Efficient resource management for linear logic proof search*, 2000, call
the same thing the ⊤-flag), and a solution with the flag can take back,
later, whatever nobody else used.  The tree of moves is therefore built
last, as a function of what is taken back: the checker sees explicit
splits.

Code, not theory: nothing here is trusted or proved, the functions are
`partial`, and the file carries no bound on axioms.  Every tree it gives
is checked (`MALL/Run.lean`).
-/
import MALL.Proof

namespace MALL.Lazy

open ProofTools ProofTools.Explore MALL

/-- **A solution** of "derive `A` with part of the context `ctx`". -/
structure Sol where
  /-- What of the context was not used. -/
  left : List Form
  /-- Some ⊤ of the derivation can use more. -/
  slack : Bool
  /-- The tree of moves, given the formulas taken back (none unless
  `slack`). -/
  build : List Form → Cert S

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

/-- The two premises of & must use the same context. -/
def reconcile (B C : Form) (s₁ s₂ : Sol) : Option Sol :=
  let mk (L : List Form) (k : Bool) (e₁ e₂ : List Form) : Sol :=
    ⟨L, k, fun extra => .mk (.wth B C) [s₁.build (extra ++ e₁), s₂.build (extra ++ e₂)]⟩
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
def firstOf {α β : Type} (l : List α) (f : α → Option β) : Option β :=
  match l with
  | [] => none
  | a :: l => match f a with
    | some b => some b
    | none => firstOf l f

mutual

/-- Derivations of `⊢ A, Δ` for a part `Δ` of `ctx`, whose last rule has
`A` as its principal formula; each solution is handed to `k`, and the
first for which `k` succeeds is the answer. -/
partial def own {α : Type} (A : Form) (ctx : List Form) (k : Sol → Option α) : Option α :=
  let viaAx : Option α :=
    if Aᗮ ∈ ctx then k ⟨ctx.erase Aᗮ, false, fun _ => .mk (.ax A) []⟩ else none
  match viaAx with
  | some r => some r
  | none =>
    match A with
    | .top => k ⟨ctx, true, fun _ => .mk .top []⟩
    | .one => k ⟨ctx, false, fun _ => .mk .one []⟩
    | .bot =>
        firstOf ctx.eraseDups fun X =>
          lz X (ctx.erase X) fun s => k ⟨s.left, s.slack, fun e => .mk .bot [s.build e]⟩
    | .par B C =>
        lz B (C :: ctx) fun s =>
          match s.within ctx with
          | some s' => k ⟨s'.left, s'.slack, fun e => .mk (.par B C) [s'.build e]⟩
          | none => none
    | .wth B C =>
        lz B ctx fun s₁ => lz C ctx fun s₂ =>
          match reconcile B C s₁ s₂ with
          | some s => k s
          | none => none
    | .plus B C =>
        match lz B ctx (fun s => k ⟨s.left, s.slack, fun e => .mk (.plus₁ B C) [s.build e]⟩) with
        | some r => some r
        | none => lz C ctx fun s => k ⟨s.left, s.slack, fun e => .mk (.plus₂ B C) [s.build e]⟩
    | .tensor B C =>
        lz B ctx fun s₁ => lz C s₁.left fun s₂ =>
          k ⟨s₂.left, s₁.slack || s₂.slack, fun e =>
            let e₁ := if s₁.slack then e else []
            let e₂ := if s₁.slack then [] else e
            .mk (.tensor B C (sub ctx s₁.left ++ e₁)) [s₁.build e₁, s₂.build e₂]⟩
    | _ => none

/-- Derivations of `⊢ A, Δ` for a part `Δ` of `ctx`: the last rule is on
`A`, or on a formula `X` of the context, and then `A` is in the context of
that rule and must be used. -/
partial def lz {α : Type} (A : Form) (ctx : List Form) (k : Sol → Option α) : Option α :=
  match own A ctx k with
  | some r => some r
  | none =>
    firstOf ctx.eraseDups fun X =>
      match X with
      | .atom _ | .natom _ | .one | .zero => none
      | _ =>
        let ctx' := ctx.erase X
        own X (A :: ctx') fun s =>
          match s.within ctx' with
          | some s' => k s'
          | none => none

end

/-- **The search**: a tree of moves for the sequent, or nothing.  The
whole sequent must be used. -/
def prove (Γ : List Form) : Option (Cert S) :=
  match Γ with
  | [] => none
  | A :: rest =>
    lz A rest fun s =>
      if s.left.isEmpty then some (s.build [])
      else if s.slack then some (s.build s.left)
      else none

end MALL.Lazy
