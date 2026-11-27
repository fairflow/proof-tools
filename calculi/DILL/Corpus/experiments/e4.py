import sys; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
tail = r'''
open DILL.Sat in
/-- (queries of membership, tests of two sequents, tests of a permutation) -/
def cntMem (D : List Seq) (j : Seq) : Nat × Nat × Nat :=
  let rec go : List Seq → Nat → Nat → Nat × Nat × Nat
    | [], e, p => (1, e, p)
    | k :: ks, e, p =>
      let g := decide (k.goal = j.goal)
      if equivB k j then (1, e + 1, if g then p + 1 else p) else go ks (e + 1) (if g then p + 1 else p)
  go D 0 0
def addc (a b : Nat × Nat × Nat) : Nat × Nat × Nat := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
def cntAll (D : List Seq) : Nat × Nat × Nat × Nat := Id.run do
  let mut c : Nat × Nat × Nat := (0, 0, 0)
  let mut splitsN := 0
  for k in D do
    let q (j : Seq) := cntMem D j
    -- the right rule
    match k.goal with
    | .lolli A B => c := addc c (q (k.unr ⨾ A :: k.lin ⟹ B))
    | .wth A B => c := addc c (q (k.unr ⨾ k.lin ⟹ A)); c := addc c (q (k.unr ⨾ k.lin ⟹ B))
    | .plus A B => c := addc c (q (k.unr ⨾ k.lin ⟹ A)); c := addc c (q (k.unr ⨾ k.lin ⟹ B))
    | .tensor A B =>
      for p in Dec.splits k.lin do
        splitsN := splitsN + 1
        c := addc c (q (k.unr ⨾ p.1 ⟹ A))
        if !Sat.memS D (k.unr ⨾ p.1 ⟹ A) then c := addc c (q (k.unr ⨾ p.2 ⟹ B))
    | _ => pure ()
    for pk in Dec.picks k.lin do
      match pk.1 with
      | .tensor A B => c := addc c (q (k.unr ⨾ A :: B :: pk.2 ⟹ k.goal))
      | .one => c := addc c (q (k.unr ⨾ pk.2 ⟹ k.goal))
      | .plus A B => c := addc c (q (k.unr ⨾ A :: pk.2 ⟹ k.goal)); c := addc c (q (k.unr ⨾ B :: pk.2 ⟹ k.goal))
      | .wth A B => c := addc c (q (k.unr ⨾ A :: pk.2 ⟹ k.goal)); c := addc c (q (k.unr ⨾ B :: pk.2 ⟹ k.goal))
      | .lolli A B =>
        for p in Dec.splits pk.2 do
          splitsN := splitsN + 1
          c := addc c (q (k.unr ⨾ p.1 ⟹ A))
          if !Sat.memS D (k.unr ⨾ p.1 ⟹ A) then c := addc c (q (k.unr ⨾ B :: p.2 ⟹ k.goal))
      | _ => pure ()
  return (splitsN, c)
#eval (saturated.length, (saturated.map fun k => k.lin.length).foldl max 0, cntAll saturated)
end DILL.Answer
'''
for n in [int(a) for a in sys.argv[1:]]:
    d = defs(nochain(n))
    path = "Corpus/out/exp/e4.lean"
    open(path, "w").write(d + tail)
    code, dt, mb, lines = lean(path, mem=4000, deadline=200)
    print(f"n={n}: (members, longest zone, (divisions, queries, tests of two sequents, tests of a permutation)) = {lines[:2]}  [{dt:.1f} s]", flush=True)
