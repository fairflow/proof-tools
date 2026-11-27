import sys; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
pre = '''import DILL.Corpus.Basic
open DILL DILL.Corpus
def allB : List Nat → (Nat → Bool) → Bool
  | [], _ => true
  | a :: l, p => p a && allB l p
def nth : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, n + 1 => nth l n
def tbl : List Nat := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3]
set_option profiler true
set_option maxRecDepth 1000000
'''
T = {
 "List.range 20000 |>.all (i == i) (BEq instance)": "example : (List.range 20000).all (fun i => i == i) = true := by decide +kernel",
 "List.range 20000, own all, Nat.beq i i": "example : allB (List.range 20000) (fun i => Nat.beq i i) = true := by decide +kernel",
 "the same, 40000": "example : allB (List.range 40000) (fun i => Nat.beq i i) = true := by decide +kernel",
 "List.replicate 20000 7, own all, Nat.beq": "example : allB (List.replicate 20000 7) (fun i => Nat.beq i 7) = true := by decide +kernel",
 "20000 x nth tbl 12 (13 steps of a list)": "example : allB (List.replicate 20000 12) (fun i => Nat.beq (nth tbl i) 9) = true := by decide +kernel",
 "20000 x (i * 31 + 7) % 65536 / 2 % 2": "example : allB (List.range 20000) (fun i => Nat.ble ((i * 31 + 7) % 65536 / 2 % 2) 1) = true := by decide +kernel",
}
for name, t in T.items():
    path = "Corpus/out/exp/b2.lean"
    open(path, "w").write(pre + t + "\n")
    code, dt, mb, lines = lean(path, mem=4000, deadline=100, show=12)
    prof = "; ".join(l.strip() for l in lines if "took" in l or "error" in l)[:160]
    print(f"{name}: exit {code}, peak {mb:.0f} MB | {prof}", flush=True)
