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
def big : Nat := 2 ^ 600000 + 12345
set_option profiler true
set_option maxRecDepth 1000000
'''
T = {
 "5000 elements, Nat.beq i i": "example : allB (List.range 5000) (fun i => Nat.beq i i) = true := by decide +kernel",
 "5000 x nth tbl (i % 16 + i * 16) on a prefix-distinct term (about 8 steps)": "example : allB (List.range 5000) (fun i => Nat.ble (nth tbl (i % 16)) 9) = true := by decide +kernel",
 "5000 x nth (tbl ++ tbl ++ tbl ++ tbl) (i % 64) (about 32 steps)": "example : allB (List.range 5000) (fun i => Nat.ble (nth (tbl ++ tbl ++ tbl ++ tbl) (i % 64)) 9) = true := by decide +kernel",
 "5000 x a shift of a number of 600000 bits": "example : allB (List.range 5000) (fun i => Nat.ble ((big >>> (i * 100)) % 65536) 65536) = true := by decide +kernel",
 "5000 x six operations on small numbers": "example : allB (List.range 5000) (fun i => Nat.ble ((i * 31 + 7) % 65536 / 2 % 2) 1) = true := by decide +kernel",
}
for name, t in T.items():
    path = "Corpus/out/exp/b3.lean"
    open(path, "w").write(pre + t + "\n")
    code, dt, mb, lines = lean(path, mem=4000, deadline=100, show=12)
    prof = "; ".join(l.strip() for l in lines if "took" in l or "error" in l)[:160]
    print(f"{name}: exit {code}, peak {mb:.0f} MB | {prof}", flush=True)
