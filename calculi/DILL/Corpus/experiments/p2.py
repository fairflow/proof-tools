import sys; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
proto = open("Corpus/experiments/proto.lean.txt").read()
n = int(sys.argv[1])
d = defs(nochain(n)); N = d.count("⟹") - 2
pre = "def dd : Nat := Nat.log2 saturated.length + 1\ndef D' : List Seq := saturated.map Fast.canon\n"
B = {
 "A  canon and build, one lookup": "example : Fast.memF dd (Fast.build dd D') (Fast.canon sequent) = true := by decide +kernel",
 "B  enumeration only (membership always true)": "example : D'.all (Fast.satAtW Fast.insH (fun _ => true)) = true := by decide +kernel",
 "B' enumeration with plain cons": "example : D'.all (Fast.satAtW List.cons (fun _ => true)) = true := by decide +kernel",
 "C  enumeration and the key of each premise": "example : D'.all (Fast.satAtW Fast.insH (fun x => Nat.ble 0 (Fast.keyOf x.goal x.lin))) = true := by decide +kernel",
 "D  the whole": "example : Fast.refutedFast saturated sequent = true := by decide +kernel",
}
for name, b in B.items():
    path = f"Corpus/out/exp/p2.lean"
    open(path, "w").write(d + proto + pre + "set_option profiler true\nset_option maxRecDepth 1000000\n" + b + "\nend DILL.Answer\n")
    code, dt, mb, lines = lean(path, mem=4000, deadline=170, show=12)
    prof = "; ".join(l.strip() for l in lines if "took" in l or "error" in l)[:200]
    print(f"N={N} {name}: exit {code}, peak {mb:.0f} MB | {prof}", flush=True)
