import sys; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
V = {
 "V1 refutedBy": "theorem c : refutedBy saturated sequent = true := by decide +kernel",
 "V2 certifier": "theorem c : noCFBySet.check sequent saturated = true := by decide +kernel",
 "V3 refutedBy, rfl": "theorem c : refutedBy saturated sequent = true := Eq.refl true",
 "V4 certifier, rfl": "theorem c : noCFBySet.check sequent saturated = true := Eq.refl true",
}
for n in [int(a) for a in sys.argv[1:]]:
    d = defs(nochain(n))
    N = d.count("⟹") - 1
    for name, v in V.items():
        path = f"Corpus/out/exp/e1_{n}.lean"
        open(path, "w").write(d + "set_option profiler true\nset_option maxRecDepth 100000 in\n" + v + "\nend DILL.Answer\n")
        code, dt, mb, lines = lean(path)
        prof = "; ".join(l.strip() for l in lines if "took" in l or "error" in l)[:230]
        print(f"n={n} N={N} {name}: exit {code}, {dt:.1f} s, {mb:.0f} MB | {prof}", flush=True)
