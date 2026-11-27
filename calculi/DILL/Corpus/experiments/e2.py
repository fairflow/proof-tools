import sys; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
V = {
 "V2": "theorem c : noCFBySet.check sequent saturated = true := by decide +kernel",
 "V1": "theorem c : refutedBy saturated sequent = true := by decide +kernel",
}
n = 5; d = defs(nochain(n)); mem = int(sys.argv[2])
name = sys.argv[1]
path = f"Corpus/out/exp/e2_{name}.lean"
open(path, "w").write(d + "set_option profiler true\n" + V[name] + "\nend DILL.Answer\n")
code, dt, mb, lines = lean(path, mem=mem, deadline=200)
print(f"n={n} {name} -M {mem}: exit {code}, {dt:.1f} s, peak {mb:.0f} MB | " + "; ".join(l.strip() for l in lines)[:400], flush=True)
