import sys; sys.path.insert(0, "Corpus/experiments"); import os; os.makedirs("Corpus/out/exp", exist_ok=True)
from h import *
C = {
 "checked of refutedBy": "theorem checked : refutedBy saturated sequent = true := by decide +kernel",
 "checked through the certifier": "theorem checked : noCFBySet.check sequent saturated = true := by decide +kernel",
}
n = int(sys.argv[1]); d = defs(nochain(n))
for name, c in C.items():
    path = f"Corpus/out/exp/e3.lean"
    open(path, "w").write(d + "set_option Elab.async false\nset_option profiler true\nset_option profiler.threshold 50\n" + c +
      "\ntheorem notCutFree : ¬ CFDerivable sequent := noCFBySet.verdict _ saturated checked\n" +
      "theorem notDerivable : ¬ Derivable sequent := noDerivableBySet.verdict _ saturated checked\nend DILL.Answer\n")
    code, dt, mb, lines = lean(path, mem=4000, deadline=200, show=30)
    print(f"n={n} {name}: exit {code}, {dt:.1f} s, peak {mb:.0f} MB")
    for l in lines:
        if "took" in l or "error" in l: print("    " + l.strip()[:160])
