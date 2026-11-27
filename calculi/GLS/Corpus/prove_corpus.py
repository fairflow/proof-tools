#!/usr/bin/env python3
"""`glsrun prove` on every entry of the corpus, and on some members of
the families.

Each sequent is given to the command as text, three times: in the
source's notation (`Seq.show`), as Lean source (`Seq.src`) and with the
signs of a keyboard (`Seq.ascii`), as `glsrun corpus` and `glsrun
families` print them.  The exit code is compared with the recorded
status: 0 for a sequent recorded derivable, 1 for one recorded not
derivable; and the three answers are compared with one another.

With `--elaborate`, the file the command prints for each sequent is
written to `Corpus/out/prove/<name>.lean` and elaborated (`lake env lean
-M 4000`, under a deadline that ends the whole process group): the kernel
then checks its certificate.  The third kind of answer, a derivation
checked over sets only, is asked for by `--sets` on two sequents, since
no sequent of the corpus or of the families gives it otherwise.  Three
files, one of each kind of answer, are then altered in their
certificates and must be refused.

Run from `calculi/GLS/` after `lake build GLS glsrun`:
    python3 -I Corpus/prove_corpus.py [--elaborate]
Exit code 0 if nothing disagrees, every file elaborates and every
altered file is refused.
"""
import subprocess, sys, os, signal, re

EXE = ".lake/build/bin/glsrun"
ELABORATE = "--elaborate" in sys.argv
DEADLINE = 120.0
WORD = {0: "derivable", 1: "not derivable", 2: "not read", 3: "flag"}

def run(cmd, deadline=DEADLINE):
    """Run under a deadline; at the deadline the whole process group ends."""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True, start_new_session=True)
    try:
        out, err = p.communicate(timeout=deadline)
        return p.returncode, out, err
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        return None, "", "cut off at the deadline"

def elaborate(path):
    code, out, err = run(["lake", "env", "lean", "-M", "4000", path])
    good = code == 0 and "error" not in out and "sorry" not in out
    return good, (out + err).strip().splitlines()[:1]

def kind(text):
    if "def proof : Fam sequent" in text:
        return "derivable, the derivation as data"
    if "setCert.verdict" in text:
        return "derivable, the proposition only"
    if "def countermodel" in text:
        return "not derivable, a countermodel"
    return "no fact"

entries = []
for listing in ("corpus", "families"):
    code, out, _ = run([EXE, listing])
    entries += [line.split("\t") for line in out.splitlines()]
if ELABORATE:
    os.makedirs("Corpus/out/prove", exist_ok=True)

counts, kinds, disagree, bad, printed, texts = {}, {}, 0, 0, {}, {}
print("| sequent | recorded | from the source's notation | from Lean source | from the signs of a keyboard | the answer |" +
      (" elaborated |" if ELABORATE else ""))
print("|---|---|---|---|---|---|" + ("---|" if ELABORATE else ""))
for name, status, shown, src, ascii in entries:
    want = 0 if status == "derivable" else 1
    c1, o1, _ = run([EXE, "prove", shown])
    c2, o2, _ = run([EXE, "prove", src])
    c3, o3, _ = run([EXE, "prove", ascii])
    ok = c1 == want and c2 == want and c3 == want and o1 == o2 == o3
    if not ok:
        disagree += 1
    word = WORD.get(c1, "cut off")
    counts[word] = counts.get(word, 0) + 1
    k = kind(o1)
    kinds[k] = kinds.get(k, 0) + 1
    printed[name] = o1
    texts[name] = shown
    row = f"| `{name}` | {status} | {word} | {WORD.get(c2, 'cut off')} | {WORD.get(c3, 'cut off')} | {k} |"
    if ELABORATE:
        path = f"Corpus/out/prove/{name}.lean"
        with open(path, "w") as f:
            f.write(o1)
        good, first = elaborate(path)
        if not good:
            bad += 1
        row += " yes |" if good else f" NO: {first} |"
    print(row + ("" if ok else " DISAGREES"))

print()
print(f"{len(entries)} sequents; by verdict: " +
      ", ".join(f"{k} {v}" for k, v in sorted(counts.items())) +
      "; by kind of answer: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) +
      f"; disagreeing with the recorded status, or the three texts answered differently: {disagree}" +
      (f"; files not elaborated: {bad}" if ELABORATE else ""))

# The third kind of answer: a derivation checked over sets only.
print()
for name in ("axLob", "boxChain_32"):
    code, out, _ = run([EXE, "prove", "--sets", texts[name]])
    k = kind(out)
    good = code == 0 and k == "derivable, the proposition only"
    line = f"`{name}` with `--sets`: {k}"
    if ELABORATE and good:
        path = f"Corpus/out/prove/{name}_sets.lean"
        with open(path, "w") as f:
            f.write(out)
        good, first = elaborate(path)
        line += "; elaborated" if good else f"; NOT elaborated: {first}"
    if not good:
        bad += 1
    printed[name + "_sets"] = out
    print(line)

# One file of each kind with its certificate altered: each must be refused.
ALTER = [
    ("axLob", r"GLS\.Move\.idP\s+0", "GLS.Move.idP 7", "the last move IdP p made IdP p7"),
    ("boxChain_32", r"GLS\.Move\.idP\s+0", "GLS.Move.idP 7", "the last move IdP p made IdP p7"),
    ("boxChain_32_sets", r"GLS\.Move\.idP\s+0", "GLS.Move.idP 7", "the last move IdP p made IdP p7"),
    ("notT", r"GLS\.Tree\.node \[\] \[\]", "GLS.Tree.node [0] []", "p made true at the root"),
]
accepted = 0
if ELABORATE:
    print()
    for name, old, new, what in ALTER:
        text = printed[name]
        found = list(re.finditer(old, text))
        altered = text[:found[-1].start()] + new + text[found[-1].end():] if found else text
        if altered == text:
            print(f"altered `{name}`: the text to alter was not found: NOT CHECKED")
            accepted += 1
            continue
        path = f"Corpus/out/prove/{name}_altered.lean"
        with open(path, "w") as f:
            f.write(altered)
        good, first = elaborate(path)
        if good:
            accepted += 1
        print(f"altered `{name}` ({kind(text)}; {what}): " +
              ("ACCEPTED, which is a fault" if good else f"refused: {first}"))

sys.exit(0 if disagree == 0 and bad == 0 and accepted == 0 else 1)
