#!/usr/bin/env python3
"""Saturated sets on the two families `bots` and `parBots`: the producer,
the two compiled checks, and the kernel on the two written forms.

    python3 -I Corpus/measure_sets.py bots 1 3 5 7 --lists
    python3 -I Corpus/measure_sets.py parBots 10 13

Run in calculi/MALL after `lake build MALL mallrun`.  For each member:
`mallrun refute <family> <n>` (with `--lists`: also the compiled check of
the set as lists, and the set written as lists), then Lean on the file in
numbers, and with `--lists` on the file in lists (`--lists-compiled`: the
compiled check of the lists only).  Each Lean run is one
process group under a deadline, with `-M <cap>` megabytes (default 4000);
one at a time.  The table is printed in Markdown.  Peak memory is that of
the process less that of a file with the imports alone.
"""
import os, re, signal, subprocess, sys, time

X = ".lake/build/bin/mallrun"
OUT = "Corpus/out/"

def run(cmd, deadline):
    t = time.monotonic()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         start_new_session=True)
    try:
        out, err = p.communicate(timeout=deadline)
        return p.returncode, out, err, time.monotonic() - t
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        return None, "", "", time.monotonic() - t

def lean(path, cap, deadline):
    code, out, err, dt = run(["/usr/bin/time", "-l", "lake", "env", "lean", "-M", str(cap), path], deadline)
    if code is None:
        return f"cut off at {deadline} s", dt, None
    m = re.search(r"(\d+)\s+maximum resident set size", err)
    rss = int(m.group(1)) / 2**20 if m else None
    # the lines of /usr/bin/time speak of memory too: look at Lean's own
    text = out + "\n".join(l for l in err.split("\n") if not l.startswith("  ") and " real " not in l)
    if code == 0 and "error" not in out:
        return "checked", dt, rss
    if "excessive memory" in text or "out of memory" in text:
        return f"stopped at the cap of {cap} MB", dt, rss
    if "Stack overflow" in text:
        return "stack overflow", dt, rss
    return "FAILED: " + " ".join(text.split())[:120], dt, rss

def main():
    args = sys.argv[1:]
    lists = "--lists" in args or "--lists-compiled" in args
    kernel_lists = "--lists" in args
    cap = 4000
    deadline = 300
    for a in args:
        if a.startswith("--cap="): cap = int(a[6:])
        if a.startswith("--deadline="): deadline = int(a[11:])
    fam = args[0]
    ns = [int(a) for a in args[1:] if a.isdigit()]
    os.makedirs(OUT, exist_ok=True)
    base = OUT + "imports_only.lean"
    open(base, "w").write("import MALL.Corpus.Basic\nimport MALL.SatRun\n")
    _, bt, brss = lean(base, cap, deadline)
    print(f"imports alone: {bt:.1f} s, {brss:.0f} MB\n")
    print("| family | n | sequents | found | lists, compiled | numbers, compiled | lists, kernel | numbers, kernel |")
    print("|---|---|---|---|---|---|---|---|")
    for n in ns:
        code, out, _, dt = run([X, "refute", fam, str(n)] + (["--lists"] if lists else []), 120)
        m = re.search(r"a set of (\d+) .*found in (\d+) µs.*the check in numbers: (\w+), (\d+) µs", out)
        if not m:
            # the check as lists did not end: the line of the set in numbers is still wanted
            code, out, _, dt = run([X, "refute", fam, str(n)], 120)
            m = re.search(r"a set of (\d+) .*found in (\d+) µs.*the check in numbers: (\w+), (\d+) µs", out)
            lc = "not ended in 120 s" if lists else "not run"
            wrote_lists = False
        else:
            ml = re.search(r"as lists: (\w+), (\d+) µs", out)
            lc = f"{int(ml.group(2)) / 1000:.1f} ms" if ml else "not run"
            wrote_lists = ml is not None
        if not m:
            print(f"| `{fam}` | {n} | no set within 120 s | | | | | |", flush=True)
            continue
        size, found, ok, chk = m.group(1), int(m.group(2)), m.group(3), int(m.group(4))
        def cell(path):
            why, t, rss = lean(path, cap, deadline)
            extra = f", {t - bt:.1f} s" + (f", {max(rss - brss, 0):.0f} MB" if rss else "")
            return why + extra
        kl = cell(f"{OUT}{fam}_{n}_lists.lean") if wrote_lists and kernel_lists else "not run"
        kn = cell(f"{OUT}{fam}_{n}_set.lean")
        print(f"| `{fam}` | {n} | {size} | {found / 1000:.1f} ms | {lc} | {chk / 1000:.2f} ms ({ok}) | {kl} | {kn} |",
              flush=True)

main()
