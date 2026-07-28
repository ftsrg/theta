#!/usr/bin/env python3
"""Compare two BenchExec result dirs task-by-task (baseline=batch60, new=batch61)."""
import bz2, glob, os, sys
import xml.etree.ElementTree as ET

import sys
BASE = sys.argv[1]
NEW  = sys.argv[2]

def load(dirpath):
    """Return {(runset, task): (category, status, expected, properties)} choosing runset-level files."""
    all_files = sorted(glob.glob(os.path.join(dirpath, "*.xml.bz2")))
    runset_files = [f for f in all_files if ".C." not in os.path.basename(f)]
    covered = set()
    for f in runset_files:
        rs = os.path.basename(f).split(".results.")[1][:-len(".xml.bz2")]
        covered.add(rs)
    chosen = list(runset_files)
    for f in all_files:
        base = os.path.basename(f)
        if ".C." not in base:
            continue
        rs = base.split(".results.")[1].split(".C.")[0]
        if rs not in covered:
            chosen.append(f)
    out = {}
    for f in chosen:
        with bz2.open(f, "rb") as fh:
            root = ET.parse(fh).getroot()
        runset = root.get("name")
        for run in root.iter("run"):
            cols = {c.get("title"): c.get("value") for c in run.findall("column")}
            key = (runset, run.get("name"))
            out[key] = (cols.get("category", ""), cols.get("status", ""),
                        run.get("expectedVerdict", ""), run.get("properties", ""))
    return out

base = load(BASE)
new = load(NEW)

print(f"baseline tasks: {len(base)}   new tasks: {len(new)}")

def tally(d):
    from collections import Counter
    c = Counter()
    for cat, status, exp, prop in d.values():
        c[cat] += 1
    return c

def score(d):
    """SV-COMP scoring: correct true +2, correct false +1, wrong true -32, wrong false -16."""
    s = 0
    cc = wc = 0
    for cat, status, exp, prop in d.values():
        if cat == "correct":
            cc += 1
            s += 2 if exp == "true" else 1
        elif cat == "wrong":
            wc += 1
            # SV-COMP penalty is on what the tool SAID: wrong "true" -> -32, wrong "false" -> -16
            s += -32 if status.startswith("true") else -16
    return s

from collections import Counter
print("baseline categories:", dict(tally(base)))
print("new categories:     ", dict(tally(new)))

# Per-task transitions
common = set(base) & set(new)
only_base = set(base) - set(new)
only_new = set(new) - set(base)
print(f"\ncommon: {len(common)}  only_base: {len(only_base)}  only_new: {len(only_new)}")

trans = Counter()
gained = []   # became correct in new (was not correct in base)
lost = []     # was correct in base, not correct in new
new_wrong = []  # became wrong in new (was not wrong in base)
fixed_wrong = []  # was wrong in base, not wrong in new
for key in common:
    bc = base[key][0]
    nc = new[key][0]
    if bc != nc:
        trans[(bc, nc)] += 1
    if nc == "correct" and bc != "correct":
        gained.append(key)
    if bc == "correct" and nc != "correct":
        lost.append(key)
    if nc == "wrong" and bc != "wrong":
        new_wrong.append(key)
    if bc == "wrong" and nc != "wrong":
        fixed_wrong.append(key)

print("\n=== category transitions (base -> new): count ===")
for (a, b), n in sorted(trans.items(), key=lambda x: -x[1]):
    print(f"  {a:10s} -> {b:10s}: {n}")

print(f"\ngained correct: {len(gained)}   lost correct: {len(lost)}")
print(f"new wrong: {len(new_wrong)}   fixed wrong: {len(fixed_wrong)}")

def short(key):
    rs, task = key
    return f"{rs.replace('SV-COMP27_','')}  {task.split('/')[-1]}"

print("\n=== NEW WRONG (regressions) ===")
for key in sorted(new_wrong, key=short):
    print(f"  {short(key)}\n      base={base[key][0]}/{base[key][1]!r}  new={new[key][0]}/{new[key][1]!r} exp={new[key][2]}")

print("\n=== FIXED WRONG (base wrong -> new not-wrong) ===")
for key in sorted(fixed_wrong, key=short):
    print(f"  {short(key)}\n      base={base[key][0]}/{base[key][1]!r}  new={new[key][0]}/{new[key][1]!r} exp={new[key][2]}")

print(f"\n=== SCORE  base={score(base)}   new={score(new)}   delta={score(new)-score(base)} ===")
