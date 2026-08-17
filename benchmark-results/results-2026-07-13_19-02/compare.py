#!/usr/bin/env python3
"""Compare the new run against the old baseline, per-task."""
import csv, os, collections

BASE = "/home/levente/Documents/University/theta/benchmark-results"
OLD = os.path.join(BASE, "runs.tsv")
NEW = os.path.join(BASE, "results-2026-07-13_19-02", "runs_new.tsv")

def norm(t):
    i = t.find("sv-benchmarks/c/")
    return t[i+len("sv-benchmarks/c/"):] if i >= 0 else t

def load(path):
    d = {}
    with open(path) as fh:
        for r in csv.DictReader(fh, delimiter="\t"):
            key = (norm(r["task"]), r["properties"])
            d[key] = r
    return d

def bucket(r):
    cat, st = r["category"], r["status"]
    if cat == "correct": return "correct"
    if cat == "wrong":   return "wrong"
    if st.startswith("TIMEOUT"):        return "timeout"
    if "OUT OF MEMORY" in st:           return "oom"
    if "before parsing finished" in st: return "fe_before"
    if "solver error" in st:            return "solver"
    if "after parsing finished" in st:  return "fe_after"
    if cat == "unknown" or st == "unknown": return "unknown"
    return "other:" + st

old, new = load(OLD), load(NEW)
ORDER = ["correct","wrong","unknown","fe_before","fe_after","solver","timeout","oom"]

def summary(d):
    c = collections.Counter(bucket(r) for r in d.values())
    return c

so, sn = summary(old), summary(new)
allk = ORDER + sorted(set(list(so)+list(sn)) - set(ORDER))
print(f"{'bucket':<14}{'OLD':>8}{'NEW':>8}{'Δ':>8}")
for k in allk:
    print(f"{k:<14}{so.get(k,0):>8}{sn.get(k,0):>8}{sn.get(k,0)-so.get(k,0):>+8}")
print(f"{'TOTAL':<14}{sum(so.values()):>8}{sum(sn.values()):>8}")

# per-task transitions
common = set(old) & set(new)
print(f"\ncommon tasks: {len(common)}  (old-only {len(set(old)-set(new))}, new-only {len(set(new)-set(old))})")

# WRONG results in new run
print("\n=== NEW wrong results ===")
wrong_new = [(k, new[k]) for k in new if new[k]["category"] == "wrong"]
for (task, prop), r in sorted(wrong_new):
    was = old.get((task, prop), {}).get("category", "MISSING")
    print(f"  [{r['status']:<28}] was={was:<8} {r['properties']:<12} {task}")

# newly-wrong (correct or error before, wrong now) -- the regressions that matter
print("\n=== transitions INTO wrong (by what they were) ===")
tr = collections.Counter()
for k in common:
    if new[k]["category"] == "wrong":
        tr[bucket(old[k])] += 1
for b, n in tr.most_common():
    print(f"  {b:<12} -> wrong : {n}")

# transitions OUT of wrong (old wrong, now not)
fixed = [k for k in common if old[k]["category"]=="wrong" and new[k]["category"]!="wrong"]
print(f"\n=== old wrong now NOT wrong: {len(fixed)} ===")
for k in sorted(fixed):
    print(f"  {bucket(new[k]):<10} {k[1]:<12} {k[0]}")
