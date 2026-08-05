import bz2, glob, os, re, sys, xml.etree.ElementTree as ET
from collections import defaultdict

def load(d):
    out = {}
    for f in glob.glob(os.path.join(d, "*.xml.bz2")):
        try:
            root = ET.parse(bz2.open(f)).getroot()
        except Exception:
            continue
        blockname = root.get("name") or ""
        for run in root.iter("run"):
            name = run.get("name")
            props = run.get("properties") or ""
            status = expected = category = None
            for col in run.iter("column"):
                t = col.get("title")
                if t == "status": status = col.get("value")
                elif t == "category": category = col.get("value")
            key = (name, props)
            # keep the first seen; identical task may appear once per block
            if key not in out:
                out[key] = (status, category)
    return out

a = load(sys.argv[1])   # before (run 79)
b = load(sys.argv[2])   # after  (run 84)
print(f"run79 runs: {len(a)}   run84 runs: {len(b)}   common: {len(set(a)&set(b))}")

def cat(v): return (v or "?")
ca = defaultdict(int); cb = defaultdict(int)
for k,(s,c) in a.items(): ca[cat(c)] += 1
for k,(s,c) in b.items(): cb[cat(c)] += 1
print("\ncategory totals")
for c in sorted(set(ca)|set(cb)):
    print(f"  {c:14s} 79={ca[c]:6d}  84={cb[c]:6d}  delta={cb[c]-ca[c]:+d}")

common = set(a) & set(b)
regress = []   # correct in 79, wrong in 84
gained  = []   # wrong in 79, correct in 84
newwrong= []   # not-wrong in 79 (timeout/error/unknown), wrong in 84
for k in common:
    sa, cta = a[k]; sb, ctb = b[k]
    if cta == "correct" and ctb == "wrong": regress.append((k, sa, sb))
    elif cta == "wrong" and ctb == "correct": gained.append((k, sa, sb))
    elif cta not in ("correct","wrong") and ctb == "wrong": newwrong.append((k, sa, sb, cta))

print(f"\nREGRESSIONS (correct in 79 -> wrong in 84): {len(regress)}")
for (n,p),sa,sb in sorted(regress)[:40]: print(f"  {n}  [{p}]  {sa} -> {sb}")
print(f"\nNEWLY WRONG from non-answer (79 {'timeout/error/unknown'} -> wrong in 84): {len(newwrong)}")
for (n,p),sa,sb,cta in sorted(newwrong)[:40]: print(f"  {n}  [{p}]  {cta}/{sa} -> {sb}")
print(f"\nFIXED (wrong in 79 -> correct in 84): {len(gained)}")
for (n,p),sa,sb in sorted(gained)[:60]: print(f"  {n}  [{p}]  {sa} -> {sb}")

def score(runs):
    s = 0; n = {"ct":0,"cf":0,"wt":0,"wf":0}
    for (st, ct) in runs.values():
        if not st: continue
        t = st.startswith("true")
        f = st.startswith("false")
        if ct == "correct":
            if t: s += 2; n["ct"] += 1
            elif f: s += 1; n["cf"] += 1
        elif ct == "wrong":
            if t: s -= 32; n["wt"] += 1
            elif f: s -= 16; n["wf"] += 1
    return s, n

sa_, na_ = score(a); sb_, nb_ = score(b)
print(f"\nSV-COMP score  run79={sa_}   run84={sb_}   delta={sb_-sa_:+d}")
print(f"  correct true : {na_['ct']:6d} -> {nb_['ct']:6d}  ({nb_['ct']-na_['ct']:+d})")
print(f"  correct false: {na_['cf']:6d} -> {nb_['cf']:6d}  ({nb_['cf']-na_['cf']:+d})")
print(f"  WRONG true   : {na_['wt']:6d} -> {nb_['wt']:6d}  ({nb_['wt']-na_['wt']:+d})   [-32 each]")
print(f"  WRONG false  : {na_['wf']:6d} -> {nb_['wf']:6d}  ({nb_['wf']-na_['wf']:+d})   [-16 each]")
