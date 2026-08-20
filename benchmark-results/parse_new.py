#!/usr/bin/env python3
"""Parse BenchExec result XMLs into one TSV of runs."""
import bz2, glob, os, csv, sys
import xml.etree.ElementTree as ET

RESULTS_DIR = "/home/levente/Documents/University/theta/benchmark-results/results-2026-07-13_19-02"
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results-2026-07-13_19-02/runs_new.tsv")

# Prefer runset-level files; fall back to block-level for runsets without one.
all_files = sorted(glob.glob(os.path.join(RESULTS_DIR, "*.xml.bz2")))
# runset-level files look like ...results.<RUNSET>.xml.bz2 where RUNSET has no ".C." block suffix
runset_files = [f for f in all_files if ".C." not in os.path.basename(f)]
runsets_covered = set()
for f in runset_files:
    base = os.path.basename(f)
    rs = base.split(".results.")[1][:-len(".xml.bz2")]
    runsets_covered.add(rs)
chosen = list(runset_files)
for f in all_files:
    base = os.path.basename(f)
    if ".C." not in base:
        continue
    rs = base.split(".results.")[1].split(".C.")[0]
    if rs not in runsets_covered:
        chosen.append(f)

rows = []
for f in chosen:
    base = os.path.basename(f)
    name_part = base.split(".results.")[1][:-len(".xml.bz2")]
    with bz2.open(f, "rb") as fh:
        tree = ET.parse(fh)
    root = tree.getroot()
    runset = root.get("name")
    for run in root.iter("run"):
        cols = {c.get("title"): c.get("value") for c in run.findall("column")}
        rows.append({
            "runset": runset,
            "task": run.get("name"),
            "properties": run.get("properties"),
            "expected": run.get("expectedVerdict"),
            "status": cols.get("status", ""),
            "category": cols.get("category", ""),
            "error_col": cols.get("Error", ""),
            "successful_config": cols.get("Successful config", ""),
            "portfolio": cols.get("Portfolio", ""),
            "arithmetic": cols.get("Arithmetic", ""),
            "cputime": cols.get("cputime", ""),
            "terminationreason": cols.get("terminationreason", ""),
            "exitsignal": cols.get("exitsignal", ""),
            "memory": cols.get("memory", ""),
        })

with open(OUT, "w", newline="") as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()), delimiter="\t")
    w.writeheader()
    w.writerows(rows)
print(f"{len(chosen)} files, {len(rows)} runs -> {OUT}")
