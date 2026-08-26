#!/usr/bin/env python3
"""
build_guard_set.py — build guard_set.tsv: the wrong-result regression
guard set.

Takes every runs.tsv row with category == "wrong" (there were 13 in the
2026-07-06 SV-COMP27 run at the time this was written) and, for each one,
adds up to 2 "neighbor" tasks: correctly-solved (category == "correct",
cputime < 60s) tasks from the *same* sv-benchmarks subfolder, picked with
the same true/false-diversity, fully deterministic selection logic as
sample_canaries.py. Neighbors give a fast smoke signal that a fix for the
wrong task didn't regress sibling tasks in the same benchmark family.

Output columns match canaries.tsv, plus a leading 'kind' column
('wrong' or 'neighbor') and a 'wrong_task_yml_relpath' column tying each
neighbor back to the wrong task it was picked for ('' for wrong rows
themselves).

Usage:
    python3 build_guard_set.py \
        [--runs-tsv PATH] [--sv-benchmarks-root PATH] [--output PATH]
"""

from __future__ import annotations

import argparse
import csv
import os
import sys

import sample_canaries as sc

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_OUTPUT = os.path.join(SCRIPT_DIR, "guard_set.tsv")

OUTPUT_COLUMNS = ["kind", "wrong_task_yml_relpath"] + sc.OUTPUT_COLUMNS


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runs-tsv", default=sc.DEFAULT_RUNS_TSV)
    ap.add_argument("--sv-benchmarks-root", default=sc.DEFAULT_SV_BENCHMARKS_ROOT)
    ap.add_argument("--output", default=DEFAULT_OUTPUT)
    ap.add_argument("--neighbors-per-wrong", type=int, default=2)
    args = ap.parse_args()

    rows = sc.load_runs(args.runs_tsv)

    wrong_rows = [r for r in rows if r.get("category") == "wrong"]
    wrong_rows.sort(key=sc.sort_key)

    correct_eligible = []
    for row in rows:
        if row.get("category") != "correct":
            continue
        cputime = sc.parse_cputime_seconds(row.get("cputime", ""))
        if cputime is None or cputime >= 60.0:
            continue
        correct_eligible.append(row)

    by_subfolder: dict[str, list[dict]] = {}
    for row in correct_eligible:
        yml_relpath = sc.task_relpath_from_sv_benchmarks_root(row["task"])
        if yml_relpath is None:
            continue
        subfolder = sc.subfolder_of(yml_relpath)
        if subfolder is None:
            continue
        by_subfolder.setdefault(subfolder, []).append(row)

    errors: list[str] = []
    output_rows: list[dict] = []

    for wrow in wrong_rows:
        yml_relpath = sc.task_relpath_from_sv_benchmarks_root(wrow["task"])
        if yml_relpath is None:
            errors.append(f"[wrong task] unexpected task path shape: {wrow['task']!r}")
            continue
        subfolder = sc.subfolder_of(yml_relpath)
        try:
            resolved = sc.resolve_row(wrow, args.sv_benchmarks_root)
        except sc.ResolutionError as e:
            errors.append(f"[wrong: {wrow['task']} / {wrow['properties']}] {e}")
            continue

        output_rows.append({"kind": "wrong", "wrong_task_yml_relpath": "", **resolved})

        # Neighbors: same selection logic as sample_canaries, but exclude
        # the wrong task's own yml (even under a different property) so
        # neighbors are genuinely different tasks.
        candidates = [
            r
            for r in by_subfolder.get(subfolder, [])
            if sc.task_relpath_from_sv_benchmarks_root(r["task"]) != yml_relpath
        ]
        neighbor_errors: list[str] = []
        neighbors = sc.select_for_subfolder(
            candidates, args.sv_benchmarks_root, args.neighbors_per_wrong, neighbor_errors
        )
        for e in neighbor_errors:
            errors.append(f"[neighbor of {wrow['task']}] {e}")
        for n in neighbors:
            output_rows.append(
                {"kind": "neighbor", "wrong_task_yml_relpath": yml_relpath, **n}
            )

    with open(args.output, "w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=OUTPUT_COLUMNS, delimiter="\t")
        writer.writeheader()
        for row in output_rows:
            writer.writerow(row)

    n_wrong = sum(1 for r in output_rows if r["kind"] == "wrong")
    n_neighbor = sum(1 for r in output_rows if r["kind"] == "neighbor")
    print(
        f"wrote {len(output_rows)} rows to {args.output} "
        f"({n_wrong} wrong + {n_neighbor} neighbors)",
        file=sys.stderr,
    )
    if errors:
        print(f"{len(errors)} rows could not be resolved:", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
