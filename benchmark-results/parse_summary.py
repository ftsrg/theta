#!/usr/bin/env python3
"""Summarise a *parse-only* benchmark run (`--backend NONE`).

With the backend disabled every task reports one of a small set of statuses, so the run
measures the frontend alone across the whole benchmark:

  unknown                                    the file parsed and built an XCFA (success)
  ERROR (frontend failed, before parsing …)  the C frontend threw before finishing
  ERROR (frontend failed, after parsing …)   parsing finished, a later pass threw
  ERROR (Unsupported source element, …)      an explicit refusal
  TIMEOUT (… parsing finished)               parsing itself did not finish in the limit

The `before`/`after` split is the useful one: `--backend NONE` run locally can only ever
observe the `before` kind, because an `after` failure needs the pass pipeline to run.

Usage:  parse_summary.py <results-dir> [--by-family] [--files <status-substring>]
"""

import bz2
import collections
import glob
import os
import re
import sys
import xml.etree.ElementTree as ET


def load(results_dir):
    """Yield (task-name, run-definition, status) for every run in the directory."""
    for path in sorted(glob.glob(os.path.join(results_dir, "*.xml.bz2"))):
        try:
            root = ET.parse(bz2.open(path)).getroot()
        except Exception as exc:  # a truncated file should not lose the other 54
            print(f"  ! skipping {os.path.basename(path)}: {exc}", file=sys.stderr)
            continue
        rundef = root.get("name") or os.path.basename(path)
        for run in root.iter("run"):
            status = None
            for col in run.iter("column"):
                if col.get("title") == "status":
                    status = col.get("value")
            yield run.get("name"), rundef, status


def family(task):
    """The sv-benchmarks directory a task lives in, which is how the sets are organised."""
    m = re.search(r"/c/([^/]+)/", task or "")
    return m.group(1) if m else "?"


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        return 1
    results_dir = args[0]
    want_files = None
    if "--files" in args:
        want_files = args[args.index("--files") + 1]

    runs = list(load(results_dir))
    if not runs:
        print(f"no results found in {results_dir}", file=sys.stderr)
        return 1

    buckets = collections.Counter(status for _, _, status in runs)
    total = len(runs)
    print(f"{total} task-runs in {results_dir}\n")
    print(f"{'status':<52} {'runs':>7}  {'share':>6}")
    print("-" * 70)
    for status, n in buckets.most_common():
        print(f"{str(status):<52} {n:>7}  {100 * n / total:>5.1f}%")

    # The headline number: how much of the benchmark the frontend can actually deliver
    # to a backend. Everything else scores 0 before verification even starts.
    ok = buckets.get("unknown", 0)
    print(f"\nparsed successfully: {ok}/{total} ({100 * ok / total:.1f}%)")

    if "--by-family" in args:
        for kind in ("before", "after"):
            per = collections.Counter(
                family(task)
                for task, _, status in runs
                if status and f"frontend failed, {kind}" in status
            )
            if not per:
                continue
            print(f"\nfrontend failed, {kind} parsing — by family (top 25)")
            print("-" * 70)
            for fam, n in per.most_common(25):
                print(f"  {fam:<50} {n:>6}")

    if want_files:
        hits = sorted({task for task, _, status in runs if status and want_files in status})
        print(f"\n{len(hits)} distinct tasks matching {want_files!r}")
        for task in hits:
            print(f"  {task}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
