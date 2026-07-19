#!/usr/bin/env python3
"""
sample_canaries.py — build a deterministic regression ("canary") task list
from a Theta SV-COMP benchmark run.

Reads benchmark-results/runs.tsv, keeps rows that were solved CORRECTLY
(category == "correct") in under 60 CPU seconds, groups them by
sv-benchmarks subfolder (the path segment right after "c/"), and picks up
to 2 tasks per subfolder — preferring one task with a 'true' expected
verdict and one with a 'false(...)' verdict, when both are available, so
the canary suite exercises both Safe and Unsafe frontend/backend paths.

For every candidate row it resolves the actual sv-benchmarks .yml task
file, extracts:
  - the primary input file
  - the property file matching the runs.tsv 'properties' column
  - the expected_verdict for that property
  - the options.data_model (ILP32 / LP64)
and verifies that both the .yml and the input file exist on disk before
including the task. Tasks that can't be resolved are skipped (and
reported on stderr) rather than silently ignored.

Selection is fully deterministic: candidates within each subfolder/verdict
bucket are sorted lexicographically by (task path, properties, runset)
before picking, so re-running this script yields byte-identical output
(hence "seeded" — the seed is the sort order, there is no RNG involved).

Usage:
    python3 sample_canaries.py \
        [--runs-tsv PATH] [--sv-benchmarks-root PATH] [--output PATH] \
        [--per-subfolder N]
"""

from __future__ import annotations

import argparse
import csv
import os
import re
import sys
from typing import Any

try:
    import yaml as _pyyaml

    HAVE_PYYAML = True
except ImportError:  # pragma: no cover - exercised only without PyYAML
    _pyyaml = None
    HAVE_PYYAML = False


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_RUNS_TSV = os.path.normpath(os.path.join(SCRIPT_DIR, "..", "runs.tsv"))
DEFAULT_SV_BENCHMARKS_ROOT = os.path.normpath(
    os.path.join(SCRIPT_DIR, "..", "..", "..", "sv-benchmarks")
)
DEFAULT_OUTPUT = os.path.join(SCRIPT_DIR, "canaries.tsv")

OUTPUT_COLUMNS = [
    "task_yml_relpath",
    "input_file_relpath",
    "property",
    "property_file_relpath",
    "expected_verdict",
    "data_model",
    "cputime",
    "subfolder",
]


# ---------------------------------------------------------------------------
# Minimal hand-rolled YAML parser (fallback if PyYAML is unavailable).
#
# sv-benchmarks task .yml files follow a narrow, very regular shape:
#
#   format_version: '2.0'
#   input_files: 'foo.c'          # or a '- item' list
#   properties:
#     - property_file: ../properties/unreach-call.prp
#       expected_verdict: true
#     - property_file: ../properties/coverage-branches.prp
#   options:
#     language: C
#     data_model: ILP32
#
# This parser only supports that shape: top-level scalar/list/mapping
# keys, one level of "- key: value" list-of-mappings nesting, and a flat
# mapping for "options". It is NOT a general YAML parser.
# ---------------------------------------------------------------------------
def _strip_quotes(s: str) -> str:
    s = s.strip()
    if len(s) >= 2 and s[0] == s[-1] and s[0] in "'\"":
        return s[1:-1]
    return s


def _scalar(s: str) -> Any:
    s = s.strip()
    if s == "":
        return None
    low = s.lower()
    if low == "true":
        return True
    if low == "false":
        return False
    return _strip_quotes(s)


def hand_rolled_yaml_load(text: str) -> dict:
    lines = [line for line in text.split("\n") if not line.strip().startswith("#")]
    # Drop fully blank lines but keep indentation info for the rest.
    lines = [line for line in lines if line.strip() != ""]

    result: dict[str, Any] = {}
    i = 0
    n = len(lines)

    def indent_of(line: str) -> int:
        return len(line) - len(line.lstrip(" "))

    while i < n:
        line = lines[i]
        ind = indent_of(line)
        if ind != 0:
            # Shouldn't happen at top level; skip defensively.
            i += 1
            continue
        stripped = line.strip()
        if ":" not in stripped:
            i += 1
            continue
        key, _, rest = stripped.partition(":")
        key = key.strip()
        rest = rest.strip()
        if rest != "":
            # Inline scalar value.
            result[key] = _scalar(rest)
            i += 1
            continue

        # Block value: gather following more-indented lines.
        block = []
        j = i + 1
        while j < n and indent_of(lines[j]) > ind:
            block.append(lines[j])
            j += 1

        if not block:
            result[key] = None
            i = j
            continue

        first_ind = indent_of(block[0])
        if block[0].lstrip().startswith("- "):
            # List. Each item starting with "- " at first_ind begins a
            # new element; may itself be a small mapping (property entries)
            # or a plain scalar (input_files list).
            items: list[Any] = []
            k = 0
            while k < len(block):
                item_line = block[k]
                if indent_of(item_line) != first_ind or not item_line.lstrip().startswith(
                    "- "
                ):
                    k += 1
                    continue
                item_body = item_line.lstrip()[2:]
                # Collect any deeper-indented continuation lines that
                # belong to this list item (extra mapping keys).
                sub_ind = first_ind + 2
                item_map: dict[str, Any] = {}
                if ":" in item_body:
                    ikey, _, ival = item_body.partition(":")
                    ikey = ikey.strip()
                    ival = ival.strip()
                    item_map[ikey] = _scalar(ival) if ival != "" else None
                    k += 1
                    while k < len(block) and indent_of(block[k]) >= sub_ind:
                        cont = block[k].strip()
                        if ":" in cont:
                            ck, _, cv = cont.partition(":")
                            item_map[ck.strip()] = _scalar(cv)
                        k += 1
                    items.append(item_map)
                else:
                    items.append(_scalar(item_body))
                    k += 1
            result[key] = items
        else:
            # Nested mapping (e.g. "options:").
            sub_map: dict[str, Any] = {}
            for sub_line in block:
                sub_stripped = sub_line.strip()
                if ":" not in sub_stripped:
                    continue
                skey, _, sval = sub_stripped.partition(":")
                sub_map[skey.strip()] = _scalar(sval)
            result[key] = sub_map
        i = j

    return result


def load_yaml_file(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        text = f.read()
    if HAVE_PYYAML:
        return _pyyaml.safe_load(text)
    return hand_rolled_yaml_load(text)


# ---------------------------------------------------------------------------
# runs.tsv handling
# ---------------------------------------------------------------------------
TASK_PREFIX_RE = re.compile(r"^\.\./\.\./\.\./sv-benchmarks/")
SUBFOLDER_RE = re.compile(r"^c/([^/]+)/")


def task_relpath_from_sv_benchmarks_root(task_field: str) -> str | None:
    """'../../../sv-benchmarks/c/foo/bar.yml' -> 'c/foo/bar.yml'"""
    if not TASK_PREFIX_RE.match(task_field):
        return None
    return TASK_PREFIX_RE.sub("", task_field)


def subfolder_of(relpath: str) -> str | None:
    m = SUBFOLDER_RE.match(relpath)
    return m.group(1) if m else None


def parse_cputime_seconds(cputime_field: str) -> float | None:
    cputime_field = cputime_field.strip()
    if not cputime_field.endswith("s"):
        return None
    try:
        return float(cputime_field[:-1])
    except ValueError:
        return None


def load_runs(runs_tsv: str) -> list[dict]:
    with open(runs_tsv, "r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f, delimiter="\t")
        return list(reader)


# ---------------------------------------------------------------------------
# Task resolution: runs.tsv row -> canaries.tsv row
# ---------------------------------------------------------------------------
class ResolutionError(Exception):
    pass


def resolve_row(row: dict, sv_benchmarks_root: str) -> dict:
    task_field = row["task"]
    yml_relpath = task_relpath_from_sv_benchmarks_root(task_field)
    if yml_relpath is None:
        raise ResolutionError(f"unexpected task path shape: {task_field!r}")

    subfolder = subfolder_of(yml_relpath)
    if subfolder is None:
        raise ResolutionError(f"could not extract subfolder from: {yml_relpath!r}")

    yml_abspath = os.path.join(sv_benchmarks_root, yml_relpath)
    if not os.path.isfile(yml_abspath):
        raise ResolutionError(f"yml not found: {yml_abspath}")

    try:
        doc = load_yaml_file(yml_abspath)
    except Exception as e:  # noqa: BLE001 - want to report and skip, not crash
        raise ResolutionError(f"failed to parse yml {yml_abspath}: {e}") from e

    if not isinstance(doc, dict):
        raise ResolutionError(f"yml did not parse to a mapping: {yml_abspath}")

    yml_dir_relpath = os.path.dirname(yml_relpath)  # e.g. c/array-examples

    # --- input file -------------------------------------------------
    input_files = doc.get("input_files")
    if isinstance(input_files, list):
        if not input_files:
            raise ResolutionError(f"empty input_files list in {yml_abspath}")
        primary_input = input_files[0]
    elif isinstance(input_files, str):
        primary_input = input_files
    else:
        raise ResolutionError(f"missing/invalid input_files in {yml_abspath}")

    input_file_relpath = os.path.normpath(os.path.join(yml_dir_relpath, primary_input))
    input_file_abspath = os.path.join(sv_benchmarks_root, input_file_relpath)
    if not os.path.isfile(input_file_abspath):
        raise ResolutionError(f"input file not found: {input_file_abspath}")

    # --- property match ----------------------------------------------
    wanted_property = row["properties"].strip()
    properties = doc.get("properties")
    if not isinstance(properties, list):
        raise ResolutionError(f"missing/invalid properties list in {yml_abspath}")

    matched_entry = None
    for entry in properties:
        if not isinstance(entry, dict):
            continue
        pf = entry.get("property_file")
        if not pf:
            continue
        stem = os.path.splitext(os.path.basename(pf))[0]
        if stem == wanted_property:
            matched_entry = entry
            break

    if matched_entry is None:
        raise ResolutionError(
            f"no property entry matching {wanted_property!r} in {yml_abspath}"
        )

    expected_verdict_raw = matched_entry.get("expected_verdict")
    if expected_verdict_raw is None:
        raise ResolutionError(
            f"property entry {wanted_property!r} in {yml_abspath} has no expected_verdict"
        )
    expected_verdict = "true" if expected_verdict_raw is True else "false"

    property_file_relpath = os.path.normpath(
        os.path.join(yml_dir_relpath, matched_entry["property_file"])
    )
    property_file_abspath = os.path.join(sv_benchmarks_root, property_file_relpath)
    if not os.path.isfile(property_file_abspath):
        raise ResolutionError(f"property file not found: {property_file_abspath}")

    # --- data model ----------------------------------------------------
    options = doc.get("options") or {}
    data_model = options.get("data_model") if isinstance(options, dict) else None
    if not data_model:
        raise ResolutionError(f"missing options.data_model in {yml_abspath}")

    cputime = parse_cputime_seconds(row["cputime"])
    if cputime is None:
        raise ResolutionError(f"unparseable cputime: {row['cputime']!r}")

    return {
        "task_yml_relpath": yml_relpath,
        "input_file_relpath": input_file_relpath,
        "property": wanted_property,
        "property_file_relpath": property_file_relpath,
        "expected_verdict": expected_verdict,
        "data_model": data_model,
        "cputime": f"{cputime:.3f}",
        "subfolder": subfolder,
    }


# ---------------------------------------------------------------------------
# Sampling
# ---------------------------------------------------------------------------
def sort_key(row: dict):
    return (row["task"], row["properties"], row["runset"])


def select_for_subfolder(
    rows: list[dict], sv_benchmarks_root: str, per_subfolder: int, errors: list[str]
) -> list[dict]:
    true_rows = sorted(
        (r for r in rows if r["status"] == "true"), key=sort_key
    )
    false_rows = sorted(
        (r for r in rows if r["status"].startswith("false")), key=sort_key
    )

    chosen: list[dict] = []
    chosen_keys: set[tuple] = set()

    def try_resolve(r: dict) -> dict | None:
        try:
            return resolve_row(r, sv_benchmarks_root)
        except ResolutionError as e:
            errors.append(f"[{r['task']} / {r['properties']}] {e}")
            return None

    # Pass 1: one from each verdict bucket, for diversity.
    for bucket in (true_rows, false_rows):
        if len(chosen) >= per_subfolder:
            break
        for r in bucket:
            resolved = try_resolve(r)
            if resolved is None:
                continue
            key = (resolved["task_yml_relpath"], resolved["property"])
            if key in chosen_keys:
                continue
            chosen.append(resolved)
            chosen_keys.add(key)
            break

    # Pass 2: fill remaining quota from either bucket (still deterministic).
    if len(chosen) < per_subfolder:
        combined = sorted(true_rows + false_rows, key=sort_key)
        for r in combined:
            if len(chosen) >= per_subfolder:
                break
            resolved = try_resolve(r)
            if resolved is None:
                continue
            key = (resolved["task_yml_relpath"], resolved["property"])
            if key in chosen_keys:
                continue
            chosen.append(resolved)
            chosen_keys.add(key)

    return chosen


def sample_canaries(
    runs_tsv: str, sv_benchmarks_root: str, per_subfolder: int = 2
) -> tuple[list[dict], list[str]]:
    rows = load_runs(runs_tsv)

    eligible = []
    for row in rows:
        if row.get("category") != "correct":
            continue
        cputime = parse_cputime_seconds(row.get("cputime", ""))
        if cputime is None or cputime >= 60.0:
            continue
        eligible.append(row)

    by_subfolder: dict[str, list[dict]] = {}
    for row in eligible:
        yml_relpath = task_relpath_from_sv_benchmarks_root(row["task"])
        if yml_relpath is None:
            continue
        subfolder = subfolder_of(yml_relpath)
        if subfolder is None:
            continue
        by_subfolder.setdefault(subfolder, []).append(row)

    errors: list[str] = []
    result: list[dict] = []
    for subfolder in sorted(by_subfolder.keys()):
        chosen = select_for_subfolder(
            by_subfolder[subfolder], sv_benchmarks_root, per_subfolder, errors
        )
        result.extend(chosen)

    result.sort(key=lambda r: (r["subfolder"], r["task_yml_relpath"], r["property"]))
    return result, errors


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runs-tsv", default=DEFAULT_RUNS_TSV)
    ap.add_argument("--sv-benchmarks-root", default=DEFAULT_SV_BENCHMARKS_ROOT)
    ap.add_argument("--output", default=DEFAULT_OUTPUT)
    ap.add_argument(
        "--per-subfolder",
        type=int,
        default=2,
        help="max canaries to sample per sv-benchmarks subfolder (default: 2)",
    )
    args = ap.parse_args()

    if not HAVE_PYYAML:
        print(
            "note: PyYAML not importable, using hand-rolled fallback YAML parser",
            file=sys.stderr,
        )

    if not os.path.isdir(args.sv_benchmarks_root):
        print(
            f"error: sv-benchmarks root not found: {args.sv_benchmarks_root}",
            file=sys.stderr,
        )
        return 1

    canaries, errors = sample_canaries(
        args.runs_tsv, args.sv_benchmarks_root, args.per_subfolder
    )

    with open(args.output, "w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=OUTPUT_COLUMNS, delimiter="\t")
        writer.writeheader()
        for row in canaries:
            writer.writerow(row)

    subfolders = sorted({r["subfolder"] for r in canaries})
    by_property: dict[str, int] = {}
    for r in canaries:
        by_property[r["property"]] = by_property.get(r["property"], 0) + 1

    print(f"wrote {len(canaries)} canaries to {args.output}", file=sys.stderr)
    print(f"covering {len(subfolders)} subfolders", file=sys.stderr)
    print(f"by property: {by_property}", file=sys.stderr)
    if errors:
        print(f"{len(errors)} candidate rows could not be resolved:", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
