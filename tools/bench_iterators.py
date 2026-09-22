#!/usr/bin/env python3
"""Measure all iterator workloads with the full runner's calibration gates.

Run benchmarks/bench.py --build first. This verifies the manifest before reuse.
It does not change the workload, sample count, or reference implementation.
"""
import json
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "benchmarks"))
import bench
import run
from workloads import TABLE


def main():
    bench.verify_build()
    destination = ROOT / "build/iterator-performance"
    destination.mkdir(parents=True, exist_ok=True)
    rows = [row for row in TABLE if row["structure"] == "dlist_iterator"]
    report = {
        "scope": "DLL iterator only; all 11 operations at all 3 nonempty sizes",
        "target_ratio": 2.5,
        "environment": run.environment(),
        "source_sha256": bench.fingerprints(),
        "build_manifest": json.loads(bench.MANIFEST.read_text()),
        "expected_rows": len(rows),
        "acceptance": False,
        "results": [],
    }
    log = []
    for row in rows:
        try:
            result = run.measure(run.BENDBIN / "dlist_iterator",
                                 run.REFBIN / "dlist_iterator", row, log)
            result["median_bend_ns"] = statistics.median(result["bend_ns"])
            result["median_c_ns"] = statistics.median(result["reference_ns"])
            result["ratio"] = result["median_bend_ns"] / result["median_c_ns"]
            result["sample_ratios"] = [b / c for b, c in
                                       zip(result["bend_ns"], result["reference_ns"])]
            result["passed"] = result["verified"] and result["ratio"] <= 2.5
        except run.Unmeasurable as error:
            result = {"operation": row["operation"], "size": row["size"],
                      "measurement": "failed", "passed": False, "reason": str(error)}
        report["results"].append(result)
        report["acceptance"] = (len(report["results"]) == len(rows)
                                and all(r["passed"] for r in report["results"]))
        (destination / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        (destination / "samples.log").write_text("\n".join(log) + "\n")
        ratio = f'{result["ratio"]:.3f}x' if "ratio" in result else result["reason"]
        print(f'{len(report["results"])}/{len(rows)} {row["operation"]} '
              f'n={row["size"]}: {ratio}', flush=True)
    return 0 if report["acceptance"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
