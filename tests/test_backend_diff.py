"""Offline checks for backend differential harness outcome classification."""

import sys
import subprocess
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import backend_diff as diff


class BuildOutcomeTests(unittest.TestCase):
    def test_nonzero_build_with_partial_artifact_is_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            def failed_build(cmd, **kwargs):
                Path(cmd[-1]).write_text("partial artifact")
                return subprocess.CompletedProcess(cmd, 1, "", "compiler failed")

            with patch.object(diff, "OUT", Path(tmp)), patch.object(diff.subprocess, "run", failed_build):
                errors = diff.Runner(SimpleNamespace(name="probe", driver="unused.bend"), 1, 1).build()

            self.assertEqual(len(errors), 2)
            self.assertTrue(all("compiler failed" in error for error in errors))
            self.assertTrue(all("exit 1" in error for error in errors))

    def test_successful_build_with_artifact_has_no_errors(self):
        with tempfile.TemporaryDirectory() as tmp:
            def successful_build(cmd, **kwargs):
                Path(cmd[-1]).write_text("complete artifact")
                return subprocess.CompletedProcess(cmd, 0, "", "")

            with patch.object(diff, "OUT", Path(tmp)), patch.object(diff.subprocess, "run", successful_build):
                errors = diff.Runner(SimpleNamespace(name="probe", driver="unused.bend"), 1, 1).build()

            self.assertEqual(errors, [])

    def test_zero_exit_without_artifact_is_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            def missing_artifact(cmd, **kwargs):
                return subprocess.CompletedProcess(cmd, 0, "", "no output")

            with patch.object(diff, "OUT", Path(tmp)), patch.object(diff.subprocess, "run", missing_artifact):
                errors = diff.Runner(SimpleNamespace(name="probe", driver="unused.bend"), 1, 1).build()

            self.assertEqual(len(errors), 2)


class KnownDivergenceTests(unittest.TestCase):
    def run_case(self, results, expect="known:probe"):
        module = diff.Module(
            "probe", "base", "unused.bend",
            lambda *_: [diff.Case(["x"], expect=expect)],
            1, 1, "outcome classification",
        )
        args = SimpleNamespace(
            seed=2026, scale=lambda _: 1, case=None,
            paths=("run", "c", "js"), show=False,
        )

        class Runner:
            oracle = None

            def all(self, argv, paths):
                return {name: (status, output, "", 0.0)
                        for name, (status, output) in results.items()}

        with ThreadPoolExecutor(max_workers=1) as pool:
            return diff.run_module(module, args, pool, Runner(), [])

    def test_known_divergence_timeout_is_an_error(self):
        results = {
            "run": ("timeout", ""),
            "c": ("ok", "result"),
            "js": ("ok", "result"),
        }
        row = self.run_case(results)
        self.assertEqual(row["timeouts"], 1)
        self.assertEqual(len(row["errors"]), 1)
        self.assertEqual(row["known"], {})

        ordinary = self.run_case(results, expect=None)
        self.assertEqual(ordinary["timeouts"], 1)
        self.assertEqual(len(ordinary["errors"]), 1)

    def test_known_divergence_is_still_recorded(self):
        row = self.run_case({
            "run": ("ok", "a"),
            "c": ("ok", "b"),
            "js": ("ok", "a"),
        })
        self.assertEqual(row["known"], {"probe": 1})
        self.assertEqual(row["errors"], [])

    def test_known_divergence_that_disappears_is_only_noted(self):
        row = self.run_case({name: ("ok", "same") for name in ("run", "c", "js")})
        self.assertEqual(row["known"], {})
        self.assertEqual(row["errors"], [])
        self.assertEqual(len(row["notes"]), 1)


if __name__ == "__main__":
    unittest.main()
