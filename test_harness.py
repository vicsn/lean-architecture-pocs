"""Tests of the generator and measurement plumbing, NOT Lean compilation."""
from pathlib import Path
import json
import re
import sys
import tempfile
import unittest

from generate import make_pair, make_fanout, graph_descendants
from bench import artifact_size, median_measurements, ratio, run_process


class GeneratorTests(unittest.TestCase):
    def test_equal_parent_source_where_claimed(self):
        with tempfile.TemporaryDirectory() as temp:
            for case in ("conversion", "instances", "opacity"):
                root = Path(temp) / case
                meta = make_pair(root, case, 4, 3)
                self.assertTrue(meta["identical_parent_source"])
                for variant in ("bad", "good"):
                    for path in (root / variant).glob("*.lean"):
                        self.assertNotRegex(path.read_text(), r"\b(sorry|axiom|unsafe|native_decide)\b")

    def test_tree_same_statement_different_interface(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            meta = make_pair(root, "tree", 4)
            bad = (root / "bad/Parent.lean").read_text().split(":= by")[0]
            good = (root / "good/Parent.lean").read_text().split(":= by")[0]
            self.assertEqual(bad, good)
            self.assertFalse(meta["identical_parent_source"])
            self.assertEqual(meta["syntactic_expansion_leaves"], 16)
            self.assertEqual(meta["syntactic_expansion_tree_nodes"], 31)
            self.assertIn("simp (config :=", (root / "bad/Parent.lean").read_text())

    def test_actual_optional_instance_difference(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            make_pair(root, "instances", 12, 2)
            bad = (root / "bad/Child.lean").read_text()
            good = (root / "good/Child.lean").read_text()
            self.assertEqual(bad.count("instance (priority := 2000)"), 12)
            self.assertEqual(good.count("def adapter"), 12)
            self.assertNotIn("instance (priority := 2000)", good)

    def test_fanout_counts_and_real_specialized_consumer(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            result = make_fanout(root, 32)
            self.assertEqual(result["static_parent_fanout_ratio"], 32)
            self.assertEqual(result["static_descendant_ratio_including_aggregate"], 16.5)
            for variant in ("bad", "good"):
                self.assertIn("auxiliary", (root / variant / "Bench/Parent0.lean").read_text())
            self.assertEqual(result["variants"]["good"]["parent_count"], 1)

    def test_changed_theorem_substitution(self):
        original = "theorem auxiliary : 0 < 10 := by decide\n"
        changed = re.sub(r"theorem auxiliary : 0 < \d+ := by decide",
                         "theorem auxiliary : 0 < 11 := by decide", original)
        self.assertIn("0 < 11", changed)
        self.assertNotEqual(original, changed)

    def test_graph_algorithm(self):
        self.assertEqual(graph_descendants({"a": [], "b": ["a"], "c": ["b"], "d": []}, "a"), {"b", "c"})

    def test_invalid_sizes(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaises(ValueError):
                make_pair(Path(temp), "tree", 0)


class PlumbingTests(unittest.TestCase):
    def test_process_success_and_rss(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            r = run_process([sys.executable, "-c", "print('ok')"], root, root / "success", 2)
            self.assertEqual(r["status"], "OK")
            self.assertEqual(r["exit_code"], 0)
            self.assertGreater(r["peak_rss_kib"], 0)
            self.assertGreater(r["wall_s"], 0)
            self.assertEqual(Path(r["stdout"]).read_text().strip(), "ok")

    def test_process_failure_is_not_success(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            r = run_process([sys.executable, "-c", "raise SystemExit(3)"], root, root / "failure", 2)
            self.assertEqual(r["status"], "FAILED")
            self.assertEqual(r["exit_code"], 3)

    def test_timeout_is_censored(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            r = run_process([sys.executable, "-c", "import time; time.sleep(3)"], root, root / "timeout", 0.05)
            self.assertEqual(r["status"], "TIMEOUT")
            self.assertNotEqual(r["exit_code"], 0)
            self.assertLess(r["wall_s"], 1)

    def test_artifact_size_includes_split_oleans(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for name, n in {"Parent.lean": 50, "Parent.olean": 10, "Parent.olean.private": 20,
                            "Parent.olean.server": 30, "Parent.ir": 40, "Parent.log": 500}.items():
                (root / name).write_bytes(b"x" * n)
            self.assertEqual(artifact_size(root, "Parent"), 100)

    def test_no_medians_of_failed_runs(self):
        with self.assertRaises(ValueError):
            median_measurements([{"status": "FAILED", "wall_s": 0.1}])
        self.assertEqual(median_measurements([{"status": "OK", "wall_s": 2},
                                               {"status": "OK", "wall_s": 4}])["wall_s"], 3)

    def test_zero_denominator_is_not_infinity(self):
        self.assertIsNone(ratio(100, 0))
        self.assertIsNone(ratio(None, 3))
        self.assertEqual(ratio(100, 10), 10)


if __name__ == "__main__":
    unittest.main(verbosity=2)
