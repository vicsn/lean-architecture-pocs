#!/usr/bin/env python3
"""Generate small Lean 4 library-architecture experiments (standard library only).

The source generator is tested in this environment; the Lean programs are not.
Run bench.py --smoke on an installed, pinned Lean toolchain before benchmarking.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

PIN = "leanprover/lean4:v4.33.1"
BASELINE = "import Child\n\ntheorem baseline : True := True.intro\n"
METRICS = """import Lean
import Lean.Util.Heartbeats

open Lean Elab Command

-- Command-elaboration heartbeats, not a replacement for whole-process timing.
elab "#bench " c:command : command => do
  let (_, raw) \u2190 Lean.withHeartbeats (elabCommand c)
  logInfo m!"BENCH_HEARTBEATS_RAW={raw}"
"""

TIME_COMMON = """import Init

namespace Buffer

-- A simple immutable zero-initialized buffer and its structural size.
def zeros : Nat \u2192 List Nat
  | 0 => []
  | Nat.succ n => 0 :: zeros n

def cells : List Nat \u2192 Nat
  | [] => 0
  | _ :: xs => Nat.succ (cells xs)

theorem cells_zeros (n : Nat) : cells (zeros n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

end Buffer
"""
TIME_BAD = """import Common

open Buffer

-- Exposes the implementation-derived size to numerical-capacity clients.
theorem child (n : Nat) : n < cells (zeros (Nat.succ n)) := by
  rw [cells_zeros]
  exact Nat.lt_succ_self n
"""
TIME_GOOD = """import Common

open Buffer

-- Preserve the raw result; add the normalized interface once in the library.
theorem raw_child (n : Nat) : n < cells (zeros (Nat.succ n)) := by
  rw [cells_zeros]
  exact Nat.lt_succ_self n

theorem child (n : Nat) : n < Nat.succ n := by
  simpa only [cells_zeros] using raw_child n
"""

TREE_COMMON = """import Init

-- All leaves of a binary address tree satisfy P.
-- Distinct left/right addresses prevent the branches from being identical.
def TreeOK (P : Nat \u2192 Prop) : Nat \u2192 Nat \u2192 Prop
  | 0, i => P i
  | Nat.succ d, i => TreeOK P d (2 * i) \u2227 TreeOK P d (2 * i + 1)

theorem leaf (P : Nat \u2192 Prop) (i : Nat) : TreeOK P 0 i \u2194 P i := Iff.rfl
"""
TREE_BAD = """import Common

-- Only a one-step expansion interface, not the reusable invariant theorem.
theorem child (P : Nat \u2192 Prop) (d i : Nat) :
    TreeOK P (Nat.succ d) i \u2194
      TreeOK P d (2 * i) \u2227 TreeOK P d (2 * i + 1) := Iff.rfl
"""
TREE_GOOD = """import Common

-- One symbolic induction, available to every consumer.
theorem child (P : Nat \u2192 Prop) (all : \u2200 j, P j) (d i : Nat) :
    TreeOK P d i := by
  induction d generalizing i with
  | zero => exact all i
  | succ d ih => exact And.intro (ih (2 * i)) (ih (2 * i + 1))
"""

INSTANCE_COMMON = """import Init

-- A reversible transformation. Identity is a lawful generic fallback.
class Codec (A : Type) where
  encode : A \u2192 A
  decode : A \u2192 A
  roundtrip : \u2200 x, decode (encode x) = x

-- An optional implementation for one named backend.
class Backend (tag : Nat) (A : Type) where
  codec : Codec A

instance (priority := 100) fallback (A : Type) : Codec A where
  encode := id
  decode := id
  roundtrip _ := rfl
"""
INSTANCE_CHILD_END = """
theorem child {A : Type} [c : Codec A] (x : A) :
    c.decode (c.encode x) = x := c.roundtrip x
"""


def write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def options(n: int) -> str:
    # Scoped to the experiment, not recommendations for production libraries.
    return (
        "set_option maxHeartbeats 0 in\n"
        f"set_option maxRecDepth {max(10000, 8 * (n + 1))} in\n"
    )


def make_pair(root: Path, case: str, size: int, repetitions: int = 16) -> dict:
    if size < 1 or repetitions < 1:
        raise ValueError("size and repetitions must be positive")
    if case not in {"conversion", "tree", "instances", "opacity"}:
        raise ValueError(f"unknown case: {case}")
    metadata: dict = {"case": case, "size": size, "lean_toolchain": PIN,
                      "lean_validation": "NOT_RUN", "variants": {}}
    for variant in ("bad", "good"):
        d = root / variant
        if case == "conversion":
            common = TIME_COMMON
            child = TIME_BAD if variant == "bad" else TIME_GOOD
            declarations = [options(size) +
                f"theorem parent : {size} < Nat.succ {size} := by\n"
                f"  exact child {size}\n"]
        elif case == "tree":
            common = TREE_COMMON
            child = TREE_BAD if variant == "bad" else TREE_GOOD
            proof = (
                "  simp (config := { maxSteps := 100000000 }) only\n"
                "    [child, leaf, all, and_self]\n"
                if variant == "bad" else f"  exact child P all {size} i\n"
            )
            declarations = [options(10000) +
                "theorem parent (P : Nat \u2192 Prop) (all : \u2200 j, P j) (i : Nat) :\n"
                f"    TreeOK P {size} i := by\n" + proof]
            metadata["syntactic_expansion_leaves"] = 2 ** size
            metadata["syntactic_expansion_tree_nodes"] = 2 ** (size + 1) - 1
        elif case == "instances":
            common = INSTANCE_COMMON
            adapters = []
            for k in range(size):
                head = "instance (priority := 2000)" if variant == "bad" else "def"
                adapters.append(
                    f"{head} adapter{k} (A : Type) [b : Backend {k} A] : Codec A :=\n"
                    "  b.codec\n")
            child = "import Common\n\n" + "\n".join(adapters) + INSTANCE_CHILD_END
            declarations = [
                options(10000) + "set_option synthInstance.maxHeartbeats 0 in\n" +
                f"theorem parent{k} (A : Type) (x : A) :\n"
                "    Codec.decode (Codec.encode x) = x := by\n"
                "  exact child x\n" for k in range(repetitions)]
            metadata["parent_declarations"] = repetitions
            metadata["optional_backend_adapters"] = size
        else:
            # Negative control: more work in the child proof, SAME child type.
            common = "import Init\n"
            if variant == "bad":
                child = ("import Common\n\n" + options(10000) +
                         "theorem child (x : Nat) : x = x := by\n  calc\n" +
                         "    x = x := rfl\n" +
                         "    _ = x := rfl\n" * (size - 1))
            else:
                child = "import Common\n\ntheorem child (x : Nat) : x = x := rfl\n"
            declarations = ["theorem parent (x : Nat) : x = x := child x\n"]
        write(d / "lean-toolchain", PIN + "\n")
        write(d / "Common.lean", common)
        write(d / "Child.lean", child)
        write(d / "Parent.lean", "import Child\n\n" + "\n".join(declarations))
        write(d / "Baseline.lean", BASELINE)
        write(d / "Metrics.lean", METRICS)
        write(d / "Probe.lean", "import Child\nimport Metrics\n\n" +
              "\n".join("#bench\n" + x for x in declarations))
        metadata["variants"][variant] = variant
    metadata["identical_parent_source"] = (
        (root / "bad/Parent.lean").read_bytes() == (root / "good/Parent.lean").read_bytes())
    write(root / "case.json", json.dumps(metadata, indent=2) + "\n")
    return metadata


def graph_descendants(graph: dict[str, list[str]], changed: str) -> set[str]:
    reached = {changed}
    while True:
        added = {node for node, deps in graph.items() if any(d in reached for d in deps)}
        new = reached | added
        if new == reached:
            return reached - {changed}
        reached = new


def make_fanout(root: Path, consumers: int = 32) -> dict:
    if consumers < 2:
        raise ValueError("fanout requires at least two consumers")
    result = {"case": "fanout", "consumers": consumers, "variants": {},
              "counts_are": "STATIC_GRAPH_COUNTS_NOT_MEASURED_LAKE_REBUILDS"}
    common_child = "theorem child (n : Nat) : n + 0 = n := rfl\n"
    for variant in ("bad", "good"):
        d = root / variant
        write(d / "lean-toolchain", PIN + "\n")
        write(d / "lakefile.toml", 'name = "fanout"\nversion = "0.1.0"\n'
              'defaultTargets = ["Bench"]\n\n[[lean_lib]]\nname = "Bench"\n')
        graph: dict[str, list[str]] = {}
        if variant == "bad":
            changed = "Bench.Child"
            write(d / "Bench/Child.lean", "import Init\n\n" + common_child +
                  "\n-- A specialized theorem, irrelevant to most consumers.\n"
                  "theorem auxiliary : 0 < 10 := by decide\n")
            graph[changed] = []
        else:
            changed = "Bench.SpecialChild"
            write(d / "Bench/BaseChild.lean", "import Init\n\n" + common_child)
            write(d / "Bench/SpecialChild.lean", "import Bench.BaseChild\n\n"
                  "theorem auxiliary : 0 < 10 := by decide\n")
            graph["Bench.BaseChild"] = []
            graph[changed] = ["Bench.BaseChild"]
        for k in range(consumers):
            imp = ("Bench.Child" if variant == "bad" else
                   "Bench.SpecialChild" if k == 0 else "Bench.BaseChild")
            # Parent0 genuinely needs the specialized capacity certificate.
            # Its existential statement survives changes to that capacity.
            declaration = (
                "theorem parent0 : \u2203 n : Nat, 0 < n := \u27e8_, auxiliary\u27e9\n"
                if k == 0 else
                f"theorem parent{k} (n : Nat) : n + 0 = n := child n\n")
            write(d / f"Bench/Parent{k}.lean", f"import {imp}\n\n" + declaration)
            graph[f"Bench.Parent{k}"] = [imp]
        roots = [f"Bench.Parent{k}" for k in range(consumers)]
        write(d / "Bench.lean", "".join(f"import {name}\n" for name in roots))
        graph["Bench"] = roots
        descendants = graph_descendants(graph, changed)
        parent_descendants = sorted(x for x in descendants if x.startswith("Bench.Parent"))
        item = {"graph": graph, "changed_module": changed,
                "changed_file": changed.replace(".", "/") + ".lean",
                "descendant_parent_modules": parent_descendants,
                "parent_count": len(parent_descendants),
                "all_descendants_including_aggregate": sorted(descendants),
                "descendant_count_including_aggregate": len(descendants)}
        write(d / "graph.json", json.dumps(item, indent=2) + "\n")
        result["variants"][variant] = item
    result["static_parent_fanout_ratio"] = (
        result["variants"]["bad"]["parent_count"] /
        result["variants"]["good"]["parent_count"])
    result["static_descendant_ratio_including_aggregate"] = (
        result["variants"]["bad"]["descendant_count_including_aggregate"] /
        result["variants"]["good"]["descendant_count_including_aggregate"])
    write(root / "case.json", json.dumps(result, indent=2) + "\n")
    return result


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out", type=Path, default=Path(__file__).parent / "examples")
    p.add_argument("--case", choices=["all", "conversion", "tree", "instances", "fanout", "opacity"], default="all")
    p.add_argument("--size", type=int)
    a = p.parse_args()
    defaults = {"conversion": 256, "tree": 4, "instances": 8, "fanout": 32, "opacity": 32}
    for case in defaults if a.case == "all" else [a.case]:
        size = a.size if a.size is not None else defaults[case]
        if case == "fanout":
            make_fanout(a.out / case, size)
        else:
            make_pair(a.out / case, case, size)
    print(f"Generated {a.case} in {a.out}; Lean validation: NOT RUN")


if __name__ == "__main__":
    main()
