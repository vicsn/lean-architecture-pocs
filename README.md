# Lean library architecture: downstream-cost experiments

Four positive experiments, one negative control, and a measurement harness.
Generated on 2026-09-05. Intended toolchain: **Lean 4.33.1**.

## Validation status: read this first

Lean 4.33.1 **was compiled and measured** on 2026-09-06 on an Apple M2 Max
(12 logical CPUs, 32 GiB RAM, macOS 26.6.2, `gtime` 1.10). Full evidence is in
`results.json`, `smoke-results.json`,
and `VALIDATION_STATUS.json`. The older `ENVIRONMENT_CHECK.json` is the
authoring-container failure (no Lean on PATH) and is superseded by this run.

Python tests: **13/13 passed** (`PYTHON_TESTS.txt`). Smoke (`--smoke --repeats 1`)
compiled all five cases, ran parent axiom audits, and measured a **32x** Lake
parent-`.olean` rewrite ratio. The shipped `examples/` sources also compile
(with `LEAN_PATH` set to the variant directory; Lake builds succeed for both
fanout layouts). Good `instances` still emit the expected class-definition
reducibility warnings.

Default full sweep (`--repeats 5 --require-targets`, 180 s timeout, 4096 MiB
Lean budget) status: **COMPLETE_WITH_FAILURES** (process exit 2). Three of four
positive cases met their defined 10x target. Tree met the serialized-bytes
target from depth 6, but **did not** reach 10x peak RSS before depth 18 was
censored at the memory budget.

| Case | Size that first met the primary 10x target | Primary ratio (median bad / median good) | Notes |
|---|---|---|---|
| `conversion` | N=65536 cells | wall **17.81x** (6.057 s / 0.340 s) | Heartbeats 8811x; RSS only 2.37x; parent `.olean` size identical |
| `tree` | (bytes from D=6; RSS never) | D=16 bytes **14204x**; RSS **4.21x** | D=16 wall 75.0x (25.809 s / 0.344 s). D=18 bad parent exit 1 at ~4096 MiB |
| `instances` | K=256 adapters | heartbeats **29.94x** | Wall only 1.35x. Sweep stopped here; K=1024/4096 not run |
| `fanout` | 32 parents | rewritten parent `.olean` count **32x** (32 vs 1) | Dirty-build wall 3.06x (3.319 s / 1.084 s), not the 10x test |
| `opacity` | N=128 (negative control) | heartbeats **1.00x**; wall 0.97x | Parent cost does not track the long child proof |

One ratio is also static: the generated import graphs have **32 versus 1
downstream parent modules** after a specialized child theorem is changed
(**32x**). On this machine the Lake dirty-build rewrite count matched that graph.

## What this investigates

A child is a separately compiled theorem-providing module. A parent imports it
and proves a client theorem. For the time and instance cases, both parents are
byte-for-byte identical. For the tree case their statements and hypotheses are
identical, but the proof line uses the different child interfaces. For the
fanout case only import placement differs.

The hypothesis is NOT that a long child proof automatically gets replayed by
its users. Theorem proof bodies are normally opaque to downstream elaboration.
The interesting costs cross other boundaries: implementation-heavy theorem
types, absence of reusable compositional lemmas, globally registered automation,
and import dependencies. The opacity control tests this distinction. See
[SOURCES.md](SOURCES.md) for primary references.

## Quick start

Requirements: Python 3.10+, GNU time, and Lean/Lake installed through elan or
an equivalent toolchain installation. On Linux use `/usr/bin/time`. On macOS
install Homebrew `gnu-time` (`gtime`); BSD `/usr/bin/time` is not sufficient.
Set `GNU_TIME` if the binary is not on `PATH`. No Mathlib or third-party Python
dependencies are required. Execute from the repository root.

```sh
elan toolchain install leanprover/lean4:v4.33.1
lean --version
python3 -m unittest test_harness -v
python3 bench.py --smoke --repeats 1 --out smoke-results.json
```

The smoke check compiles small instances of all five cases, runs the instrumented
probes and parent-axiom audits for numerical cases, and exercises actual Lake
rebuilds for the fanout case. If it fails, inspect the recorded stdout/stderr and
resolve the compiler or source problem before making any performance claim.

Then run a full sweep:

```sh
python3 bench.py --repeats 5 --require-targets --out results.json
```

This command exits nonzero unless all four positive cases achieve their defined
measured threshold and there are no compilation/resource failures. A successful
process exit without `--require-targets` does NOT imply a 10x result.

Each subprocess has a default 180-second timeout. Numerical Lean invocations use
a 4096 MiB Lean memory budget, a 131072 KiB thread-stack setting, one worker, and
synchronous declaration elaboration. These are stress-test settings, not
production-library recommendations; Lean's internal memory budget is not an OS
container memory guarantee. Lake fanout builds use Lake's default scheduler and
the subprocess timeout, not those numerical-case Lean flags.

The largest tree cases can be expensive. The sweep stops increasing a case after
a failure or after all its targets pass, unless `--keep-sweeping` is specified.
A timeout/OOM is recorded as a censored failure, never as an infinite speedup.

## Experiment map

| Case | Bad library boundary | Good library boundary | Primary measured target |
|---|---|---|---|
| `conversion` | Buffer capacity is exposed as a recursive size computation | Export a normalized capacity theorem | Parent whole-process wall time >=10x |
| `tree` | Only one-step unfolding is supplied for a recursive invariant | Export the invariant proved by symbolic induction | BOTH parent peak RSS and serialized parent bytes >=10x |
| `instances` | Optional codec adapters are all high-priority global instances | Adapters remain available as explicit definitions | Parent-command raw heartbeats >=10x |
| `fanout` | Stable and specialized child theorems share one widely imported module | Split the minimal base from the specialized module | Rewritten parent `.olean` count >=10x; static graph ratio is 32x |
| `opacity` | A needlessly long proof of the same child proposition | A short proof of exactly the same proposition | Negative control: no 10x target |

Wall time, process CPU time, peak RSS, serialized output bytes, and command
heartbeats are recorded for every numerical case. A case can exhibit additional
regressions beyond its primary metric. These are separate measurements, not
interchangeable definitions of cost.

## 1. Conversion: leaking structural computation through a theorem's type

Shared definitions represent a zero-initialized immutable buffer:

```lean
def zeros : Nat -> List Nat
  | 0 => []
  | Nat.succ n => 0 :: zeros n

def cells : List Nat -> Nat
  | [] => 0
  | _ :: xs => Nat.succ (cells xs)
```

`Common.lean` proves `cells_zeros (n) : cells (zeros n) = n` by induction.

The bad child exports:

```lean
theorem child (n : Nat) : n < cells (zeros (Nat.succ n)) := by
  rw [cells_zeros]
  exact Nat.lt_succ_self n
```

The good child preserves that result as `raw_child` and adds:

```lean
theorem child (n : Nat) : n < Nat.succ n := by
  simpa only [cells_zeros] using raw_child n
```

Both parents are identical, with a generated numeral replacing `N`:

```lean
theorem parent : N < Nat.succ N := by
  exact child N
```

For the bad interface, reconciling the supplied and expected types requires
normalizing the structural buffer-size computation. The good interface agrees
with the target without that traversal. The raw child proof is short in BOTH
versions; the difference is which statement is exported to numerical clients.

There are N+1 buffer cells in the relevant computation. This is a structural
work argument, not a prediction that elapsed time is exactly linear or that any
particular N necessarily gives 10x on a specific compiler. The whole-process
startup/import baseline also matters. The good parent still pays ordinary
elaboration costs, including reading its numeric literal.

The bad interface is not universally wrong: a caller working directly with the
raw buffer length may naturally need it. The architectural improvement is to
provide the normalized view as well, rather than making every numerical client
rediscover or reduce it.

Default sweep: 256, 1024, 4096, 16384, 65536 cells.

```sh
python3 bench.py --case conversion --repeats 5 --require-targets
```

## 2. Memory and proof artifacts: one-step expansion versus compositional proof

`TreeOK P d i` says every leaf of a depth-d binary address tree satisfies P.
Its equations are:

```lean
def TreeOK (P : Nat -> Prop) : Nat -> Nat -> Prop
  | 0, i => P i
  | Nat.succ d, i => TreeOK P d (2*i) /\ TreeOK P d (2*i+1)
```

The bad child supplies only the one-level equivalence. The parent simplifies
that equivalence repeatedly, using `all : forall j, P j` at every leaf.

The good child proves `TreeOK P d i` once for arbitrary d and i from `all`, by
induction on d. Its two recursive calls discharge the left and right branches.
Every parent can apply that theorem without expanding its proof.

The two parent statements are exactly the same:

```lean
theorem parent (P : Nat -> Prop) (all : forall j, P j) (i : Nat) :
    TreeOK P D i := by
  -- Bad: simp ... only [child, leaf, all, and_self]
  -- Good: exact child P all D i
```

This models a common choice in tree/trie verification and recursive safety
invariants: expose constructors and leave all consumers to enumerate branches,
or expose a theorem that composes certificates.

At depth 16, fully expanding the recurrence produces 65536 leaves and 131071 tree
nodes. These are **syntactic expansion counts**, not allocated bytes, peak RSS,
or necessarily serialized proof nodes. Distinct symbolic addresses prevent the
trivial identical-branch memoization that would undermine a naive duplicated-P
example. Compiler sharing and proof serialization can still alter the measured
cost, which is why the harness measures rather than infers these metrics.

The target is >=10x for BOTH total peak RSS and serialized parent outputs. The
latter includes every generated `Parent.olean*` piece and any `Parent.ir` or
`Parent.ilean`, not just the main file. It excludes child artifacts. A large
artifact is a persistence/load cost; it is not itself a memory measurement.

Default depths: 6, 8, 10, 12, 14, 16, 18, 20. Source examples ship at depth 4 for
readability. Failed large depths are censored, not counted as successes.

```sh
python3 bench.py --case tree --repeats 5 --require-targets
```

## 3. Hidden elaboration work: optional backends made global

A `Codec A` has encode/decode operations and a round-trip theorem. A lawful
identity codec is the low-priority generic fallback. `Backend tag A` describes
an optional implementation.

The bad child registers K adapters of this form globally:

```lean
instance (priority := 2000) adapter17 (A : Type)
    [b : Backend 17 A] : Codec A := b.codec
```

The good child offers the same adapter without global registration:

```lean
def adapter17 (A : Type) [b : Backend 17 A] : Codec A := b.codec
```

Both export exactly the same round-trip theorem `child`. Both parents say:

```lean
theorem parent0 (A : Type) (x : A) :
    Codec.decode (Codec.encode x) = x := by
  exact child x
```

There are no Backend instances in this client. In the bad environment,
instance search considers the high-priority adapters and their unsatisfied,
distinct Backend goals before using the fallback. The good environment leaves
that unrelated work out of implicit search. The generated parent has 16
independent declarations in both variants, reducing startup dominance while
retaining identical client work.

This is not the obsolete assertion that ordinary instance diamonds necessarily
produce exponential search in Lean 4. Lean 4 tables repeated goals. Here the
candidate goals differ in their tags, so they remain distinct tasks. Expected
extra search grows with the number of candidates; the measured target is
command-elaboration heartbeats, not an asserted wall-time ratio.

K is a stress parameter, not a claim that a typical project contains thousands
of codecs. The corresponding real concern is broad optional inheritance,
coercion, or backend adapters affecting every importing client. Explicit values
or opt-in/scoped instance modules are the architectural alternatives.

Current Lean may emit a class-definition-reducibility warning for the good
plain definitions; they intentionally are not registered global instances.
Warnings are retained in logs. A warning alone is not treated as a compile error.

Default K: 16, 64, 256, 1024, 4096.

```sh
python3 bench.py --case instances --repeats 5 --require-targets
```

## 4. Collaboration and incremental builds: unrelated theorems share a module

There are 32 independently compiled parent modules and an aggregate `Bench`.
Thirty-one parents use a stable `child (n) : n + 0 = n`. The remaining parent uses a
specialized theorem `auxiliary : 0 < 10` as an existential witness.

In the bad layout, both child theorems live in `Bench.Child`, imported by all 32
parents. In the good layout, stable results live in `Bench.BaseChild`; the
specialized theorem lives in `Bench.SpecialChild`, imported only by Parent0.
The other 31 parents import just BaseChild.

The experiment changes the actual specialized theorem statement from `0 < 10`
to `0 < 11`, then to `0 < 12`, and so on. This is not a timestamp-only edit.
Parent0's existential proposition remains unchanged and uses the new witness
without a source edit.

The changed module has 32 versus 1 parent descendants, exactly a 32x ratio.
Including the aggregate root gives 33 versus 2, or 16.5x. Both counts are
calculated from the generated source import graph and unit-tested.

The optional measured experiment runs real Lake clean, no-op, and dirty builds.
It verifies that a no-op build does not rewrite `.olean` files, then counts
parent `.olean` modification-time changes after each theorem-statement edit.
This observable artifact-rewrite count is not silently equated with all compiler
jobs. Build-system fingerprinting, cache reuse, or unchanged output suppression
can change the measured count. Full Lake logs are retained for inspection.

This case directly models team interference: contributors working on the
specialized theorem should not pull unrelated contributors through its import
boundary. Graph fanout quantifies exposure, not a guaranteed 32x wall-time
slowdown and not a guarantee about modern interface-based invalidation.

```sh
python3 bench.py --case fanout --consumers 32 --repeats 3 --require-targets
```

## Negative control: opacity is already an abstraction boundary

Both child declarations have exactly the type `(x : Nat) -> x = x`. One uses a
long reflexive calculation chain; the other is `rfl`. The identical parent is
`theorem parent (x : Nat) : x = x := child x`.

Do not expect the parent's elaboration cost to scale with the child's tactic
script simply because the script is long. Child compilation is excluded from
parent measurements. Import loading/artifact size can still differ, so this is
not a promise that whole-process memory or time is perfectly equal.

```sh
python3 bench.py --case opacity --repeats 5
```

## Measurement contract and interpretation

Children are compiled separately before parent timing. The harness records their
prebuild times, but never adds them to the parent's time. Both variants use the
same toolchain and numerical-case flags. Imports are warmed before repeated
measurements; this is a warm-cache benchmark. Variant order alternates.

The reported ratio for a metric M is:

    median(M_bad_successful_runs) / median(M_good_successful_runs)

All required builds must succeed. Failed or timed-out runs are not dropped to
improve a median. A zero/absent denominator produces no ratio, not infinity.
Raw runs, source hashes, toolchain, host, options, output paths, and audit logs
are preserved. Medians are descriptive, not statistical confidence intervals.

`Baseline.lean` imports the same Child and proves True. Its time and RSS are
reported separately. Baseline-subtracted wall time is diagnostic only; the 10x
test uses total time. Peak RSS is NEVER calculated by subtracting two process
peaks, because those peaks need not occur at comparable stages.

Heartbeats are measured in a separate Probe module using
`Lean.withHeartbeats (elabCommand c)`, with asynchronous elaboration disabled.
The instrumentation imports are not added to primary wall-time/RSS runs.
The result is the **raw internal heartbeat count**, whose scale differs by
1000 from user-facing `maxHeartbeats` units. Heartbeats are not peak live memory
and the probe is not an isolated measurement of every possible kernel activity.

Separate `#print axioms` checks reject parent dependencies on `sorryAx` or
`Lean.ofReduceBool`. No generated Lean source uses `sorry`, `axiom`, `unsafe`,
or `native_decide`. This audit is run by the harness after real compilation. On the 2026-09-06
run it passed for every successfully measured numerical size (no `sorryAx` or
`Lean.ofReduceBool`). Tree depth 18 never reached the audit because compilation
failed.

Use a new `--work` and `--out` per hardware/toolchain run to preserve comparisons:

```sh
python3 bench.py --case tree --sizes 8,10,12,14,16,18 \
  --repeats 5 --memory-mib 4096 --timeout 180 \
  --work work-machine-a --out machine-a-tree.json --require-targets
```

A meaningful result states the Lean version, hardware, parameter, both raw
medians, their ratio, baseline values, and all failures. The default threshold
is 10; changing `--threshold` changes what the harness accepts. A failed threshold
means this run did not establish the requested factor. Increase sizes only
within a controlled resource budget, and do not hide failures.

## Files

`generate.py` creates the examples and parameter sweeps. `bench.py` compiles and
measures them. `test_harness.py` tests Python behavior. `examples/` contains small
inspectable child/common/parent source files plus dependency graphs.
`PYTHON_TESTS.txt` contains the actual Python test output.
`VALIDATION_STATUS.json` is the 2026-09-06 Lean run. `ENVIRONMENT_CHECK.json` is
the earlier authoring-container failure. `SOURCES.md` is the cited reading list.

A generated `case.json` initially says `NOT_RUN`. A successful numerical run
updates it to `COMPILED_AND_PARENT_AXIOM_AUDITED`; a failed attempt updates it to
`ATTEMPTED_NOT_VALIDATED`. Per-case `measurement.json` under `--work` and the
chosen top-level results JSON contain the empirical data. The inspectable
`examples/*/case.json` files remain the small shipped sources (`NOT_RUN`);
measured copies live under `work-macos-m2max/`.

## Architectural takeaway

A useful collaborator-facing theorem contract has more than a proposition: it
also has an expected elaboration cost, a deliberately chosen automation
footprint, and an appropriately narrow import boundary. Provide reusable
semantic lemmas, normalized interface views, opt-in optional machinery, and
small stable foundational modules. Those choices let contributors work against
stable specifications instead of depending on one another's implementation
and performance accidents. These experiments illustrate that design argument;
they are not measurements of collaboration productivity or a universal 10x law.
