# Lean library architecture

This repo contains four small Lean libraries. Each library has a parent and two
children — one bad and one good. These examples showcase how bad architecture
can have significant negative effects on parent libraries. The results shared
in this repo were tested on Lean 4.33.1.

There is also a control, `opacity`: the child proof is long, but the exported
type is the same. Parent cost should not move.

Proof bodies are already opaque to importers. The costs here leak through the
exported type, the instance table, or the import graph. Background reading is
in [SOURCES.md](SOURCES.md).

## Results

Apple M2 Max, 12 CPUs, 32 GiB, macOS 26.6.2, five repeats, 180 s timeout, 4096
MiB Lean budget. Raw runs are in `results.json`.

| Case | What 10× means here | What happened |
|---|---|---|
| `conversion` | parent wall time | **17.81×** at N=65536 (6.057 s / 0.340 s). Heartbeats 8811×. RSS only 2.37×. |
| `tree` | peak RSS *and* parent `.olean` bytes | Bytes **14204×** by depth 16. RSS only **4.21×**. Wall 75×. Depth 18 died at the 4 GiB budget. |
| `instances` | elaboration heartbeats | **29.94×** at K=256. Wall only 1.35×. Larger K not run. |
| `fanout` | rewritten parent `.olean` files after a specialized edit | **32×** (32 vs 1). Dirty-build wall 3.06×. |
| `opacity` | control, no 10× target | Heartbeats 1.00×, wall 0.97×. |

`--require-targets` exits 2 because tree needs both RSS and bytes. Bytes pass;
RSS does not before the memory cap.

## How to run

Python 3.10+, Lean/Lake via elan, and GNU time. On Linux that is
`/usr/bin/time`. On macOS install Homebrew `gnu-time` (`gtime`); BSD time will
not work. Set `GNU_TIME` if needed. No Mathlib.

From the repo root:

```sh
elan toolchain install leanprover/lean4:v4.33.1
lean --version
python3 -m unittest test_harness -v
python3 bench.py --smoke --repeats 1 --out smoke-results.json
python3 bench.py --repeats 5 --require-targets --out results.json
```

Smoke compiles a small instance of each case, audits parent axioms, and does a
real Lake rebuild for fanout. The full sweep grows each case until it hits 10×
or fails. Timeouts and OOM are failures, not infinite speedups. Without
`--require-targets`, a zero exit only means the jobs ran; it does not mean 10×.

Each Lean invocation is single-threaded, 4096 MiB, 128 MiB stack, async
elaboration off. Those are stress settings. Lake fanout uses Lake's normal
scheduler.

## The four libraries (and the control)

| Case | Bad child | Good child | Target |
|---|---|---|---|
| `conversion` | capacity is a recursive size computation | a normalized `n < n+1` theorem | wall time |
| `tree` | one-step unfolding of a recursive invariant | the invariant, proved by induction | peak RSS and parent artifact bytes |
| `instances` | optional backends as high-priority global instances | the same adapters as plain definitions | heartbeats |
| `fanout` | stable and specialized theorems in one widely imported module | split the specialized theorem out | rewritten parent `.olean` count |
| `opacity` | a long proof of `x = x` | `rfl` | control |

For conversion, instances, and opacity the two parents are byte-for-byte the
same. For tree the statement matches and only the proof line differs. For
fanout only import placement differs.

The harness records wall time, CPU, peak RSS, serialized parent bytes, and
heartbeats for every numerical case. Only the column above is the 10× test.

### 1. Conversion

A zero-initialized buffer, and a recursive length:

```lean
def zeros : Nat -> List Nat
  | 0 => []
  | Nat.succ n => 0 :: zeros n

def cells : List Nat -> Nat
  | [] => 0
  | _ :: xs => Nat.succ (cells xs)
```

`Common.lean` proves `cells (zeros n) = n`. The bad child still talks about
the buffer:

```lean
theorem child (n : Nat) : n < cells (zeros (Nat.succ n)) := by
  rw [cells_zeros]
  exact Nat.lt_succ_self n
```

The good child keeps that as `raw_child` and exports the reduced fact:

```lean
theorem child (n : Nat) : n < Nat.succ n := by
  simpa only [cells_zeros] using raw_child n
```

Both parents are `exact child N`. The bad interface makes the parent reconstruct
`cells (zeros (N+1))` before it can see `N < N+1`. The proofs in both children
are short; what changes is the statement clients see.

A caller that really wants the buffer length can keep `raw_child`. The issue is
making every numerical client reduce it themselves.

Sweep: 256, 1024, 4096, 16384, 65536 cells.

```sh
python3 bench.py --case conversion --repeats 5 --require-targets
```

### 2. Trees

`TreeOK P d i` holds if every leaf of a depth-`d` binary tree of addresses
satisfies `P`:

```lean
def TreeOK (P : Nat -> Prop) : Nat -> Nat -> Prop
  | 0, i => P i
  | Nat.succ d, i => TreeOK P d (2*i) /\ TreeOK P d (2*i+1)
```

The bad child only gives the one-level unfolding. The parent `simp`s it down
to the leaves, using `all : forall j, P j` at each one. The good child proves
`TreeOK P d i` once by induction on `d`. Same parent statement:

```lean
theorem parent (P : Nat -> Prop) (all : forall j, P j) (i : Nat) :
    TreeOK P D i := by
  -- Bad: simp ... only [child, leaf, all, and_self]
  -- Good: exact child P all D i
```

That is the usual constructor-vs-lemma choice for a recursive invariant.
Depth 16 is 65536 leaves / 131071 nodes if you fully expand; those are
syntactic counts, which is why RSS and `.olean` size are measured rather than
inferred. Addresses are distinct, so the compiler cannot collapse the two
branches as identical.

The 10× test is peak RSS *and* all `Parent.olean*` / `Parent.ir` / `Parent.ilean`
bytes (not the child's). A fat artifact is a load cost, not a memory number.

Sweep: depths 6–20. The shipped sources use depth 4. Depth 18 on this machine
hit the 4096 MiB Lean budget and was dropped.

```sh
python3 bench.py --case tree --repeats 5 --require-targets
```

### 3. Global instances

`Codec A` has encode, decode, and a round-trip theorem. A lawful identity
codec is the low-priority fallback. `Backend tag A` is an optional
implementation. The bad child registers K adapters globally:

```lean
instance (priority := 2000) adapter17 (A : Type)
    [b : Backend 17 A] : Codec A := b.codec
```

The good child keeps the same function as a definition. The parent never
has a `Backend` instance:

```lean
theorem parent0 (A : Type) (x : A) :
    Codec.decode (Codec.encode x) = x := by
  exact child x
```

In the bad library, instance search still walks those high-priority adapters
and their unsatisfied `Backend` goals before falling back. The tags differ, so
Lean 4 cannot table them as the same goal. The parent has 16 copies of this
declaration so startup does not dominate.

K is a stress knob, not a claim that a real project has thousands of codecs.
The real analogue is optional inheritance, coercions, or backends that hitch
a ride on every import. Prefer explicit values or a scoped instance module.

The good definitions may warn about class reducibility. That is expected;
warnings are not treated as compile errors.

Sweep: K = 16, 64, 256, 1024, 4096.

```sh
python3 bench.py --case instances --repeats 5 --require-targets
```

### 4. Import fanout

32 parent modules plus an aggregate `Bench`. 31 parents use a stable
`child (n) : n + 0 = n`. Parent0 uses a specialized `auxiliary : 0 < 10` as
an existential witness.

Bad layout: both theorems live in `Bench.Child`, imported by everyone. Good
layout: `Bench.BaseChild` for the stable fact; `Bench.SpecialChild` only for
Parent0.

The run then *changes the theorem* from `0 < 10` to `0 < 11`, `0 < 12`, …
Parent0's statement stays the same and picks up the new witness. That is 32
parent dependents vs 1 (33 vs 2 if you count `Bench`).

Lake clean / no-op / dirty builds check that a no-op does not rewrite
`.olean`s, then count which parent `.olean`s change after the edit. Fingerprints
and output suppression can change that count; the logs are kept. Graph fanout
is exposure, not a 32× wall-time slowdown.

```sh
python3 bench.py --case fanout --consumers 32 --repeats 3 --require-targets
```

### 5. Opacity

Both children have type `(x : Nat) -> x = x`. One is a long `rfl` chain; the
other is `rfl`. The parent is `theorem parent (x : Nat) : x = x := child x`.
Child compile time is not included in the parent numbers. A long tactic script
does not get replayed just because it is long.

```sh
python3 bench.py --case opacity --repeats 5
```

## How the numbers are computed

Children are compiled first; their time is recorded and then ignored. Parents
are timed on a warm cache. Variant order alternates. The ratio is

    median(successful bad runs) / median(successful good runs)

Failed runs stay in the log. A zero good median is “no ratio”, not infinity.
`Baseline.lean` imports Child and proves `True`; that time is reported
separately and is not subtracted from the 10× wall test. Peak RSS is never
two peaks subtracted from each other.

Heartbeats come from a separate `Probe` via `Lean.withHeartbeats (elabCommand c)`,
with async elaboration off. That is Lean's raw internal count (÷1000 for
`maxHeartbeats` units). It is not RSS, and the probe is not in the wall/RSS
runs.

After a successful compile, `#print axioms` must not mention `sorryAx` or
`Lean.ofReduceBool`. Generated sources do not use `sorry`, `axiom`, `unsafe`,
or `native_decide`. That check passed for every size that compiled on
2026-09-06; tree depth 18 never got there.

Use a fresh `--work` and `--out` per machine:

```sh
python3 bench.py --case tree --sizes 8,10,12,14,16,18 \
  --repeats 5 --memory-mib 4096 --timeout 180 \
  --work work-machine-a --out machine-a-tree.json --require-targets
```

Report Lean version, hardware, the parameter, both medians, the ratio,
baseline, and failures. Changing `--threshold` only changes what this harness
accepts.

`generate.py` writes the sources. `bench.py` measures them. `examples/` has
small readable copies. `results.json` is the sweep on this machine.

## Takeaway

Export the lemma clients will actually apply, keep optional instances off the
global table, and do not put a specialized theorem in a module everyone
imports. The 10× figures are for these examples on this compiler; the design
point is the boundary, not the factor.
