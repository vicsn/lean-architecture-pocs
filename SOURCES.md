# Primary sources and how they support this project

Accessed 2026-09-05. The custom examples are original proposed experiments, not
code or benchmark results taken from these publications. Version-specific
measurements in historical papers must not be treated as results for Lean 4.33.1.

## Directly about collaboration and abstraction boundaries

### Johan Commelin and Adam Topaz
**Abstraction boundaries and spec driven development in pure mathematics.**
Bulletin of the American Mathematical Society 61(2), 241-255, April 2024.
Preprint submitted September 2023.

https://arxiv.org/html/2309.14870

Publication metadata:
https://research-portal.uu.nl/en/publications/abstraction-boundaries-and-spec-driven-development-in-pure-mathem/

The closest match to the collaboration question. Sections 3.4 and 4 explain how
an interactive theorem prover makes abstraction boundaries and specifications
usable for collaborative mathematics, with examples from the Liquid Tensor
Experiment. Stable statements separate mathematical components and permit
implementation/refactoring without requiring every collaborator to track the
implementation details. Temporary unproved specifications in the paper are
project-development placeholders, not permission to leave final results
unproved. This suite contains no such placeholders.

### The mathlib Community
**The Lean Mathematical Library.** CPP 2020, pp. 367-381.

https://arxiv.org/html/1910.09336

DOI: https://doi.org/10.1145/3372885.3373824

Explains the integrated library's organization, mathematical structures,
automation, and community development. Useful background for why shared
interfaces matter to distributed contributors. It describes the Lean 3 era;
it is not evidence of current Lean 4 performance ratios.

## Library architecture, maintenance, and measured performance

### Anne Baanen, Matthew Robert Ballard, Johan Commelin, Bryan Gin-ge Chen,
### Michael Rothgang, and Damiano Testa
**Growing Mathlib: maintenance of a large scale mathematical library.**
CICM 2025; preprint August 2025.

https://arxiv.org/html/2508.21593v1

Publisher: https://link.springer.com/chapter/10.1007/978-3-032-07021-0_4

Sections 4 and 7 connect maintainability, import organization, linters, and review
tooling with scaling contributions. Section 5 gives concrete performance
mechanisms. The paper reports a 20% decrease in instance-inference time and 6%
overall compilation speedup from an ordered-hierarchy refactor; a separate
FunLike refactor achieved a 33% instance-synthesis speedup and 19% fewer total
build instructions. These are real reported improvements, not a universal 10x
claim. Its discussion of fast_instance also demonstrates the importance of
normal forms at interfaces.

The paper explicitly cautions that Lean 4's better discrimination-tree indexing
changes advice inherited from Lean 3: merely replacing every `simp` with
`simp only` is not a universal performance or maintenance improvement.

### Anne Baanen
**Use and Abuse of Instance Parameters in the Lean Mathematical Library.**
ITP 2022; expanded Journal of Automated Reasoning article published online
December 2024, volume 69, article 1 (2025).

https://link.springer.com/article/10.1007/s10817-024-09712-7

A technical companion on library structure and instance parameters. The
retrospective discussion is primarily about Lean 3, with comparisons to Lean 4;
consult modern instance-synthesis documentation before reproducing a historical
pathology. Sections on failing searches and hierarchy design motivate the
optional-backend experiment, which deliberately uses distinct goals rather
than relying on repeated diamonds.

## A practical design blog

### Yael Dillies
**Tradeoffs of defining types as subobjects.** Lean community blog,
January 13, 2026.

https://leanprover-community.github.io/blog/posts/tradeoff-of-defining-types-as-subobjects/

Compares subobjects, coerced subobjects, and custom structures. It discusses dot
notation, meaningful projection names, and the tradeoff between automatically
inherited instances and one-time transfer work. Useful concrete API-design
reading, but not a controlled 10x benchmark or a study measuring collaboration.

## Compiler semantics and measurement references

**Lean language reference: Theorems.**
https://lean-lang.org/doc/reference/latest/Definitions/Theorems/

Theorem declarations and their default irreducibility explain why a larger
child tactic proof does not automatically get replayed by a parent applying its
constant. This motivates the negative control.

**Lean language reference: Instance Synthesis.**
https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/

Describes priority ordering, implicit-argument synthesis, and tabled resolution
that avoids repeated-goal diamond explosion and nontermination on cycles.
It also documents `trace.Meta.synthInstance` for diagnosis. The backend example
uses different numeric tags so its failing subgoals are distinct.

**Lean.Util.Heartbeats API documentation.**
https://lean-lang.org/doc/api/Lean/Util/Heartbeats.html

Documents `Lean.withHeartbeats` and the factor of 1000 between its raw counts and
user-facing maxHeartbeats units. A heartbeat count is not a measurement of peak
live process memory.

**Lean simplifier reference and community guide.**
https://lean-lang.org/doc/reference/latest/The-Simplifier/Configuring-Simplification/
https://leanprover-community.github.io/extras/simp.html

Configuration, memoization, and `simp (config := ...) only [...]` syntax.
These references inform the tree experiment; they do not establish its ratios.

**Lean language reference: Lake.**
https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/

Build configuration and incremental build infrastructure. This suite records
actual output rewrites separately from source-level import-graph descendants.
The distinction is important as build-system and module-interface behavior
evolves.

**Pinned Lean release: v4.33.1.**
https://github.com/leanprover/lean4/releases/tag/v4.33.1

Released August 21, 2026. The numerical source suite pins this release rather
than claiming compatibility with every compiler version. The online `latest`
reference may describe a later release candidate; compilation on the pinned
version remains a required validation step.
