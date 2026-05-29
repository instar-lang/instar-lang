# Artifact for "Let It Be Optimized"

## 1. Paper Summary

This artifact accompanies the ICFP '26 pearl *"Let It Be Optimized"*.
The paper reconstructs optimizing staged evaluation as found in
library-based multi-stage programming (MSP) systems (e.g., LMS, BuildIt) as a
proper calculus with executable semantic artifacts.

All semantic artifacts are implemented in Scala 3 as executable code, serving as
a reference implementation for the paper's figures and claims. The artifact is
organized as two complementary parts:

1. **A family of definitional evaluators** (`src/main/scala/experiment/`) that
   trace the derivation of the calculus, from a stateful evaluator to a CPS
   interpreter, a direct-style interpreter using delimited control, and finally
   an abstract machine (§2–§4).
2. **A single optimizing staged evaluator** (`src/main/scala/Interp.scala`) that
   realizes each optimization from the paper (§5–§12) as a modular `reflect`
   combinator, toggled independently at run time.

Every claim in the paper is backed by an executable test. The artifact is
self-contained: the only external dependency is the
[MUnit](https://scalameta.org/munit/) test framework, fetched automatically by
the build tool.

### Claims supported by this artifact

- The definitional evaluators in §2–§4 are equivalent: each produces the same
  staged object code for the same input (see `src/test/scala/experiment/`).
- Each optimization of §5–§12 (constant propagation, CSE, constant folding,
  dead-code elimination, partially-static data, inlining with renormalization,
  and λ-hoisting) is implemented as an independent, composable pass, and the
  examples shown in the paper reduce to the stated object code (see
  `src/test/scala/Interp.scala`).

## 2. Environment

- **JDK**: 17 or later
- **Scala**: 3.8.0 (managed by sbt)
- **Build tool**: sbt 1.11+

## 3. Code Structure

```
├── build.sbt
├── src/main/scala/
│   ├── Syntax.scala          # Core two-stage language AST (§2, Figure 2)
│   ├── Interp.scala          # Optimizing staged evaluator (§5–§12)
│   ├── Algebra.scala         # Partially-static data algebra (§9)
│   ├── BiMap.scala           # Bidirectional map (code cache, §5.2)
│   ├── Counter.scala         # Fresh variable name generator
│   └── experiment/
│       ├── Syntax.scala      # Shared syntax for experiment evaluators
│       ├── WadlerFest.scala  # Stateful evaluator (§2, Figures 3–4)
│       ├── OneCPS.scala      # 1-CPS evaluator (§3.1)
│       ├── TwoCPS.scala      # 2-CPS definitional interpreter (§3.2)
│       ├── Delimited.scala   # Direct-style via shift/reset (§3.3, Figure 5)
│       └── CEKM.scala        # CEKM abstract machine (§4, Figure 6)
└── src/test/scala/
    ├── Interp.scala          # Tests for the optimizing evaluator
    └── experiment/           # Tests for each experiment evaluator
```

### Paper-to-code mapping

| Section | Content | File |
|---------|---------|------|
| §2 | Core language syntax (Figure 2) | `Syntax.scala`, `experiment/Syntax.scala` |
| §2 | Stateful WadlerFest evaluator (Figures 3–4) | `experiment/WadlerFest.scala` |
| §3.1 | 1-CPS transformation | `experiment/OneCPS.scala` |
| §3.2 | 2-CPS definitional interpreter | `experiment/TwoCPS.scala` |
| §3.3 | Delimited control (Figure 5) | `experiment/Delimited.scala` |
| §4 | CEKM abstract machine (Figure 6) | `experiment/CEKM.scala` |
| §5 | Reflect combinators, code cache | `Interp.scala` (`reflectAtom`, `Cache`) |
| §6 | Common sub-expression elimination | `Interp.scala` (`reflectCse`) |
| §7 | Constant folding | `Interp.scala` (`reflectSimp`) |
| §8 | Dead-code elimination | `Interp.scala` (`reflectDce`) |
| §9 | Partially-static data | `Interp.scala` (`reflectPS`), `Algebra.scala` |
| §10 | Inlining with renormalization | `Interp.scala` (`reflectInline`, `renormalize`) |
| §11 | Code motion (λ-hoisting) | `Interp.scala` (`hoist`, `reflectLam`) |
| §12 | Extensions (mutable refs, by-name, etc.) | `Interp.scala` (eval cases) |

## 4. Getting Started

From the repository root, run the entire test suite:

```bash
sbt test
```

The first invocation downloads Scala 3.8.0 and MUnit, then compiles and runs all
**68 tests**. A successful run ends with a line such as:

```
[info] Passed: Total 68, Failed 0, Errors 0, Passed 68
[success] Total time: ... s
```

This single command exercises every claim in the paper and is sufficient to
confirm the artifact is functional.

## 5. How to Run the Tests

### Run everything

```bash
sbt test
```

### Run one part of the artifact

```bash
# The optimizing staged evaluator (paper §5–§12)
sbt 'testOnly instar.interp.*'

# The family of definitional evaluators (paper §2–§4)
sbt 'testOnly instar.experiment.*'
```

### Run the tests for a single section / evaluator

Each paper section maps to a test class:

```bash
sbt 'testOnly instar.interp.Section6_CSE'        # §6  CSE
sbt 'testOnly instar.interp.Section9_PSD'        # §9  partially-static data
sbt 'testOnly instar.interp.Section10_Inlining'  # §10 inlining
sbt 'testOnly instar.experiment.cekm.CEKMTest'   # §4  CEKM machine
```

| Paper part | Test class |
|------------|------------|
| §2–§4 1-CPS evaluator | `instar.experiment.onecps.OneCPSTest` |
| §2–§4 2-CPS evaluator | `instar.experiment.twocps.TwoCPSTest` |
| §3.3 delimited control | `instar.experiment.delimited.DelimitedTest` |
| §2 WadlerFest evaluator | `instar.experiment.wadlerfest.WadlerFestTest` |
| §4 CEKM machine | `instar.experiment.cekm.CEKMTest` |
| §6 CSE | `instar.interp.Section6_CSE` |
| §7 constant folding | `instar.interp.Section7_Folding` |
| §8 dead-code elimination | `instar.interp.Section8_DCE` |
| §9 partially-static data | `instar.interp.Section9_PSD` |
| §10 inlining / renormalization | `instar.interp.Section10_Inlining` |
| §11 λ-hoisting | `instar.interp.Section11_Hoisting` |
| §12 extensions | `instar.interp.Section12_CBN`, `…_Analysis`, `…_Extensions` |

### Run a single test case

MUnit accepts a name filter via `--tests=`:

```bash
sbt 'testOnly instar.interp.Section6_CSE -- --tests=cse-1'
```

## 6. Reading the Tests and Reproducing Paper Examples

Each test builds an input term as an AST value and asserts the staged result.
A test looks like this (`src/test/scala/Interp.scala`):

```scala
test("cse-1") {
  val e5 = EBinOp2("+",
    EBinOp2("*", ENum2(2), ENum2(3)),
    EBinOp2("*", ENum2(2), ENum2(3)))
  testEval(e5,
    """⟨code:
      |  let x0 = (2 * 3) in
      |  let x1 = (x0 + x0) in
      |  x1⟩""".stripMargin, Set("cse"))
}
```

- **Input.** `e5` is the source term `(2 * 3) + (2 * 3)`, written directly with
  the AST constructors from `Syntax.scala`. The `…2` smart constructors (e.g.
  `ENum2`, `EBinOp2`) build *dynamic* (second-stage) nodes, while the `…1`
  variants build *static* nodes (see `Syntax.scala`).
- **Expected output.** The string is the generated object code, rendered by the
  pretty-printer `show` (`Syntax.scala`). `⟨code: … ⟩` wraps a residual program;
  staged `let`-bindings are the let-inserted bindings produced by the `reflect`
  combinators.
- **Optimizations.** The trailing `Set("cse")` selects which optimizations are
  enabled for that run. The harness resets all flags (`Opt.disableAll`) before
  enabling exactly the requested set, so each test specifies its configuration
  independently.

By comparing tests for the same input term under different flag sets (e.g.
`inline-cse-1` through `inline-cse-6`, which enable progressively more passes),
you can observe each optimization's effect in isolation and in combination,
matching the derivations in the paper.

### Optimization flags

The optimizing evaluator is configured through string flags (`Opt(...)` in
`src/main/scala/Interp.scala`):

| Flag | Optimization | Paper |
|------|--------------|-------|
| `cse` | common sub-expression elimination | §6 |
| `rewriting` | constant folding / static rewriting | §7 |
| `dce` | dead-code elimination | §8 |
| `ps` | partially-static data | §9 |
| `fun-inline` | function inlining | §10 |
| `no-let-lam` | suppress let-binding of λ-abstractions | §10 |
| `simp-cond` | conditional simplification | §10 |
| `lam-hoist` | code motion / λ-hoisting | §11 |

With no flags enabled, the evaluator performs only the baseline staging of §5
(constant propagation + let-insertion via the code cache).

