# Artifact for "Let It Be Optimized"

## 1. Paper Summary

This artifact accompanies the ICFP '26 paper *"Let It Be Optimized: Building
Multi-Stage Evaluators with Let-Insertion and Optimizations in Small Pieces
(Functional Pearl)"*.
The paper reconstructs optimizing staged evaluation as found in
library-based multi-stage programming (MSP) systems (e.g., LMS, BuildIt) as a
proper calculus with executable semantic artifacts.

All semantic artifacts are implemented in Scala 3 as executable code, serving as
a reference implementation for the paper's exposition and claims. The artifact is
organized as two complementary parts:

1. **A family of definitional evaluators** (`src/main/scala/`) that
   explain the derivation of different style of evaluation, from a stateful
   evaluator to CPS interpreters, a direct-style interpreter using delimited
   control, and finally an abstract machine (§2–§4).
2. **A single optimizing staged evaluator** (`src/main/scala/TwoCPSOpt.scala`) based
   one the 2-CPS interpreter that realizes each optimization from the paper (§5–§12)
   as modular combinators, toggled independently at run time.

Every claim in the paper is backed by an executable test. The artifact is
self-contained: the only external dependency is the
[MUnit](https://scalameta.org/munit/) test framework, fetched automatically by
the build tool.

### Claims supported by this artifact

- The definitional evaluators in §2–§4 are functionally equivalent: each
  produces the same staged object code given the same input.
  This is backed empirically by the test suite (see `src/test/scala/`)
  and can be justified following the derivations in the paper.
- Each optimization of §5–§11 (constant propagation, CSE, constant folding,
  dead-code elimination, partially-static data, inlining with renormalization,
  and λ-hoisting) is implemented as an independent, composable pass, and the
  examples shown in the paper reduce to the stated object code (see
  `src/test/scala/TwoCPSOpt.scala`).
- Additional extensions (mutable references, by-name staging, etc.) can
  be added to the same framework with minimal changes to the core evaluator (see
  `src/main/scala/TwoCPSOpt.scala` eval cases and `src/test/scala/TwoCPSOpt.scala`
  Section 12 tests).

## 2. Environment

- **JDK**: 17
- **Scala**: 3.8.0 (managed by sbt)
- **Build tool**: sbt 1.11+

## 3. Code Structure

```
├── build.sbt
├── src/main/scala/
│   ├── Syntax.scala          # Shared syntax for definitional evaluators (§2, Figure 2)
│   ├── ExtSyntax.scala       # Full core two-stage language AST
│   ├── WadlerFest.scala      # Stateful evaluator (§2, Figures 3–4)
│   ├── OneCPS.scala          # 1-CPS evaluator (§3.1)
│   ├── TwoCPS.scala          # 2-CPS definitional interpreter (§3.2)
│   ├── Delimited.scala       # Direct-style via shift/reset (§3.3, Figure 5)
│   ├── CEKM.scala            # CEKM abstract machine (§4, Figure 6)
│   ├── TwoCPSOpt.scala       # Optimizing staged evaluator (§5–§12)
│   ├── BiMap.scala           # Bidirectional map (code cache, §5.2)
│   ├── Algebra.scala         # Partially-static data algebra (§9)
│   └── Counter.scala         # Fresh variable name generator
└── src/test/scala/
    ├── WadlerFest.scala      # Tests for the stateful evaluator (§2)
    ├── OneCPS.scala          # Tests for the 1-CPS evaluator (§3.1)
    ├── TwoCPS.scala          # Tests for the 2-CPS evaluator (§3.2)
    ├── Delimited.scala       # Tests for the delimited control evaluator (§3.3)
    ├── CEKM.scala            # Tests for the CEKM machine (§4)
    └── TwoCPSOpt.scala       # Tests for the optimizing evaluator (§5–§12)
```

### Paper-to-code mapping

| Section | Content | File |
|---------|---------|------|
| §2 | Core language syntax (Figure 2) | `Syntax.scala`, `ExtSyntax.scala` |
| §2 | Stateful WadlerFest evaluator (Figures 3–4) | `WadlerFest.scala` |
| §3.1 | 1-CPS transformation | `OneCPS.scala` |
| §3.2 | 2-CPS definitional interpreter | `TwoCPS.scala` |
| §3.3 | Delimited control (Figure 5) | `Delimited.scala` |
| §4 | CEKM abstract machine (Figure 6) | `CEKM.scala` |
| §5 | Reflect combinators, code cache | `TwoCPSOpt.scala` (`reflectAtom`, `Cache`) |
| §6 | Common sub-expression elimination | `TwoCPSOpt.scala` (`reflectCse`) |
| §7 | Constant folding | `TwoCPSOpt.scala` (`reflectSimp`) |
| §8 | Dead-code elimination | `TwoCPSOpt.scala` (`reflectDce`) |
| §9 | Partially-static data | `TwoCPSOpt.scala` (`reflectPS`), `Algebra.scala` |
| §10 | Inlining with renormalization | `TwoCPSOpt.scala` (`reflectInline`, `renormalize`) |
| §11 | Code motion (λ-hoisting) | `TwoCPSOpt.scala` (`hoist`, `reflectLam`) |
| §12 | Extensions (mutable refs, by-name, etc.) | `TwoCPSOpt.scala` (eval cases) |

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
sbt 'testOnly instar.twocpsopt.*'

# The family of definitional evaluators (paper §2–§4)
sbt 'testOnly instar.cekm.* instar.wadlerfest.* instar.onecps.* instar.twocps.* instar.delimited.*'
```

### Run the tests for a single section / evaluator

Each paper section maps to a test class:

```bash
sbt 'testOnly instar.wadlerfest.WadlerFestTest'           # §2  stateful evaluator
sbt 'testOnly instar.onecps.OneCPSTest'                   # §3.1  1-CPS
sbt 'testOnly instar.twocps.TwoCPSTest'                   # §3.2  2-CPS
sbt 'testOnly instar.delimited.DelimitedTest'             # §3.3  delimited control
sbt 'testOnly instar.cekm.CEKMTest'                       # §4  CEKM machine
sbt 'testOnly instar.twocpsopt.Section6_CSE'              # §6  CSE
sbt 'testOnly instar.twocpsopt.Section7_Folding'          # §7  constant folding
sbt 'testOnly instar.twocpsopt.Section8_DCE'              # §8  dead-code elimination
sbt 'testOnly instar.twocpsopt.Section9_PSD'              # §9  partially-static data
sbt 'testOnly instar.twocpsopt.Section10_Inlining'        # §10 inlining
sbt 'testOnly instar.twocpsopt.Section11_Hoisting'        # §11 λ-hoisting
sbt 'testOnly instar.twocpsopt.Section12_Extensions'      # §12 extensions
```

### Run a single test case

MUnit accepts a name filter via `--tests=`:

```bash
sbt 'testOnly instar.twocpsopt.Section6_CSE -- --tests=cse-1'
```

## 6. Reading the Tests and Reproducing Paper Examples

Each test builds an input term as an AST value and asserts the staged result.
A test looks like this (`src/test/scala/TwoCPSOpt.scala`):

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
`src/main/scala/TwoCPSOpt.scala`):

| Flag | Optimization | Paper |
|------|--------------|-------|
| `cse` | common sub-expression elimination | §6 |
| `rewriting` | constant folding / static rewriting | §7 |
| `dce` | dead-code elimination | §8 |
| `ps` | partially-static data | §9 |
| `fun-inline` | function inlining | §10 |
| `simp-cond` | conditional simplification | §10 |
| `lam-hoist` | code motion / λ-hoisting | §11 |

With no flags enabled, the evaluator performs only the baseline staging of §5
(constant propagation + let-insertion via the code cache).

