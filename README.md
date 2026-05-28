# Artifact for "Let It Be Optimized"

## 1. Paper Summary

This artifact accompanies the ICFP '26 pearl *"Let It Be Optimized"*. 
The paper reconstructs optimizing staged evaluation as found in
library-based multi-stage programming (MSP) systems (e.g., LMS, BuildIt) as a
proper calculus with executable semantic artifacts.

All semantic artifacts are implemented in Scala 3 as executable code, serving as
a reference implementation for the paper's figures and claims.

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

## 4. How to Run the Tests
