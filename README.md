## Instar: A Stage-Polymorphic Meta-programming Language

Instar is a research programming language with multi-stage programming.
It is still under active development.
One distinctive feature of Instar is stage polymorphism, which allows to
write code that can be instantiated at different stages.
For example, we can write the stage-polymorphic `power` function
with the stage parameter `s`, which can be instantiated as either stage 1 and stage 2.

```instar
letrec power[s](x: Int@s)(n: Int): Int@s =
  if n == 0
  then 1
  else x * power[s](x)(n - 1) in
// to specialize power given n is 3:
let power3 =
  fun@2(x: Code[Int]) => power[2](x)(3) in
power3(4)
```

In the above example, we instantiate `power` with stage 2, and generate a
specialized `power3`, which will be called at the second stage.

### Getting Started

Requirements: JDK 17+, Scala, sbt

Install Scala: https://www.scala-lang.org/download/

Run `sbt` to start an interactive console.

### Try Examples

To run an Instar program:

```
sbt:instar-lang> run --emit-c tests/impPower.instar
```

With the `--emit-c` flag, the next-stage C code will be generated at `tests/impPower.c`.

To run inlined program:

```
sbt:instar-lang> run --program "1 + 2 * 3"
```

### Coverage

To get statement coverage for the current test suite:

- `sbt coverageAll`

To focus on the main parser/interpreter/C-backend suites:

- `sbt coverageMain`

The HTML and XML reports are written under:

- `target/scala-3.8.0/scoverage-report/`

### Publication

- Let It Be Optimized: Building Multi-Stage Evaluators with Let-Insertion and Optimizations in Small Pieces (Functional Pearl)

  Guannan Wei, Jun Tan, and Dinghong Zhong. ICFP 26

  The [icfp26](https://github.com/instar-lang/instar-lang/tree/icfp26) branch contains the corresponding artifact.

