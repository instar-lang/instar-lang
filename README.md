## Instar: A Stage-Polymorphic Meta-programming Language

### Getting Started

Requirements: JDK 17+, Scala, sbt

Install Scala: https://www.scala-lang.org/download/

Run `sbt` to start an interactive console.

### Features

The distinctive feature of Instar is stage polymorphism, which allows us to write code that can be
instantiated at different stages.
For example, we can write the stage-polymorphic `power` function
with the stage parameter `s`, which can be instantiated as either stage 1 and stage 2.

```instar
letrec power[s](x: Int@s)(n: Int@1): Int@s =
  if n == 0
  then 1
  else x * power[s](x)(n - 1) in
let power3 =
  fun@2(x: Code[Int]) => power[2](x)(3) in
power3(4)
```

In the above example, we instantiate `power` at stage 2, and
generate a specialized `power3`, which will be called at the second stage as well.

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

- `target/scala-3.7.4/scoverage-report/`
