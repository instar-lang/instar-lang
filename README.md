## Instar: A Stage-Polymorphic Meta-programming Language

### Getting Started

Requirements: JDK 17+, Scala, sbt

Install Scala: https://www.scala-lang.org/download/

Run `sbt` to start an interactive console.

### Features

The distinctive feature of Instar is stage polymorphism, which allows us to write code that can be
instantiated at different stages.
For example, we can write a power function that can be instantiated at both stage 1 and stage 2:

```instar
letrec power[s](x: Int@s)(n: Int): Int@s =
  if n == 0
  then lift[s](1)
  else x *@s power[s](x)(n - 1)
in ...
```

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
