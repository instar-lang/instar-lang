## Instar: Stage-Polymorphic Meta-programming Language

### Getting Started

Requirements: JDK 17+, Scala, sbt

Install Scala: https://www.scala-lang.org/download/

Run `sbt` to start an interactive console.

### Interpreter

Currently there are three variant interpreters for the elaborated core language:

- `Core.scala` the pure two-level language (no recursion, no mutable store)
- `CoreEff.scala` imperative core with recursion and mutable stores
- `CoreEffOpt.scala` imperative core with additional optimizations for second-stage code

### TODO

High priority

- [x] need a name for the language
- [x] surface language syntax and parser
  - [x] ast definitions (Syntax.scala)
  - [x] parsing to ast
- [ ] type checking/inference/elaboration
  - [ ] type checking for core language (without bidirectional typing)
    - [ ] scala implementation
      - we need a type checker for this fully annotated language to build up
        correct understanding of the type system, and to see how many
        annotations can be inferred and removed.
    - [ ] lean mechanization
      - this will be an extension of the existing mechanization for the pldi26
        submission.
    - [ ] formalization of typing rules (in latex)
      - this will be an extension of pldi26 submission to include stage
        polymorphism.
  - [ ] type checking for surface language, elaborating surface language to core language (with bidirectional typing)
    - [ ] lean mechanization
    - [ ] formalization of typing rules (in latex)
- [ ] case study
  - [ ] explore stage-polymorphic standard library
  - [ ] stream fusion

Medium priority

- [ ] optimizations
  - [ ] lambda lifting or closure conversion
  - [ ] lambda dropping
  - [x] common sub-expression elimination (pure)
  - [x] code motion (lambda hoisting)
  - [x] function inlining
  - [x] simplification of pure expressions
  - [x] dead code elimination (pure)

Low priority

- [ ] back-end codegen
  - [ ] C backend
  - [ ] Wasm backend
  - [ ] Rust backend?
- [ ] type system tracking aliases and separation
- [ ] type polymorphism a la F