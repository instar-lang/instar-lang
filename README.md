## Stage-Polymorphic Meta-programming Language

### Interpreter

Currently there are three variant interpreters for the elaborated core language:

- `Core.scala` the pure two-level language (no recursion, no mutable store)
- `CoreEff.scala` imperative core with recursion and mutable stores
- `CoreEffOpt.scala` imperative core with additional optimizations for second-stage code

### TODO

High priority

- [ ] need a name for the language
- [ ] surface language syntax and parser
  - [ ] antlr4 grammar
  - [ ] ast definitions (Surface.scala)
  - [ ] parsing to ast
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
  - [ ] stream fusion


Medium priority

- [ ] explore stage-polymorphic standard library
- [ ] optimizations
  - [ ] lambda lifting or closure conversion
  - [ ] lambda dropping
  - [ ] common sub-expression elimination (pure)
  - [ ] code motion
  - [ ] function inlining
  - [x] simplification of pure expressions
  - [x] dead code elimination (pure)

Low priority

- [ ] back-end codegen
  - [ ] C backend
  - [ ] Wasm backend
  - [ ] Rust backend?
- [ ] type system tracking aliases and separation
- [ ] type polymorphism a la F

### Meeting notes
20251213 (Jun and Dinghong):
- Discussed the overall plan (see TODO list updates above)
- We will first focus on implementing type checking for a fully annotated
  monomorphic core language
  - Dinghong will work on Scala implementation of core language type checker
  - Jun will sort out the gap of Lean mechanization, and some test cases for scala type checker for core language
