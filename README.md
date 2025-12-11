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
- [ ] type checking/inference/elaboration

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
