### Interpreter

Currently there are three variant interpreters for the elaborated core language:

There are several variant interpreters for the language:

- `experiment/Core.scala` the pure two-level language (no recursion, no mutable store)
- `experiment/CoreEff.scala` imperative core with recursion and mutable stores
- `experiment/CoreAbsMachine.scala` an abstract machine for let-inserting staging semantics
- `experiment/CoreImp.scala` stateful implementation of `Core.scala`
- `experiment/CoreDelimited.scala` an implementation of `Core.scala` using delimited control operators (embedded as monads)
- `Interpreter.scala` the current main interpreter, with all features and some optimizations over the generated code

### TODO

High priority

- [x] need a name for the language
- [x] surface language syntax and parser
  - [x] ast definitions (Syntax.scala)
  - [x] parsing to ast
- [ ] type checking/inference/elaboration
  - [x] scala implementation
    - not much inference yet, but we can check the types of fully annotated programs
  - [ ] inference of stage annotations and instantiations
  - [ ] lean mechanization
  - [ ] formalization of typing rules (in latex)
- [ ] case study
  - [ ] explore stage-polymorphic standard library
  - [ ] stream fusion
- [ ] algebraic datatype

Medium priority

- [ ] type system tracking aliases and separation
- [ ] generate recursive definitions (see `tests/ackermann.instar` a challenging example and https://okmij.org/ftp/meta-programming/genletrec/genletrec.pdf)
- [ ] module/functor
- [ ] optimizations
  - [ ] lambda lifting or closure conversion
  - [ ] lambda dropping
  - [x] common sub-expression elimination (pure)
  - [x] code motion (lambda hoisting)
  - [x] function inlining
  - [x] simplification of pure expressions
  - [x] dead code elimination (pure)

Low priority

- back-end codegen
  - [x] C backend
  - [ ] Wasm backend
  - [ ] Rust backend?
- [ ] type polymorphism a la F-sub
- [x] pretty printer
- [ ] convenient syntax for assignment
