# Dafny toy
Deductively verifies a _program_ using Hoare Logic & First Order Logic

### Dafny engine
Self-Verifying Prgrogramming Language made by Microsoft [Dafny](https://github.com/Microsoft/dafny)

### Basics
{Pre-cond} _program_ {Post-cond}
_for loops:_
{Pre-cond} {Invariant} {Invariant and cond} _loop_ {Invariant} {Invariant and not cond} {Post-cond}
#### _Tips_
- __Specs__ are the most important things!! (without specs, impossible to verify)
- __Invariant__ is hard to find, but use your intuition :)
