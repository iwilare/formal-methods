# Formal Methods in Agda

Agda formalization for operational semantics of a simple imperative language, type-based information flow security, Hoare logic, verification conditions, and separation logic.

## Files structure

- [IMP](IMP.agda): syntax of the IMP language; evaluation of expressions and substitution lemma.
- [OperationalSemantics](OperationalSemantics.agda): small-step and big-step semantics for IMP; determinism, program equivalence, equivalence between the two semantics.
- [Security](Security.agda): security type system for IMP; non-interference, anti-monotonicity, confinement lemma.
- [Types](Types.agda): type system for IMP; preservation, progress, type soundness.
- [HoareLogic](HoareLogic.agda): Hoare logic; syntax, weakest preconditions, completeness and soundness.
- [SeparationLogic](SeparationLogic.agda): separation logic; frame lemmas.
