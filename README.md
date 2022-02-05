# exsub-ccc

Categorical semantics of functional type theory with explicit substitutions, formalized in Agda.

This project depends on [agda-categories](https://github.com/agda/agda-categories) library.

- The semantics is given by the correspondence between functional type theories and Cartesian Closed Categories (CCC).
- We use de Bruijn index, as opposed to named variables, because we don't want to bother with α-equivalent terms.
- We use explicit substitutions because shift/substitution are tedious to deal with, and more importantly, explicit substitutions scale to dependent type theories.

## Status

- [x] Soundness
- [ ] Completeness

## References

- Roy L. Crole. Categories for Types. Cambridge University Press. 1993.
