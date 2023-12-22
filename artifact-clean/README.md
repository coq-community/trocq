# Trocq

Trocq is a prototype of a modular parametricity plugin for Coq, aiming
to perform proof transfer by translating the goal into an associated
goal featuring the target data structures as well as a rich
parametricity witness from which a function justifying the goal
substitution can be extracted.

The plugin features a hierarchy of parametricity witness types,
ranging from structure-less relations to a new formulation of type
equivalence, gathering several pre-existing parametricity
translations, including
[univalent parametricity](https://doi.org/10.1145/3429979) and
[CoqEAL](https://github.com/coq-community/coqeal), in the same framework.

This modular translation performs a fine-grained analysis and
generates witnesses that are rich enough to preprocess the goal yet
are not always a full-blown type equivalence, allowing to perform
proof transfer with the power of univalent parametricity, but trying
not to pull in the univalence axiom in cases where it is not required.

The translation is implemented in Coq-Elpi and features transparent
and readable code with respect to a sequent-style theoretical presentation.

## How to reproduce the results of the paper

todo

## Relation between the files and the theoretical presentation in the paper

todo