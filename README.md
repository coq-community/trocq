<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Trocq

[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![DOI][doi-shield]][doi-link]


[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users


[doi-shield]: https://zenodo.org/badge/DOI/10.5281/zenodo.10492404.svg
[doi-link]: https://doi.org/10.5281/zenodo.10492404

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

## Meta

- Author(s):
  - Cyril Cohen (initial)
  - Enzo Crance (initial)
  - Assia Mahboubi (initial)
- Coq-community maintainer(s):
  - Cyril Cohen ([**@CohenCyril**](https://github.com/CohenCyril))
  - Enzo Crance ([**@ecranceMERCE**](https://github.com/ecranceMERCE))
  - Assia Mahboubi ([**@amahboubi**](https://github.com/amahboubi))
- License: [GNU Lesser General Public License v3.0](LICENSE)
- Compatible Coq versions: 8.17
- Additional dependencies:
  - [Coq-Elpi custom version](https://github.com/ecranceMERCE/coq-elpi/tree/strat)
  - [Coq-HoTT 8.17](https://github.com/HoTT/Coq-HoTT)
- Coq namespace: `Trocq`
- Related publication(s):
  - [Trocq: Proof Transfer for Free, With or Without Univalence](https://hal.science/hal-04177913/document) 

## Building and installation instructions

As Trocq is a prototype, it is currently unreleased, and depends on a
[custom version](https://github.com/ecranceMERCE/coq-elpi/tree/strat)
of Coq-Elpi. It is not yet packaged in Opam or Nix, but will be in
the near future.

There are however three ways to develop it and experiment with it,
they are documented in the [INSTALL.md file](INSTALL.md).

## Documentation

For now, there is one tactic:
- `trocq` (without arguments) which attempts to run a translation on
a given goal, using the information provided by the user with the
commands described below.

And three commands:
- `Trocq Use t` to use a translation `t` during the subsequent calls to
the tactic `trocq`.
- `Trocq Register Univalence u` to declare a univalence axiom `u`.
- `Trocq Register Funext fe` to declare a function extensionality axiom `fe`.

See the [tutorial](artifact-doc/TUTORIAL.md) for concrete usecases.

## ESOP 2024 artifact documentation

The ESOP 2024 artifact documentation files can be found in the `artifact-doc` directory, except for `INSTALL.md` that can be found in the current directory.
