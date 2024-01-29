<p style="text-align: center"><img src="trocq-logo-text.png" alt="Trocq logo" width="50%" /></p>

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

[doi-shield]: https://zenodo.org/badge/DOI/10.5281/zenodo.10492403.svg
[doi-link]: https://doi.org/10.5281/zenodo.10492403

**Trocq** is a prototype of a modular parametricity plugin for **Coq**, aiming
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

The translation is implemented in **Coq-Elpi** and features transparent
and readable code with respect to a sequent-style theoretical presentation.

## Building and installation instructions

As **Trocq** is a prototype, it is currently unreleased, and depends on a
[custom version](https://github.com/ecranceMERCE/coq-elpi/tree/strat)
of **Coq-Elpi**. It is not yet packaged in **Opam** or **Nix**, but will be in
the near future.

There are however three ways to develop it and experiment with it,
they are documented in the [INSTALL.md file](https://github.com/coq-community/trocq/blob/master/INSTALL.md) of the repository.

## Documentation

There are several kinds of documentation for **Trocq**:

1. The motivation, theoretical basis, and formal definition of **Trocq** are given in our [article](https://hal.science/hal-04177913/document), with details about our parametricity framework, the supported hierarchy of structures, *etc*.
More theoretical details are available and implementation issues are discussed in a less space-constrained format in the related parts of Enzo Crance's [PhD thesis](https://ecrance.net/files/thesis-Enzo-Crance-en-light.pdf):
    - Part III, called *Trocq: proof transfer by parametricity*, currently page 69;
    - Part IV, called *Implementation of preprocessing tools with Coq-Elpi*, currently page 99.

2. A showcase of all the features of **Trocq** is available in the [examples](https://github.com/coq-community/trocq/tree/master/examples/) directory of the repository, and some of them are explained in the [tutorial](https://github.com/coq-community/trocq/blob/master/artifact-doc/TUTORIAL.md).

3. A quick start guide for complete beginners, written with practical utility in mind, is available on [this website](quick-start.md).