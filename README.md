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


[doi-shield]: https://zenodo.org/badge/DOI/10.5281/zenodo.10492403.svg
[doi-link]: https://doi.org/10.5281/zenodo.10492403

Trocq is a modular parametricity plugin for Coq. It can be used to
achieve proof transfer by both translating a user goal into another,
related, variant, and computing a proof that proves the corresponding implication.

The plugin features a hierarchy of structures on relations, whose
instances are computed from registered user-defined proof via
parametricity. This hierarchy ranges from structure-less relations
to an original formulation of type equivalence. The resulting
framework generalizes [raw
parametricity](https://arxiv.org/abs/1209.6336), [univalent
parametricity](https://doi.org/10.1145/3429979) and
[CoqEAL](https://github.com/coq-community/coqeal), and includes them
in a unified framework.

The plugin computes a parametricity translation "à la carte", by
performing a fine-grained analysis of the requires properties for a
given proof of relatedness. In particular, it is able to prove
implications without resorting to full-blown type equivalence,
allowing this way to perform proof transfer without necessarily
pulling in the univalence axiom.

The plugin is implemented in Coq-Elpi and the code of the
parametricity translation is fairly close to a pen-and-paper
sequent-style presentation.

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

Trocq is a still a prototype. In particular, it depends on a [custom
version](https://github.com/ecranceMERCE/coq-elpi/tree/strat) of
Coq-Elpi.  It is not yet packaged in Opam or Nix.

There are however three ways to experiment with it, all documented
in the [INSTALL.md file](INSTALL.md).

## Documentation

See the [tutorial](artifact-doc/TUTORIAL.md) for concrete use cases.

In short, the plugin provides a tactic:
- `trocq` (without arguments) which attempts to run a translation on
  a given goal, using the information provided by the user with the
  commands described below.

And three commands:
- `Trocq Use t` to use a translation `t` during the subsequent calls
  to the tactic `trocq`.
- `Trocq Register Univalence u` to declare a univalence axiom `u`.
- `Trocq Register Funext fe` to declare a function extensionality
  axiom `fe`.


## ESOP 2024 artifact documentation

The ESOP 2024 artifact documentation files can be found in the `artifact-doc` directory, except for `INSTALL.md` that can be found in the current directory.
