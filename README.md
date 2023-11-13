<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Trocq

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/coq-community/trocq/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/trocq/actions?query=workflow:"Docker%20CI"




Trocq is a prototype of modular parametricity plugin for Coq, aiming
to perform proof transfer by translating the goal into an associated
goal featuring the target data structures as well as a rich
parametricity witness from which a function justifying the goal
substitution can be extracted.

The plugin features a hierarchy of parametricity witness types,
ranging from structure-less relations to a new formulation of type
equivalence, gathering several pre-existing parametricity
translations, among which univalent parametricity [1] and
CoqEAL [2], under the same framework.

This modular translation performs a fine-grained analysis and
generates witnesses that are rich enough to preprocess the goal yet
are not always a full-blown type equivalence, allowing to perform
proof transfer with the power of univalent parametricity, but trying
not to pull in the univalence axiom in cases where it is not required.

The translation is implemented in Coq-Elpi and features transparent
and readable code with respect to a sequent-style theoretical presentation.

[1] The marriage of univalence and parametricity, Tabareau et al. (2021)
[2] https://github.com/coq-community/coqeal

## Meta

- Author(s):
  - Cyril Cohen (initial)
  - Enzo Crance (initial)
  - Assia Mahboubi (initial)
- License: [GNU Lesser General Public License v3.0](LICENSE)
- Compatible Coq versions: Coq 8.17
- Additional dependencies:
  - [Coq-Elpi custom version](https://github.com/ecranceMERCE/coq-elpi/tree/strat)
  - [Coq-HoTT 8.17](https://github.com/HoTT/Coq-HoTT)
- Coq namespace: `Trocq`
- Related publication(s):
  - [<nil>](https://hal.science/hal-04177913/document) 

## Building and installation instructions

As Trocq is a prototype, it is currently unreleased, and depends on a
development version of Coq-ELPI. There is not yet a dedicated way to
install it.

There are however two ways to develop it and experiment with it:

### Through nix

1. First install nix https://nixos.org/download
2. Add the [cachix](https://docs.cachix.org/installation) repository `coq-community`
```shell
nix-env -iA cachix -f https://cachix.org/api/v1/install
cachix use coq-community
```
3. Clone the current repository and type `nix-shell`
```shell
git clone https://github.com/coq-community/trocq.git
nix-shell
```
4. You may also use `nix-build` to build it and reuse it as a nix package.

### Through opam

1. Install [opam](https://opam.ocaml.org/doc/Install.html)
2. Install the custom version of coq-elpi
```shell
opam pin add coq-elpi https://github.com/ecranceMERCE/coq-elpi/archive/refs/heads/strat.tar.gz
```
3. Build Trocq
```shell
git clone https://github.com/coq-community/trocq.git
cd trocq
make   # or make -j <number-of-cores-on-your-machine> 
```
4. You may also `make install` it to install it on your system.

## Documentation

Upcoming
