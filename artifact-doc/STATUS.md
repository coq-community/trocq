# Badges applied for

We apply for the Functional, Reusable and Available badges on this artifact.

## Functional

We believe that this artifact covers the content of the paper. Indeed, the Coq files include a formalisation of the parametricity witness types presented in the paper, proofs of equivalence of the highest witness type with univalent parametricity, and various lemmas (symmetry, reflexivity, *etc.*). The fact that these proofs are formal proofs gives extra confidence that our results are correct. The Elpi files contain a parametricity framework implementation on top of this hierarchy of parametricity witness types. The architecture of the plugin enables the presentation of readable code, such as the `param.elpi` file corresponding to the core of the inference rules presented in the paper.

## Reusable

This artifact is in reality a specially packaged version of a Coq plugin that, as such, aims to be installed by a substantial number of users and to evolve with the proof assistant in the mid term. To that end, we provide extensive documentation, both for users and developers, and the architecture of the plugin is made so that a user can actually make use of it in conditions of a real Coq formalisation.

## Available

Via [https://www.softwareheritage.org/](https://archive.softwareheritage.org/browse/revision/1268bcbbc4143bc26c03e9e0ccb29216f36f5f91/?origin_url=https://github.com/coq-community/trocq).
