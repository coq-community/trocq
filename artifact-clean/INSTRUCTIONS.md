# Trocq

0. We use the Opam package manager, please install it from the
   official Opam webpage: https://opam.ocaml.org/doc/Install.html
   and add the Coq opam repository, with the following command:
   `opam repo add coq-released https://coq.*/opam/released`

1. Create a fresh Opam switch (development was done with
   OCaml 4.12.0, but anything newer should work). An existing switch may
   also be used, if:
   - the version the `coq` package is at least 8.17 and
   - the `coq-hott` packaged is either not installed or at version 8.17 and
   - package `coq-elpi` is **not** installed.

   The plugin indeed requires a custom version of Coq-Elpi, with features
   related to universe polymorphism that are still experimental. This
   is why a version of the Coq-Elpi sources is included in this
   artifact.

2. Install Trocq and its dependencies by running `make` in the root
   directory of the archive.

3. Open your IDE at the root of the `trocq` directory. Open and execute
   any of the example files present in the `trocq/examples` directory.

   The examples have been put inside the `trocq` project for the sake of
   convenience, so that the `-noinit`  and `-indices-matter` options of `coqtop` are taken into account in the IDE.

   Please use either:
   - CoqIDE (available in your switch via `opam install coqide`)
   - VSCode or VSCodium with the **VSCoq Legacy** extension.
   - emacs together with proof-general
