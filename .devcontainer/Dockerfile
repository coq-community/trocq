FROM coqorg/coq:8.17.1
RUN eval $(opam env "--switch=${COMPILER}" --set-switch)
RUN opam update -y
RUN opam install -y coq-lsp
RUN git clone -b strat --depth 1 https://github.com/ecranceMERCE/coq-elpi
RUN opam install -y ./coq-elpi
RUN opam install -y coq-mathcomp-algebra.1.19.0