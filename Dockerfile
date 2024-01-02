FROM coqorg/coq:8.17.1

RUN eval $(opam env "--switch=${COMPILER}" --set-switch)
RUN opam update -y
RUN cd artifact-clean
RUN opam install -y -j "${NJOBS}" ./coq-elpi
RUN cd ..
RUN opam install -y -j "${NJOBS}" .
