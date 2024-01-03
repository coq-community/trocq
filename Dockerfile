FROM coqorg/coq:8.17.1
COPY artifact-clean.zip artifact-clean.zip
RUN eval $(opam env "--switch=${COMPILER}" --set-switch)
RUN opam update -y
RUN unzip artifact-clean.zip
RUN cd artifact-clean && make