#!/bin/sh
rm -rf artifact-clean/trocq artifact-clean/coq-elpi
git clone -b strat --depth 1 https://github.com/ecranceMERCE/coq-elpi/ artifact-clean/coq-elpi
rm -f theories/.*.aux theories/*.glob theories/*.vo theories/*.vok theories/*.vos
mkdir artifact-clean/trocq/
mkdir artifact-clean/trocq/theories
mkdir artifact-clean/trocq/examples
cp theories/*.v artifact-clean/trocq/theories/
cp examples/*.v artifact-clean/trocq/examples/
rm -f artifact-clean/trocq/theories/Inductives.v
rm -f artifact-clean/trocq/examples/list_to_seq.v
cp -R elpi artifact-clean/trocq/elpi
cp _CoqProject artifact-clean/trocq/
cp Makefile artifact-clean/trocq/
cp coq-trocq.opam artifact-clean/trocq/
find artifact-clean/trocq -type f -exec sed -i 's/assia//gIm' {} +
find artifact-clean/trocq -type f -exec sed -i 's/cyril//gIm' {} +
find artifact-clean/trocq -type f -exec sed -i 's/enzo//gIm' {} +
find artifact-clean/trocq -type f -exec sed -i 's/mahboubi//gIm' {} +
find artifact-clean/trocq -type f -exec sed -i 's/cohen//gIm' {} +
find artifact-clean/trocq -type f -exec sed -i 's/crance//gIm' {} +
find artifact-clean/trocq -type f -exec sed -i 's/inria.fr//gIm' {} +
find artifact-clean/trocq -type f -exec sed -i 's/inria//gIm' {} +
find artifact-clean/trocq -type f -exec sed -i 's/merce//gIm' {} +
find artifact-clean/trocq -type f -exec sed -i 's/mitsubishi electric r.d centre europe//gIm' {} +
zip -u -r artifact-clean artifact-clean
