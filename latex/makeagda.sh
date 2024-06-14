#!/bin/sh
Files="agda/examples/container.lagda agda/funct/funext.lagda agda/church/initial.lagda agda/cochurch/terminal.lagda agda/cochurch/terminalbisim.lagda agda/church/defs.lagda agda/church/proofs.lagda agda/church/inst/list.lagda agda/church/inst/free.lagda agda/cochurch/defs.lagda agda/cochurch/proofs.lagda agda/cochurch/inst/list.lagda"
for f in $Files; do
  echo 'building' $f && /home/rogerse/.cabal/bin/agda --latex --latex-dir sections $f
done
