#!/bin/sh
Files="agda/funct/funext.lagda agda/funct/endo.lagda agda/init/initalg.lagda agda/init/fusion.lagda agda/init/initial.lagda agda/term/termcoalg.lagda agda/term/cofusion.lagda agda/term/terminal.lagda agda/church/defs.lagda agda/church/proofs.lagda agda/church/inst/list.lagda agda/church/inst/free.lagda agda/cochurch/defs.lagda agda/cochurch/proofs.lagda agda/cochurch/inst/list.lagda"
for f in $Files; do
  echo 'building' $f && /home/rogerse/.cabal/bin/agda --latex --latex-dir sections $f
done
