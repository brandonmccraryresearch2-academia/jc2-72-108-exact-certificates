#!/bin/bash
# Compile every GGHV Lean part standalone (core Lean 4.34.0, no Mathlib).
# Usage: bash compile_all.sh   (from this directory, or anywhere)
# Exits non-zero if any file fails, and prints PASS/FAIL per file.
set -u
cd "$(dirname "$0")" || exit 1
LEAN="${HOME}/.elan/bin/lean"
fail=0
for f in Part1_Cases.lean Part2_Discards.lean Part3_NewtonReductions.lean \
         Part4_Systems.lean Part5_Assembly.lean Part6_Directions.lean \
         Part7_MonomialBracket.lean Part8_MaxSegments.lean \
         Part9_DirectionsGeneral.lean \
         Part13_FaceLists.lean \
         Part14_LFaceTerms.lean \
         Part15_FaceEndpoints.lean \
         Part16_PredSucc.lean \
         Part17_GGV1Definitions.lean \
         Part18_GGV1Prop82.lean \
         Part19_GGV1Cor74Thm76.lean \
         Part20_GGV1SuccPred.lean \
         Part21_GGV2Corners.lean \
         Part22_GGV2Prop312.lean \
         Part23_PossibleStartingPoints.lean \
         Part24_GGV2TextCheck.lean \
         Part25_GGV6Roots.lean \
         Part26_GGV6Props.lean \
         Part27_GGV6Prop25.lean \
         Part28_Table10.lean \
         Part29_PLLCFilter.lean \
         Part30_PFLLoop.lean \
         Part31_RowDegrees.lean \
         Part32_DegreePairs.lean \
         Part33_Ledger.lean \
         Part34_ReducedPremises.lean; do
  if out="$("$LEAN" "$f" 2>&1)"; then
    echo "PASS  $f"
  else
    echo "FAIL  $f"
    echo "$out"
    fail=1
  fi
done
# No sorry/admit/axiom declarations in any part file.
if grep -nE '^[[:space:]]*(axiom|sorry|admit)[[:space:]]' Part*.lean; then
  echo "FAIL  forbidden declaration found (see above)"
  fail=1
else
  echo "PASS  no sorry/admit/axiom declarations"
fi
exit $fail
