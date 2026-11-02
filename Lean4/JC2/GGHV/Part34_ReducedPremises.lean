/- Part 34 — D4 Part F, session 2: premise replacement,
    second half — the reduced premise structure and the
    assembly theorem. Part F is COMPLETE, and with it D4 as
    a whole is COMPLETE as a formalization programme
    (not as a proof: see the status below).

    The reduced structure keeps exactly the fields Parts
    B–E did NOT instance-discharge, and adds the two
    instance bundles as hypotheses. The assembly theorem
    states: from the reduced premises plus the two instance
    bundles, the full 7-field premise structure follows —
    by construction, since the instance fields are supplied
    by the bundles. Combined with Part 33's survivor
    computation, the survivor is (8,28) given the reduced
    premises plus the two bundles.

    Final status, stated plainly: NO field of Part 5's
    `AssemblyPremises` is unconditionally proved by D4.
    What D4 did is: (i) formalize every cited instance at
    the data/arithmetic level, (ii) reduce the premise
    structure from 7 opaque fields to 5 opaque fields plus
    2 instance bundles, and (iii) compute the survivor
    from the row→field map. The remaining gap is exactly
    the cited theorems' proofs ([GGV1] Prop. 8.2 item (2),
    k = 2 exclusion, Cor. 7.4 condition (3), full Dir/Succ
    theory, [GGV5] completeness, [GGV6] Prop. 2.5's
    statement, the red-row discards, the 99 discard, the
    Thm 5.1 elimination argument, the (7,21) §6 link) —
    plus, outside D4, branch (c) A1/A2, which remain the
    programme priority. Part 5's Theorem 2.1 stays
    CONDITIONAL until those are proved; D4 does not move
    any grade.

    The structures below restate Part 5's premise fields
    locally (standalone convention: no imports between
    Parts); Part 5 itself is edited separately to carry
    the same reduced structure (see the session report).

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- The full 7-field premise structure, restated locally. -/
structure AssemblyPremisesR where
  red_rows_discarded : Prop
  discard_84 : Prop
  discard_120 : Prop
  discard_924 : Prop
  discard_927 : Prop
  discard_721 : Prop
  enumeration : Prop

/-- The reduced structure: the 5 fields D4 did not
    instance-discharge. -/
structure ReducedPremises where
  red_rows_discarded : Prop
  discard_924 : Prop
  discard_927 : Prop
  discard_721 : Prop
  enumeration : Prop

/-- Assembly: reduced premises + the two instance bundles
    give the full premise structure. (A `def`, not a
    theorem: it constructs the structure value.) -/
def assemble (r : ReducedPremises) (d84 d120 : Prop) :
    AssemblyPremisesR where
  red_rows_discarded := r.red_rows_discarded
  discard_84 := d84
  discard_120 := d120
  discard_924 := r.discard_924
  discard_927 := r.discard_927
  discard_721 := r.discard_721
  enumeration := r.enumeration
