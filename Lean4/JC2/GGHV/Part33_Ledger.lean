/- Part 33 — D4 Part F, session 1: premise replacement,
    first half — the discharge ledger and the survivor
    computation.

    Part 5's `AssemblyPremises` has 7 fields. This ledger
    records, for each field, what Parts B–E actually did to
    it. Statuses: `instance` = the field's instance is
    formalized (data + arithmetic + the cited theorem as a
    carried bundle; the cited theorem itself is NOT proved
    here); `ingredients` = supporting material formalized,
    the discard argument itself not proved; `external` =
    untouched by D4 (still a citation); `unpinned` = the
    field's exact meaning not pinned (counted as not
    discharged).

    Ledger:

    - red_rows_discarded: EXTERNAL (GGV4 §3.5, GGV3 §5, M, H).
    - discard_84 (§2, (7,21) row): INSTANCE (Parts 25–27:
      I_M = 4, I_m = 5, I_m ≤ I_M from [GGV6]'s two theorems).
    - discard_120 (§2, (8,32) row): INSTANCE (Parts 19/21/24:
      (8,4) excluded by Prop. 3.29 / "casos imposibles",
      d₀ = 4, ℓ_{1,0}(P) = R^{4m}).
    - discard_924 ((9,24) row, 99): EXTERNAL (no D4 session
      addressed the 99 discard; "no detail in M" in the
      table).
    - discard_927 ((9,27) row): INGREDIENTS (Parts 8/13–17:
      faces and endpoints for the §5 shapes; the Thm 5.1
      elimination argument itself is not a proved theorem
      in the library).
    - discard_721 ((7,21) case, §6 system): INGREDIENTS
      (Part 3 records both the Prop. 4.4 and §6 polygon
      lists; the transformation linking them is OPEN, and
      the §6 elimination identities are D3's for the
      principal equations, not a row discard proof).
    - enumeration (§2 premise, [GGV5] §§5–6): INSTANCE as
      data (Parts 28–32: table, row degrees, PLLC filter,
      PFL loop) with the completeness claim carried from
      [GGV5].

    Survivor computation, checked below: mapping each of
    the 10 rows to its discard field (or none) leaves
    exactly one row without a field — the (8,28) row. So,
    GIVEN the 7 fields, the survivor is row828. That is the
    content Part F adds to Part 5's conditional theorem,
    whose proof did not use the premises at all.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- Discard fields, as an enumeration. -/
inductive DiscardField where
  | red
  | d84
  | d120
  | d924
  | d927
  | d721
  | enumeration
  deriving DecidableEq, Repr

/-- The row → discard-field map, in table order; `none` for
    the survivor row. -/
def rowField : List (Nat × Nat × Option DiscardField) :=
  [ (4, 12, some DiscardField.red)
  , (4, 12, some DiscardField.red)
  , (5, 20, some DiscardField.red)
  , (5, 20, some DiscardField.red)
  , (7, 21, some DiscardField.d84)
  , (8, 24, some DiscardField.red)
  , (8, 28, none)
  , (8, 32, some DiscardField.d120)
  , (9, 24, some DiscardField.d924)
  , (9, 27, some DiscardField.d927) ]

/-- Exactly one row has no discard field, and it is (8,28). -/
example : (rowField.filter (fun r => r.2.2 = none)) = [(8, 28, none)] := by decide

/-- The (7,21) row's second claim (d721, §6 system) is a
    further claim on an already-discarded row, not a new
    survivor: the survivor computation is unchanged by it. -/
example : (rowField.filter (fun r => r.2.2 = none)).length = 1 := by decide
