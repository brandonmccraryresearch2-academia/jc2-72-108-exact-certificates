/- Part 31 — D4 Part E, session 4: the row-to-degree
    computation, as a verified computation.

    The family formula (already in Part 5 as `degreePair`):
    for a row with A₀ = (a,b) and (m,n), the degree pair is
    (m·(a+b), n·(a+b)), and the max degree is
    max(m,n)·(a+b). Checked below over all 10 §2 rows: the
    computed max degree equals the table's max degree in
    every row. This is the computation behind Part 28's
    table and Part 5's survivor arithmetic; the claim that
    these rows exhaust the sub-125 cases is [GGV5]'s,
    carried, not proved here.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- A row: (A₀x, A₀y, m, n, table max degree). -/
def rows10 : List (Nat × Nat × Nat × Nat × Nat) :=
  [ (4, 12, 3, 4, 64)
  , (4, 12, 5, 7, 112)
  , (5, 20, 2, 3, 75)
  , (5, 20, 3, 2, 75)
  , (7, 21, 2, 3, 84)
  , (8, 24, 2, 3, 96)
  , (8, 28, 3, 2, 108)
  , (8, 32, 3, 2, 120)
  , (9, 24, 2, 3, 99)
  , (9, 27, 2, 3, 108) ]

/-- Max degree from the family formula. -/
def rowMaxDeg (r : Nat × Nat × Nat × Nat × Nat) : Nat :=
  max r.2.2.1 r.2.2.2.1 * (r.1 + r.2.1)

/-- The computed max degree equals the table's in all 10
    rows. -/
example : rows10.all (fun r => rowMaxDeg r = r.2.2.2.2) = true := by decide

/-- The degree pair of the survivor row (8,28) is (108,72),
    and its swap is (72,108). -/
example : (3 * (8 + 28), 2 * (8 + 28)) = (108, 72) := by decide
example : (2 * (8 + 28), 3 * (8 + 28)) = (72, 108) := by decide
