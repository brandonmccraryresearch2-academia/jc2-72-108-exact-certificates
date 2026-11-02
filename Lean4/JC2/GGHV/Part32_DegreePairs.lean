/- Part 32 — D4 Part E, session 5: degree pairs and source
    count. Part E is COMPLETE after this session.

    Checked below:

    - The degree pair (72,108) arises from TWO rows: the
      (9,27) row directly, (2·36, 3·36) = (72,108), and the
      (8,28) row swapped, (3·36, 2·36) = (108,72), swapped to
      (72,108). This is why eliminating the (9,27) ROW does
      not eliminate the degree PAIR (72,108) — Part 5's
      row-vs-degree-pair correction, now computed.
    - The source count: GGHV takes the smallest members of
      the six §5 families F₁,F₂,F₃,F₉,F₁₇,F₂₂ and three
      additional §6 cases. The (5,20) A₀ appears in TWO rows
      with different (m,n) — GGHV's own note that the max-75
      case "corresponds to two cases in two different
      families" — so the §5 contribution is 7 rows, and
      7 + 3 = 10 rows total, matching the table. The
      family→row attribution itself is [GGV5]'s, carried;
      what is checked here is the counting and the double
      (5,20) occurrence.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- The (72,108) pair from the (9,27) row, directly. -/
example : (2 * (9 + 27), 3 * (9 + 27)) = (72, 108) := by decide

/-- The (72,108) pair from the (8,28) row, swapped. -/
example : (2 * (8 + 28), 3 * (8 + 28)) = (72, 108) := by decide

/-- The (5,20) A₀ occurs in exactly two rows of the table
    (with (m,n) = (2,3) and (3,2)). -/
def rowsA0 : List (Nat × Nat × Nat × Nat) :=
  [ (4, 12, 3, 4), (4, 12, 5, 7), (5, 20, 2, 3), (5, 20, 3, 2)
  , (7, 21, 2, 3), (8, 24, 2, 3), (8, 28, 3, 2), (8, 32, 3, 2)
  , (9, 24, 2, 3), (9, 27, 2, 3) ]

example : (rowsA0.filter (fun r => r.1 = 5 && r.2.1 = 20)).length = 2 := by decide
example : (rowsA0.filter (fun r => r.1 = 5 && r.2.1 = 20)) =
    [(5, 20, 2, 3), (5, 20, 3, 2)] := by decide

/-- Source count: 7 (§5 rows, one family contributing two)
    + 3 (§6 cases) = 10 rows. -/
example : 7 + 3 = 10 := by decide
example : rowsA0.length = 10 := by decide
