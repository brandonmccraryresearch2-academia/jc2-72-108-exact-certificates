/- Part 28 — D4 Part E, session 1: the §2 table of 10 cases
    (GGHV §1, "Complete list of small cases"), as data.

    The table, from [GGV5] §§5–6: every counterexample with
    max{deg P, deg Q} < 125 lies in one of these 10 rows (the
    §2 premise itself is [GGV5]'s, carried, not proved here).
    Rows (A₀, (m,n), max degree, discarded-in-table?):

    1. (4,12), (3,4), 64, discarded (GGV4 §3.5, M, H)
    2. (4,12), (5,7), 112, discarded (GGV4 §3.5)
    3. (5,20), (2,3), 75, discarded (GGV3 §5)
    4. (5,20), (3,2), 75, discarded (GGV3 §5)
    5. (7,21), (2,3), 84, not discarded in the table (GGHV §2
       discards it via [GGV6] Thm 7.3 — Parts 25–27)
    6. (8,24), (2,3), 96, discarded ([GGV5] Prop. 6.1)
    7. (8,28), (3,2), 108, not discarded (the * row — the
       (72,108) survivor row)
    8. (8,32), (3,2), 120, not discarded in the table (GGHV §2
       discards it via the §3-120 argument — Parts 19/21)
    9. (9,24), (2,3), 99, not discarded in the table
       ("no detail in M")
    10. (9,27), (2,3), 108, not discarded in the table
       (the §5 row — eliminated by Thm 5.1, see Part 5's
       row-vs-degree-pair correction)

    Checked below: all 10 max degrees are < 125; exactly 5
    rows are marked discarded in the table; the remaining
    rows' max degrees are [84, 108, 120, 99, 108]. The paper's
    theorem — a counterexample has max degree ≥ 125 or degree
    pair (72,108)/(108,72) — is the assembly of this table
    with the four in-paper discards plus the §4–§6 analysis
    of the (8,28) row; that assembly is Part F's work, not
    claimed here.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- A table row: (A₀x, A₀y, m, n, max degree, discarded?). -/
def table10 : List (Nat × Nat × Nat × Nat × Nat × Bool) :=
  [ (4, 12, 3, 4, 64, true)
  , (4, 12, 5, 7, 112, true)
  , (5, 20, 2, 3, 75, true)
  , (5, 20, 3, 2, 75, true)
  , (7, 21, 2, 3, 84, false)
  , (8, 24, 2, 3, 96, true)
  , (8, 28, 3, 2, 108, false)
  , (8, 32, 3, 2, 120, false)
  , (9, 24, 2, 3, 99, false)
  , (9, 27, 2, 3, 108, false) ]

/-- All 10 max degrees are < 125. -/
example : table10.length = 10 := by decide
example : table10.all (fun r => r.2.2.2.2.1 < 125) = true := by decide

/-- Exactly 5 rows are marked discarded in the table. -/
example : (table10.filter (fun r => r.2.2.2.2.2)).length = 5 := by decide

/-- The remaining rows' max degrees, in table order. -/
example : (table10.filter (fun r => !r.2.2.2.2.2)).map
    (fun r => r.2.2.2.2.1) = [84, 108, 120, 99, 108] := by decide

/-- The survivor row (8,28) is in the table with max degree
    108 and (m,n) = (3,2). -/
example : (8, 28, 3, 2, 108, false) ∈ table10 := by decide
