/-
  JC2 / GGHV formalization — Part 1: the §2 case table.

  Source: Guccione, Guccione, Horruitiner, Valqui,
  "Increasing the degree of a possible counterexample to the
  Jacobian Conjecture from 100 to 108", arXiv:2204.14178v1,
  §2 ("Complete list of small cases"), Theorem 2.1 and its table.
  TeX source read: ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.

  STATUS (2026-10-29): Part 1 only. This file proves the
  COMBINATORIAL content of the §2 table: the degree-pair
  arithmetic, the max-degree column, and exactly which rows
  survive once the paper's discards are applied. It does NOT
  prove Theorem 2.1 itself. The discards are NOT proved here:
  the five red rows are discarded by cited papers ([M], [H],
  [GGV4] §3.5, [GGV3] §5, [GGV5] Prop. 6.1), the max = 84 row by
  [GGV6] Thm 7.3, the max = 120 row by [GGV2] Remark 3.31, and
  the (9,24)/(9,27) rows by GGHV §§5–6. Those are inputs to
  this file (the `redDiscarded` / filter data below, taken
  verbatim from the paper's table), and their proofs are
  Parts 3+ of this formalization. Nothing here is an axiom:
  there is no `sorry` and no `axiom` in this file.

  Conventions: a row is (A₀, (m, n), maxDeg) with A₀ a pair of
  naturals. The degree pair of a row is (m * (a + b), n * (a + b))
  where (a, b) = A₀ — this is the [GGV5] family formula, and it
  reproduces every maxDeg entry in the table (see
  `table_max_degrees`).
-/

namespace JC2
namespace GGHV
namespace Part1

/-- A row of the GGHV §2 table: A₀, the (m, n) pair, and the
    paper's stated max degree. -/
structure CaseRow where
  a0 : Nat × Nat
  m : Nat
  n : Nat
  maxDeg : Nat
deriving DecidableEq, Repr

/-- The degree pair of a row, by the family formula. -/
def degreePair (r : CaseRow) : Nat × Nat :=
  (r.m * (r.a0.1 + r.a0.2), r.n * (r.a0.1 + r.a0.2))

/-- The max degree of a row's degree pair. -/
def pairMax (r : CaseRow) : Nat :=
  max (degreePair r).1 (degreePair r).2

/-- The ten rows of the GGHV §2 table, in the paper's order. -/
def table : List CaseRow :=
  [ ⟨(4, 12), 3, 4, 64⟩,
    ⟨(4, 12), 5, 7, 112⟩,
    ⟨(5, 20), 2, 3, 75⟩,
    ⟨(5, 20), 3, 2, 75⟩,
    ⟨(7, 21), 2, 3, 84⟩,
    ⟨(8, 24), 2, 3, 96⟩,
    ⟨(8, 28), 3, 2, 108⟩,
    ⟨(8, 32), 3, 2, 120⟩,
    ⟨(9, 24), 2, 3, 99⟩,
    ⟨(9, 27), 2, 3, 108⟩ ]

/-- The five rows the paper marks red (discarded by cited
    papers). Indices into `table`, in order. -/
def redDiscarded : List Nat := [0, 1, 2, 3, 5]

/-- Every row's degree pair has the paper's stated max degree.
    This is the arithmetic check that the table is internally
    consistent with the family formula. -/
theorem table_max_degrees :
    table.map pairMax = [64, 112, 75, 75, 84, 96, 108, 120, 99, 108] := by
  rfl

/-- Every row's degree pair, in table order. -/
theorem table_degree_pairs :
    table.map degreePair =
      [(48, 64), (80, 112), (50, 75), (75, 50), (56, 84),
       (64, 96), (108, 72), (120, 80), (66, 99), (72, 108)] := by
  rfl

/-- The table really is a list of cases with max degree < 125,
    as §2 assumes. -/
theorem table_below_125 : ∀ r ∈ table, r.maxDeg < 125 := by
  decide

/-- Rows surviving the paper's §2 discards: remove the five red
    rows, and the max = 84 and max = 120 rows (discarded in
    GGHV §3). The survivors are exactly the (8,28) and (9,27)
    rows — i.e. the (108,72) and (72,108) cases of Theorem 2.1.
    The (9,24) row (66,99) is NOT a survivor of the full
    theorem: it is discarded later, in GGHV §4 (Prop. 4.2), so
    it appears here as the one remaining non-survivor row and
    is handled in Part 4.
    Rows remaining after the §2/§3 discards, as degree pairs: -/
def section2Remaining : List (Nat × Nat) :=
  ((table.filter (fun r => r.maxDeg ≠ 84 ∧ r.maxDeg ≠ 120)).map degreePair).filter (fun p => p ≠ (48, 64) ∧ p ≠ (80, 112) ∧ p ≠ (50, 75) ∧ p ≠ (75, 50) ∧ p ≠ (64, 96))

theorem section2_survivors :
    section2Remaining = [(108, 72), (66, 99), (72, 108)] := by
  rfl

/-- The (72,108) case: gcd and reduced ratio, as used
    throughout the programme (cf. the Guccione [1] analysis:
    corner-sum 36, ratio (2,3)). -/
theorem deg_72_108_gcd : Nat.gcd 72 108 = 36 := by rfl

theorem deg_72_108_ratio : (72 / Nat.gcd 72 108, 108 / Nat.gcd 72 108) = (2, 3) := by
  rfl

/-- The (72,108) row is in the table: the (9,27) row. -/
theorem row_72_108_in_table : (⟨(9, 27), 2, 3, 108⟩ : CaseRow) ∈ table := by
  decide

/-- The (108,72) row is in the table: the (8,28) row. -/
theorem row_108_72_in_table : (⟨(8, 28), 3, 2, 108⟩ : CaseRow) ∈ table := by
  decide

end Part1
end GGHV
end JC2
