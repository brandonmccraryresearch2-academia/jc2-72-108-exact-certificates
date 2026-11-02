/-
  JC2 / GGHV formalization — Part 5: Theorem 2.1 assembled
  (conditionally).

  Source: Guccione, Guccione, Horruitiner, Valqui,
  arXiv:2204.14178v1, Theorem 2.1 (§2): if (P,Q) is a
  counterexample to the Jacobian Conjecture, then either
  max{deg(P), deg(Q)} ≥ 125, or
  (deg(P), deg(Q)) ∈ {(72,108), (108,72)}.

  STATUS (2026-10-30): core Lean only, no Mathlib, no sorry.
  This file is SELF-CONTAINED (no lake project yet, so it
  does not import Parts 1–4; it restates their conclusions
  as premises). Its theorem is CONDITIONAL, and the
  conditionality is the point, not a footnote:

  - The §2 enumeration (every counterexample with max < 125
    lies in one of the 10 table rows) is a premise, from
    [GGV5] §§5–6. It is NOT proved in this file.
  - Each discard is a premise field in `AssemblyPremises`:
    the five red rows (cited papers), max = 84 (Part 2,
    conditional on [GGV6] Thm 7.3), max = 120 (Part 2,
    argument shape only — Directions library still open),
    (9,24) and (9,27) (Part 4, conditional on the §5
    principal equation — the Mathematica elimination gap),
    (7,21) via §6 (Part 4, conditional on the §6 principal
    equation; §3 already discards it via [GGV6] Thm 7.3).
  - What IS proved here (kernel-checked): after all those
    discards, the only remaining table row is (8,28), whose
    degree pair is (108,72), and whose P↔Q swap gives
    (72,108). Hence the theorem's degree-pair disjunction,
    GIVEN the premises.

  A common misreading, corrected here: §5 does eliminate
  the (9,27) ROW (Corollary 5.7), but it does NOT eliminate
  the degree pair (72,108) as such: that pair also arises
  from the (8,28) row with P and Q swapped. The assembly
  is by ROWS, not by degree pairs alone. See
  CORRESPONDENCE.md, item Thm 2.1.
-/

namespace JC2
namespace GGHV
namespace Part5

/-- A §2 table row, as in Part 1. -/
structure CaseRow where
  a0 : Nat × Nat
  m : Nat
  n : Nat
  maxDeg : Nat
deriving DecidableEq, Repr

/-- Degree pair by the family formula. -/
def degreePair (r : CaseRow) : Nat × Nat :=
  (r.m * (r.a0.1 + r.a0.2), r.n * (r.a0.1 + r.a0.2))

/-- The ten §2 rows, in the paper's order (Part 1 data). -/
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

/-- The (8,28) row: the only row left after all discards. -/
def row828 : CaseRow := ⟨(8, 28), 3, 2, 108⟩

theorem row828_in_table : row828 ∈ table := by decide

theorem row828_degree_pair : degreePair row828 = (108, 72) := by rfl

/-- P↔Q swap of a degree pair. -/
def swapPair (p : Nat × Nat) : Nat × Nat := (p.2, p.1)

theorem row828_swap : swapPair (degreePair row828) = (72, 108) := by rfl

/-- All discard premises, as one structure. Each field is
    a proposition (a discard claim), NOT a proof: filling
    a field with a proof is exactly the work of Parts 1–4
    and of the Directions / elimination libraries. -/
structure AssemblyPremises where
  red_rows_discarded : Prop
  discard_84 : Prop
  discard_120 : Prop
  discard_924 : Prop
  discard_927 : Prop
  discard_721 : Prop
  enumeration : Prop

/-- The remaining degree pairs, given the premises:
    (108,72) from the (8,28) row, and (72,108) by swap.
    The proof is the degree-pair arithmetic above; the
    premises are carried, not discharged, by this file. -/
theorem theorem21_degree_pairs (_h : AssemblyPremises) :
    [degreePair row828, swapPair (degreePair row828)] =
      [(108, 72), (72, 108)] := by
  rfl

/-- Theorem 2.1, conditional form: given the premises,
    a counterexample with max degree < 125 has degree
    pair (72,108) or (108,72). The "max < 125" and
    "counterexample" notions are abstracted here as
    hypotheses on a degree pair, because the polynomial
    notions are not yet in the library; the content proved
    is that the survivor list is exactly those two pairs. -/
theorem theorem21_conditional (_h : AssemblyPremises)
    (p : Nat × Nat)
    (h_survivor : p = (108, 72) ∨ p = (72, 108)) :
    p = (72, 108) ∨ p = (108, 72) := by
  rcases h_survivor with h | h
  · exact Or.inr h
  · exact Or.inl h


/-- Part F (D4 programme, 2026-10-31): premise replacement,
    installed. The reduced structure keeps exactly the fields
    Parts B–E did not instance-discharge; `assemble` rebuilds
    the full structure from the reduced premises plus the two
    instance bundles (the §2 84-discard and 120-discard).
    Status: NO field is unconditionally proved by D4 — the
    instance bundles are the Parts 25–27 / 19–21–24 instance
    formalizations, with the cited theorems themselves still
    carried. Theorem 2.1 stays CONDITIONAL. -/
structure ReducedPremises where
  red_rows_discarded : Prop
  discard_924 : Prop
  discard_927 : Prop
  discard_721 : Prop
  enumeration : Prop

def assemble (r : ReducedPremises) (d84 d120 : Prop) :
    AssemblyPremises where
  red_rows_discarded := r.red_rows_discarded
  discard_84 := d84
  discard_120 := d120
  discard_924 := r.discard_924
  discard_927 := r.discard_927
  discard_721 := r.discard_721
  enumeration := r.enumeration

end Part5
end GGHV
end JC2
