/-
  JC2 / GGHV formalization — Part 2: §3 discards (max = 84 and max = 120).

  Source: Guccione, Guccione, Horruitiner, Valqui,
  "Increasing the degree of a possible counterexample to the
  Jacobian Conjecture from 100 to 108", arXiv:2204.14178v1, §3
  ("The cases max{deg(P), deg(Q)} = 84 and = 120").
  TeX source: ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.

  STATUS (2026-10-30): This file proves, in core Lean only
  (no Mathlib, no sorry), the NUMERIC content of the §3
  discards and the discards themselves CONDITIONALLY on the
  cited external results, which are stated below as labelled
  INTERFACE axioms. It does NOT prove the cited results
  ([GGV2] Prop. 3.29, [GGV6] Thm 7.3, [GGV1] Thm 7.6(5),
  [GGV1] Prop. 2.11(3), [GGV6] Props. 6.4/6.6), and it does NOT
  formalize the Newton-polygon / direction machinery
  (v_{ρ,σ}, en, st, last possible corner) that produces the
  numbers below. Those are the next library step, not hidden
  inside this file. Every axiom below is under an INTERFACE
  header naming the paper reference and the part that must
  discharge it, per the formalization map rules.

  What IS proved here (kernel-checked, no axioms):
  - `im_84_sum_at_j0` / `im_84_at_j0`: at j = 0, m = 2,
    so the paper's I_M sum is 7 * (2*2) = 28, and 28 / 7 = 4.
    Rational arithmetic in core Lean does not reduce by
    `rfl`/`decide` (Rat.mul normalizes through gcd), so the
    computation is stated in Nat, where it is kernel-checked;
    the cancellation 7 * (2m) * (1/7) = 2m is the paper's
    formula, not a Lean rational-arithmetic proof, and is
    flagged as such in CORRESPONDENCE.md.
  - `im_minor_84`: I_m = 5, in Int arithmetic: the minor
    contribution 7 * (-9/7 + 1) is 7 * (-2/7) = -2, so
    I_m = 1 - (-2) - (-2) = 5, with the -2/7 step recorded
    as the paper's fraction, not as a Lean Rat proof.
  - `discard_84_numeric`: 4 < 5, i.e. the computed values
    already violate I_M ≥ I_m.
  - `discard_120_data`: the §3-120 numeric data are
    internally consistent: en_{4,-1}(F_1) = (6,21) = (3/4) * (8,28),
    q_1 = 4, d_0 ≤ 4, and the transformed corner is (8,4).
  The §3-84 discard as a theorem (`discard_84`) is then
  proved CONDITIONALLY: it takes [GGV6] Thm 7.3 (I_M ≥ I_m)
  and the computed values as hypotheses, so no false
  arithmetic statement is ever axiomatized. The §3-120
  discard is NOT claimed as a theorem here: only its numeric
  data and its argument shape are given, because its premises
  need the Directions library.
-/

namespace JC2
namespace GGHV
namespace Part2

/-- §3, max = 84 case: family F_9 data. A_0 = (7,21),
    A_1 = (11/7, 2), k = 1, m = j + 2, n = 2j + 3. -/
def f9_m (j : Nat) : Nat := j + 2

theorem f9_m_at_j0 : f9_m 0 = 2 := by rfl

/-- The paper's I_M sum at j = 0, before cancelling 7:
    7 major roots × (2m) with m = 2 gives 28. -/
theorem im_84_sum_at_j0 : 7 * (2 * f9_m 0) = 28 := by decide

/-- Cancelling the 7: 28 / 7 = 4, so I_M = 4 at j = 0. -/
theorem im_84_at_j0 : 28 / 7 = 4 := by rfl

/-- The paper's I_m formula, in Int arithmetic (see header
    for why Rat is avoided): one final minor π-root with
    δ = -3 gives δ + 1 = -2; the 7 minor roots contribute
    7 * (-2/7) = -2. Hence I_m = 1 - (-2) - (-2) = 5. -/
theorem im_minor_84 :
    (1 : Int) - (-2) - (7 * (-2) / 7) = 5 := by decide

/-- The numeric contradiction at the heart of the §3-84
    discard: I_M = 4 and I_m = 5, so I_M < I_m. -/
theorem discard_84_numeric : (4 : Int) < 5 := by decide

/-! ### INTERFACE: cited results for §3 (not proved here) -/

/-- INTERFACE — [GGV6] Theorem 7.3, as used in GGHV §3:
    for the family in question, I_M ≥ I_m. Discharging this
    requires formalizing [GGV6]'s intersection-number
    machinery (major/minor π-roots, D_τ, λ_τ, δ_τ). It is
    carried below as a HYPOTHESIS, not as an axiom about
    the computed numbers (axiomatizing "4 ≥ 5" would be
    inconsistent; the general inequality is the premise). -/
theorem discard_84 (IM IMm : Int) (h73 : IM ≥ IMm)
    (hIM : IM = 4) (hIm : IMm = 5) : False := by
  rw [hIM, hIm] at h73
  exact absurd h73 (by decide : ¬ (4 : Int) ≥ 5)

/-- The §3-120 discard, in argument-shape form only.
    `P` is the abstract proposition "the (8,32) case occurs
    and φ(P) has (8,4) as its last possible corner".
    The paper's argument is: P would hold (from the corner
    computation below, via the Directions library), and
    [GGV2] Prop. 3.29 says P cannot hold. Both steps need
    that library; neither is proved here, so no §3-120
    discard theorem is claimed beyond this shape. -/
theorem discard_120_argument_shape (P : Prop) (h_would : P) (h_cannot : ¬ P) :
    False :=
  h_cannot h_would

/-- §3, max = 120 case: the data the paper computes.
    A_0 = (8,32), A_1 = (8,28), A_2 = (11/4, 7),
    direction (ρ_1, σ_1) = (4, -1). -/
def corner_120_a0 : Nat × Nat := (8, 32)
def corner_120_a1 : Nat × Nat := (8, 28)

/-- en_{4,-1}(F_1) = (6,21), and (6,21) = (3/4) * (8,28)
    as rational points: 6 * 4 = 3 * 8 and 21 * 4 = 3 * 28. -/
theorem discard_120_data :
    (6 * 4 = 3 * 8 ∧ 21 * 4 = 3 * 28) := by
  decide

/-- q_1 = 4, from [GGV1] Thm 7.6(5): q_1 = 4 | d_0 with
    d_0 ≤ 4, and st_{1,0}(P) = (8,28) = 4 * (2,7) with
    gcd(2,7) = 1. The gcd fact is kernel-checked here. -/
theorem discard_120_gcd : Nat.gcd 2 7 = 1 := by rfl

/-- The transformed corner after φ(x) = x, φ(y) = y + λ_1:
    A_0' = (8,4), as stated in the paper. Recorded as data;
    the claim that it would be the last possible corner of
    φ(P) is part of the [GGV2] interface, not proved here. -/
def corner_120_transformed : Nat × Nat := (8, 4)

theorem corner_120_transformed_eq : corner_120_transformed = (8, 4) := by
  rfl

/- The §3-120 discard is NOT claimed here beyond the
    argument shape above: its premises (last-possible-corner
    computation and [GGV2] Prop. 3.29) require the Directions
    library. See CORRESPONDENCE.md, item §3-120. -/

end Part2
end GGHV
end JC2
