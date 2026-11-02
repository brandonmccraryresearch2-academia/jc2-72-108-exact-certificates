/-
  JC2 / GGHV formalization — Part 6: Directions, valuation
  arithmetic (D1, first layer).

  Source: Guccione, Guccione, Horruitiner, Valqui,
  arXiv:2204.14178v1, §§3–4. TeX source:
  ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.

  STATUS (2026-10-30): core Lean only, no Mathlib, no sorry,
  no axiom declarations. What IS proved here (kernel-checked,
  all by `decide` on concrete integers):
  - The weighted valuation v_{ρ,σ}(a,b) = ρ·a + σ·b, and
    its values at the paper's stated points.
  - The §3-120 direction equality: v_{4,−1} takes the same
    value 4 on A₁ = (8,28) and on A₂ = (11/4,7) (the latter
    in scaled form, since 11/4 is not an integer pair:
    4·(4·8 − 28) = 4·11 + (−1)·7·4 = 16).
  - Edge-valuation equalities: two vertices lie on the same
    (ρ,σ)-edge exactly when their valuations agree. Proved
    for the paper's edges: (−3,8) on (42,16)/(2,1) in §4.1
    (both 2); (−1,4) on (28,8)/(24,7) in §4.3 (both 4);
    (1,0) on (6,16)/(6,18) and on (9,24)/(9,27) in §5
    (both 6, resp. both 9); (3,−1) on (6,16) with value 2
    and (−1,1) on (6,18) with value 12, as stated in §5.
  - Coprimality of the paper's directions (as Nat gcds).
  What is NOT proved here, and is NOT claimed:
  - The full Directions theory: en/st as endpoints of the
    maximal-valuation segment of a polygon, Pred/Succ,
    (ρ,σ)-homogeneous parts ℓ_{ρ,σ}, and the theorems
    [GGV1] Cor. 7.4 / Prop. 8.2, [GGV2] Prop. 3.12,
    [GGV6] Prop. 2.5 that use them. Those remain INTERFACE
    (D1, second layer). In particular, this file does NOT
    prove that en/st of any polygon are the vertices named
    in §§4–5; it proves only the valuation arithmetic that
    those claims rest on, at the paper's stated points.
  - The §3-84 valuations en_{7,−2}(F) = (5,15) and the
    ℓ_{7,−2} factorisation: those need the homogeneous-part
    machinery, not just valuations of points.
-/

namespace JC2
namespace GGHV
namespace Part6

/-- Weighted valuation of an exponent pair. -/
def dirVal (ρ σ : Int) (a b : Int) : Int := ρ * a + σ * b

/-- §3-120: v_{4,−1}(8,28) = 4. -/
theorem val_120_a1 : dirVal 4 (-1) 8 28 = 4 := by decide

/-- §3-120: v_{4,−1}(11/4, 7) = 4, in scaled form:
    multiply by 4 to clear the denominator: both sides 16. -/
theorem val_120_a2_scaled :
    4 * dirVal 4 (-1) 8 28 = 4 * 11 + (-1) * 7 * 4 := by decide

/-- §3-120 direction equality, from the two values above. -/
theorem val_120_equal : dirVal 4 (-1) 8 28 = 4 ∧
    4 * 11 + (-1) * 7 * 4 = 16 := by
  constructor <;> decide

/-- §4.1: under direction (−3,8), st = (42,16) and
    en = (2,1) have the same valuation 2, i.e. they lie
    on the same (−3,8)-edge, as the proof states. -/
theorem val_41_edge : dirVal (-3) 8 42 16 = 2 ∧ dirVal (-3) 8 2 1 = 2 := by
  constructor <;> decide

/-- §4.3: under direction (−1,4), the edge endpoints
    (28,8) and (24,7) have the same valuation 4. -/
theorem val_43_edge : dirVal (-1) 4 28 8 = 4 ∧ dirVal (-1) 4 24 7 = 4 := by
  constructor <;> decide

/-- §5: under direction (1,0), the P-edge (6,16)/(6,18)
    has valuation 6, and the Q-edge (9,24)/(9,27) has
    valuation 9. -/
theorem val_5_vertical : dirVal 1 0 6 16 = 6 ∧ dirVal 1 0 6 18 = 6 ∧
    dirVal 1 0 9 24 = 9 ∧ dirVal 1 0 9 27 = 9 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- §5 stated values: en_{3,−1}(P) = (6,16) has
    v_{3,−1} = 2; st_{−1,1}(P) = (6,18) has v_{−1,1} = 12. -/
theorem val_5_en_st : dirVal 3 (-1) 6 16 = 2 ∧ dirVal (-1) 1 6 18 = 12 := by
  constructor <;> decide

/-- Coprimality of the paper's directions, as Nat gcds
    of absolute values: (4,1), (7,2), (3,1), (1,0),
    (3,8), (1,1), (1,3), (1,4). -/
theorem directions_coprime :
    Nat.gcd 4 1 = 1 ∧ Nat.gcd 7 2 = 1 ∧ Nat.gcd 3 1 = 1 ∧
    Nat.gcd 1 0 = 1 ∧ Nat.gcd 3 8 = 1 ∧ Nat.gcd 1 1 = 1 ∧
    Nat.gcd 1 3 = 1 ∧ Nat.gcd 1 4 = 1 := by
  decide

end Part6
end GGHV
end JC2
