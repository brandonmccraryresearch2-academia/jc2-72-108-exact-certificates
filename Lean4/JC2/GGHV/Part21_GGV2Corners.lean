/- Part 21 — D4 Part C, session 1: [GGV2] corner theory,
    instance layer.

    Identification (CORRECTED in Part 24): [GGV2] IS
    arXiv:1605.09430, "The Two-Dimensional Jacobian Conjecture
    and the Lower Side of the Newton Polygon" — it IS among the
    six TeX sources. The original header's claim that [GGV2] is
    J. Algebra 471 (2017) was wrong: that journal paper is
    [GGV1]. The conditions below were formalized as cited in
    GGHV/1708.07936 and are checked against [GGV2]'s own TeX
    in Part 24.

    Contents:

    - The two cited necessary conditions for a possible last
      lower corner (a,b) with b < a: Prop. 3.25, b ≤ (a−b−1)²,
      and Prop. 3.29, b + gcd(a,b) ≠ a. Their conjunction is
      recorded as `PossibleLastCorner` — explicitly NOT the
      definition (Def. 3.21), which is carried as future work.
    - The §3-120-adjacent instance: (8,4) passes 3.25 but fails
      3.29 (4 + gcd(8,4) = 8 = a), so it is not a possible last
      lower corner — this is the step in GGHV's discarding of
      (8,32) ("(8,4) is not a last possible corner").
    - A passing instance: (8,3) satisfies both conditions
      (necessary, not sufficient).
    - The §3-120 direction computation: (ρ₁,σ₁) = (4,−1) from
      A₁ = (8,28), A₂ = (11/4,7) — the integer check is
      dirVal (4,−1) (8,28) = 4, and clearing A₂'s denominator,
      4·11 − 4·7 = 16 = 4·4.
    - The §3-120 scaling en_{4,−1}(F₁) = (3/4)(8,28) = (6,21),
      checked as 4·(6,21) = 3·(8,28).
    - The Prop. 4.2 algorithm setting, carried as data (the
      algorithm itself — PossibleStartingPoints, l = 1, a = 8,
      b = 3 — is to be formalized as a verified computation in
      sessions 2–4, not transcribed): Pred_P(1,0) ∈ {(1,−2),
      (2,−5)}; the (2,−5) branch is excluded in GGHV by
      st_{2,−5}(P) = 3m(3,1) and Pred_P(2,−5) ≤ (1,−3) forcing
      deg_x(P(x,0)) ≤ 0 (vdE Prop. 10.2.6); the surviving branch
      has st_{1,−2}(R) ∈ {(2,0),(4,1)}.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- Weighted valuation (restated from Part 17). -/
def dirVal (ρ σ : Int) (a b : Int) : Int := ρ * a + σ * b

/-- Conjunction of the two cited necessary conditions for a
    possible last lower corner (a,b), b < a: [GGV2] Prop. 3.25
    and Prop. 3.29, as cited in 1605.09430/1708.07936. This is
    NOT Def. 3.21 (the definition itself), only its cited
    necessary consequences. -/
def PossibleLastCorner (a b : Nat) : Prop :=
  b < a ∧ b ≤ (a - b - 1) ^ 2 ∧ b + Nat.gcd a b ≠ a

/-- (8,4) is not a possible last lower corner: it passes 3.25
    (4 ≤ 9) but fails 3.29, since 4 + gcd(8,4) = 8 = a. -/
example : ¬ PossibleLastCorner 8 4 := by
  show ¬ (4 < 8 ∧ 4 ≤ (8 - 4 - 1) ^ 2 ∧ 4 + Nat.gcd 8 4 ≠ 8)
  decide

/-- (8,3) passes both cited necessary conditions (necessary
    only — passing does not make it a last lower corner). -/
example : PossibleLastCorner 8 3 := by
  show 3 < 8 ∧ 3 ≤ (8 - 3 - 1) ^ 2 ∧ 3 + Nat.gcd 8 3 ≠ 8
  decide

/-- §3-120: the direction (4,−1) gives valuation 4 on A₁ = (8,28). -/
example : dirVal 4 (-1) 8 28 = 4 := by decide

/-- §3-120: A₂ = (11/4,7) lies on the same (4,−1)-line at level 4,
    with the denominator cleared: 4·11 − 4·7 = 16 = 4·4. -/
example : 4 * 11 - 4 * 7 = 4 * dirVal 4 (-1) 8 28 := by decide

/-- §3-120: en_{4,−1}(F₁) = (6,21) = (3/4)(8,28), cleared of
    denominators. -/
example : 4 * 6 = 3 * 8 ∧ 4 * 21 = 3 * 28 := by decide

/-- Prop. 4.2 algorithm setting, carried as data: l = 1, a = 8,
    b = 3, and the algorithm's output for Pred_P(1,0). The
    algorithm itself is future work (sessions 2–4). -/
structure Prop42Setting where
  l : Nat
  a : Nat
  b : Nat
  pred : Int × Int
  hpred : pred = (1, -2) ∨ pred = (2, -5)

def prop42_setting : Prop42Setting where
  l := 1
  a := 8
  b := 3
  pred := (1, -2)
  hpred := Or.inl rfl

/-- The excluded Prop. 4.2 branch's data: st_{2,−5}(P) = 3m(3,1),
    which for the (m,n) = (2,3) pair is (18,6). -/
example : 3 * 2 * 3 = 18 ∧ 3 * 2 * 1 = 6 := by decide
