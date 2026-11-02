/- Part 22 — D4 Part C, session 2: [GGV2] Prop. 3.12, Def. 3.21,
    Remark 3.31, as cited in GGHV (and in 1605.09430/1708.07936).
    [GGV2] itself (J. Algebra 471 (2017) 13–74) is not among the
    six TeX sources; nothing here is read from [GGV2] directly.

    Pins:

    - Prop. 3.12(2) instance (GGHV, Prop. 4.2 argument): in the
      last case (c,d) = (12,3), (a,b) = (24,9), with s = ϑ = 6,
      N₁ = 6, N₂ = 3. Checked below: N₁ = gcd(24−12, 9−3) = 6,
      N₂ = gcd(12,3) = 3, the direction dir((24,9)−(12,3)) =
      (1,−2), and s = (24−18)/gcd(6,−1) = 6. The proposition's
      conclusion — a linear factor of R³ with multiplicity
      s = ϑ = 6 — contradicts R having three distinct linear
      factors, eliminating the case; the conclusion itself is
      [GGV2]'s, carried, not proved here.
    - Prop. 3.12 case structure, as cited in 1708.07936: case (1)
      is impossible when a ≤ 2b; θ and t' satisfy the Remark 3.13
      ratio ϑ/t' = −(ρa+σb)/(ρ+σ). For the (12,3)/(24,9)
      instance with (ρ,σ) = (1,−2) the ratio is −(24−18)/(−1) =
      6, consistent with ϑ = 6 (t' = 1). The case exclusion is
      carried as a hypothesis field (project convention for
      cited results), not proved.
    - Def. 3.21 instance (GGHV §3-120): A₀' = (8,4) "would be the
      last possible corner of φ(P)" after the automorphism
      φ(y) = y + λ₁, from ℓ_{1,0}(φ(P)) = (λ_P x²y(y+λ₁)⁷)^{4m}:
      the x²y factor gives 4m·(2,1), i.e. (1/m)·4m·(2,1) =
      (8,4), checked below. It is impossible by Prop. 3.29
      (Part 21: 4 + gcd(8,4) = 8), which discards the case.
    - Remark 3.31: GGHV cites it for discarding max{deg P,
      deg Q} = 120, and says the argument "we will describe in
      detail in the next section" — i.e. the §3-120 discard
      itself (the (8,4)/d₀ = 4 argument of Parts 19/21). So
      Remark 3.31 is pinned as the degree-120 discard, whose
      detailed form in GGHV is the §3-120 argument; its
      [GGV2] text is not independently checked here.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- Prop. 3.12 instance data: (c,d) = (12,3), (a,b) = (24,9). -/
example : Nat.gcd (24 - 12) (9 - 3) = 6 := by decide
example : Nat.gcd 12 3 = 3 := by decide

/-- Direction dir((24,9)−(12,3)) = (1,−2), with the algorithm's
    orientation (see Part 23): ((b−d)/g, (c−a)/g) with
    g = gcd(a−c, b−d) = 6. -/
example : ((9 - 3) / 6, (12 - 24) / 6) = (1, -2) := by decide

/-- s for the instance: (ρa + σlb)/gcd(ρa + σlb, l(ρ+σ)) with
    (ρ,σ) = (1,−2), l = 1: (24−18)/gcd(6,−1) = 6 = ϑ. -/
example : (((1 * 24 + (-2) * 1 * 9) / Int.gcd (1 * 24 + (-2) * 1 * 9) (1 * (1 + (-2)))) : Int) = 6 := by decide

/-- Remark 3.13 ratio for the instance: ϑ/t' = −(ρa+σb)/(ρ+σ)
    = −(24−18)/(−1) = 6, consistent with ϑ = 6, t' = 1. -/
example : (((-(1 * 24 + (-2) * 9)) / (1 + (-2))) : Int) = 6 := by decide

/-- Prop. 3.12 case structure: cases (1), (2), (3), with the
    cited case-(1) exclusion carried as a hypothesis field. -/
inductive Prop312Case where
  | case1
  | case2
  | case3

structure Prop312Theorem where
  a : Nat
  b : Nat
  c : Prop312Case
  hcase1 : a ≤ 2 * b → c ≠ Prop312Case.case1

/-- Def. 3.21 instance: the x²y factor gives 4m·(2,1), i.e.
    (1/m)·4m·(2,1) = (8,4) = A₀'. -/
example : (4 * 2, 4 * 1) = (8, 4) := by decide

/-- The (8,4) exclusion by Prop. 3.29 (Part 21's check, restated):
    4 + gcd(8,4) = 8 = a. -/
example : 4 + Nat.gcd 8 4 = 8 := by decide
