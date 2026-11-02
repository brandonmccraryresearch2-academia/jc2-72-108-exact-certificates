/- Part 24 — D4 Part C, session 4: [GGV2] checked against its own
    text, and the direction-orientation resolution. Part C is
    COMPLETE after this session.

    CORRECTION (applied here and to the Part 21/22/23 headers):
    [GGV2] IS arXiv:1605.09430, "The Two-Dimensional Jacobian
    Conjecture and the Lower Side of the Newton Polygon" — it
    IS among the six TeX sources. The earlier claim that [GGV2]
    is J. Algebra 471 (2017) 13–74 was wrong: that journal paper
    is [GGV1] (arXiv:1401.1784, the shape paper). The substance
    of Parts 21–23 is unaffected (the cited conditions were
    accurate); only the source-identification sentence was
    wrong. GGHV cites [GGV2] by published numbers (3.12, 3.21,
    3.29, 3.31); the arXiv TeX labels results by name, so the
    mapping below is by content.

    Mapping, checked in 1605.09430's TeX:

    - Prop. 3.12 = TeX Proposition "finitas direcciones": for
      [G,R] = R^i with R non-monomial (ρ,σ)-homogeneous, one of
      three cases occurs: (1) ρ ∣ l and r = ξh^j (h linear ≠ z);
      (2) ϑ ≤ N₁, 0 < t' < ℓϑ, (ρ,σ) = −dir(t'·st + ϑ(1,1)),
      with a linear factor of r(z) of multiplicity ϑ; (3)
      ϑ ∣ N₂, same dir formula, ν₂ > 0. Plus: if l = 1 and
      case (1) occurs, then v_{1,−2}(en_{ρ,σ}(R)) > 0. The
      instance data (Part 22) sit in case (2): ϑ = 6 ≤ N₁ = 6,
      while ϑ ∣ N₂ fails (6 ∤ 3), both checked below.
    - Def. 3.21 = TeX Definition "llc": a last lower corner is
      the final point of an admissible chain obtained from a
      standard (m,n)-pair, with m(a,b) the last corner of H(P)
      below the main diagonal. It is distinct from TeX
      Definition "Definicion pllc": a possible last lower
      corner is the final point of any admissible chain. The
      (8,4) instance (Part 22) is a would-be last lower corner
      of φ(P), excluded by Prop. 3.29.
    - Prop. 3.25 = TeX Proposition "cota": a possible last lower
      corner satisfies b < a and b ≤ (a−b−1)² (Part 21's first
      condition, now sourced).
    - Prop. 3.29 = TeX Proposition "casos imposibles": for
      ℘, n' ∈ ℕ with n' ≥ 2, the point ℘(n', n'−1) is not a
      possible last lower corner. The general identity behind
      the cited form is proved below: for such points,
      b + gcd(a,b) = a. The (8,4) instance is ℘ = 4, n' = 2.
    - Remark 3.31: not located as a separate remark in the TeX
      (the TeX's remarks are name-labelled); the pin from
      Part 22 stands as a citation-level pin only: GGHV cites
      Remark 3.31 for the degree-120 discard, whose detailed
      form in GGHV is the §3-120 argument.
    - Admissible-chain endpoint example (TeX Proposition
      "ejemplo" + Remark "condicion para v sub rho sigma1"):
      (a,b) = (k,0) + j(2,1) with k > 0, j > 0 is a possible
      last lower corner; instance (7,3) = (1,0) + 3·(2,1), with
      v_{1,−2}(7,3) = 1 > 0, checked below.

    Orientation resolution: [GGV2]'s dir(r/l,s) is the unique
    (ρ,σ) ∈ V_{>0} with v_{ρ,σ}(r/l,s) = 0, and Prop. 3.12's
    direction is its negative, (ρ,σ) = −dir(...). Part 20's
    formula ((d−b)/g, (a−c)/g) is dir_{GGV2} (it lands in
    V_{>0}: for (8,3)−(3,1) it gives (−2,5), sum 3 > 0);
    Part 23's dirAlg ((b−d)/g, (c−a)/g) is its negative, the
    proposition's (ρ,σ) (for (8,3)−(3,1) it gives (2,−5)).
    The negation identity is proved below in general.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- The shared gcd denominator, kept as its own definition so
    the orientation proof below does not rewrite inside it. -/
def gg (a b c d : Int) : Int :=
  (Nat.gcd (a - c).natAbs (b - d).natAbs : Int)

/-- [GGV2]'s dir: ((d−b)/g, (a−c)/g) (Part 20's formula). -/
def dirGGV2 (a b c d : Int) : Int × Int :=
  ((d - b) / gg a b c d, (a - c) / gg a b c d)

/-- Algorithm's direction (Part 23's dirAlg): the negative of
    dirGGV2, i.e. Prop. 3.12's (ρ,σ). -/
def dirAlg (a b c d : Int) : Int × Int :=
  ((b - d) / gg a b c d, (c - a) / gg a b c d)

/-- Negated division under divisibility (the correction term in
    `Int.neg_ediv` vanishes). -/
theorem neg_ediv_of_dvd {x g : Int} (h : g ∣ x) :
    (-x) / g = -(x / g) := by
  rw [Int.neg_ediv]
  simp [h]

/-- The gcd denominator divides both differences. -/
theorem gg_dvd_sub (a b c d : Int) : gg a b c d ∣ (d - b) := by
  simp only [gg]
  have h : Nat.gcd (a - c).natAbs (b - d).natAbs ∣ (b - d).natAbs :=
    Nat.gcd_dvd_right _ _
  have h2 : ((Nat.gcd (a - c).natAbs (b - d).natAbs : Int)) ∣
      ((b - d).natAbs : Int) := Int.natCast_dvd_natCast.mpr h
  have h3 : ((Nat.gcd (a - c).natAbs (b - d).natAbs : Int)) ∣ (b - d) :=
    Int.dvd_natAbs.mp h2
  obtain ⟨k, hk⟩ := h3
  refine ⟨-k, ?_⟩
  rw [Int.mul_neg]
  have e : d - b = -(b - d) := by omega
  rw [e]
  exact congrArg Neg.neg hk

theorem gg_dvd_sub' (a b c d : Int) : gg a b c d ∣ (a - c) := by
  simp only [gg]
  have h : Nat.gcd (a - c).natAbs (b - d).natAbs ∣ (a - c).natAbs :=
    Nat.gcd_dvd_left _ _
  have h2 : ((Nat.gcd (a - c).natAbs (b - d).natAbs : Int)) ∣
      ((a - c).natAbs : Int) := Int.natCast_dvd_natCast.mpr h
  exact Int.dvd_natAbs.mp h2

/-- The orientation identity, in general. -/
theorem dirAlg_neg_dirGGV2 (a b c d : Int) :
    dirAlg a b c d = (-(dirGGV2 a b c d).1, -(dirGGV2 a b c d).2) := by
  simp only [dirAlg, dirGGV2]
  congr 1
  · rw [show b - d = -(d - b) by omega]
    exact neg_ediv_of_dvd (gg_dvd_sub a b c d)
  · rw [show c - a = -(a - c) by omega]
    exact neg_ediv_of_dvd (gg_dvd_sub' a b c d)

/-- Instance: dirGGV2 for (8,3)−(3,1) is (−2,5) ∈ V_{>0}
    (sum 3 > 0, gcd 1); dirAlg is (2,−5). -/
example : dirGGV2 8 3 3 1 = (-2, 5) := by decide
example : (-2) + 5 = 3 := by decide
example : Int.gcd (-2) 5 = 1 := by decide
example : dirAlg 8 3 3 1 = (2, -5) := by decide

/-- Prop. 3.12 case (2) vs (3) for the (12,3)/(24,9) instance:
    ϑ = 6 ≤ N₁ = 6 holds, ϑ ∣ N₂ fails (6 ∤ 3) — so the
    instance sits in case (2), not case (3). -/
example : 6 ≤ 6 := by decide
example : ¬ (6 ∣ 3) := by decide

/-- Prop. 3.29's general identity: points ℘(n', n'−1) with
    n' ≥ 2 satisfy b + gcd(a,b) = a, hence are excluded. -/
theorem casos_imposibles_identity (p n : Nat) (hn : 2 ≤ n) :
    (p * (n - 1)) + Nat.gcd (p * n) (p * (n - 1)) = p * n := by
  rw [Nat.gcd_mul_left]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h : Nat.gcd (m + 1) m = 1 := by
    have h1 : Nat.gcd (m + 1) m ∣ (m + 1) := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd (m + 1) m ∣ m := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd (m + 1) m ∣ 1 := by
      have h := Nat.dvd_sub h1 h2
      simpa using h
    exact (Nat.dvd_one.mp h3)
  rw [h, Nat.mul_add]

/-- The (8,4) instance: ℘ = 4, n' = 2. -/
example : (4 * (2 - 1)) + Nat.gcd (4 * 2) (4 * (2 - 1)) = 4 * 2 := by decide

/-- Admissible-chain endpoint example: (7,3) = (1,0) + 3·(2,1),
    with v_{1,−2}(7,3) = 1 > 0. -/
example : (1 + 3 * 2, 0 + 3 * 1) = (7, 3) := by decide
example : 1 * 7 + (-2) * 3 = 1 := by decide
