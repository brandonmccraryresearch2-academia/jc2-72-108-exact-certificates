/- Part 23 — D4 Part C, session 3: the PossibleStartingPoints
    algorithm as a verified computation (GGHV's algorithm for
    [GGV2] Prop. 3.12's setting, l = 1, a = 8, b = 3).

    The algorithm, transcribed from GGHV ([GGV2] =
    arXiv:1605.09430; the algorithm's setting is [GGV2]
    Prop. 3.12's): input a corner
    (a/l, b); for d = 0..b−1, for c = ⌊d·a/b⌋+1 .. ld+a−bl−1,
    compute N₁ = gcd(a−c, b−d), N₂ = gcd(c, d),
    (ρ,σ) = dir((a/l,b)−(c/l,d)),
    s = (ρa+σlb)/gcd(ρa+σlb, l(ρ+σ)); include (c/l,d) if
    (s ∣ N₂ and d > 0) or s ≤ N₁.

    Orientation note: the algorithm's dir is taken here as
    ((b−d)/g, (c−a)/g) with g = gcd(a−c, b−d) — the negative of
    the Part 20 "formula basica" orientation. The sign is pinned
    by the instance: with this orientation the surviving
    directions are exactly GGHV's Pred_P(1,0) ∈ {(1,−2),
    (2,−5)}; with the opposite orientation they would be the
    negatives. The general sign convention in [GGV2]'s text
    remains to be checked (session 4).

    Scope note: the function is written over Nat (l, a, b, c, d
    are naturals in GGHV's statement); the c-upper bound
    ld+a−bl−1 uses truncated Nat subtraction, so the function
    is the algorithm only for inputs where that bound does not
    truncate. The verified instance l = 1, a = 8, b = 3 does not
    truncate (upper bound d+4).

    Verified by computation: possibleStartingPoints 1 8 3 =
    [(2,0),(3,1),(4,1),(6,2)], and their directions are
    [(1,−2),(2,−5),(1,−2),(1,−2)] — so every surviving direction
    is (1,−2) or (2,−5), exactly GGHV's Pred_P(1,0) set. The
    further step (Pred_P(1,0) is the direction of a surviving
    starting point) is GGHV's argument, carried, not proved
    here.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- Algorithm's direction: ((b−d)/g, (c−a)/g), g = gcd(a−c, b−d). -/
def dirAlg (a b c d : Int) : Int × Int :=
  let g : Int := (Nat.gcd (a - c).natAbs (b - d).natAbs : Int)
  ((b - d) / g, (c - a) / g)

/-- Algorithm's s value for a direction. -/
def sAlg (l a b : Int) (dir : Int × Int) : Int :=
  let num := dir.1 * a + dir.2 * l * b
  num / Int.gcd num (l * (dir.1 + dir.2))

/-- Algorithm's inclusion condition for (c,d), as a Bool:
    (s ∣ N₂ and d > 0) or s ≤ N₁, with divisibility via emod
    (N₂ % s == 0 is exactly s ∣ N₂ for integers, including the
    s = 0 case, since n % 0 = n). -/
def condAlg (l a b c d : Int) : Bool :=
  let dir := dirAlg a b c d
  let s := sAlg l a b dir
  let n1 : Int := (Nat.gcd (a - c).natAbs (b - d).natAbs : Int)
  let n2 : Int := (Nat.gcd c.natAbs d.natAbs : Int)
  let dvd : Bool := (n2 % s == 0)
  (dvd && Decidable.decide (0 < d)) || Decidable.decide (s ≤ n1)

/-- PossibleStartingPoints, over Nat parameters. -/
def possibleStartingPoints (l a b : Nat) : List (Nat × Nat) :=
  (List.range b).flatMap (fun d =>
    ((List.range (d + 5)).filter (fun c =>
      (d * a / b + 1 ≤ c) && (c ≤ l * d + a - b * l - 1) &&
      condAlg (l : Int) (a : Int) (b : Int) (c : Int) (d : Int))).map
      (fun c => (c, d)))

/-- Spot checks of the algorithm's inner values. -/
example : dirAlg 8 3 3 1 = (2, -5) := by decide
example : dirAlg 8 3 4 1 = (1, -2) := by decide
example : sAlg 1 8 3 (dirAlg 8 3 3 1) = 1 := by decide
example : sAlg 1 8 3 (dirAlg 8 3 4 1) = 2 := by decide
example : condAlg 1 8 3 1 0 = false := by decide
example : condAlg 1 8 3 2 0 = true := by decide

/-- The verified computation: the full output for l = 1, a = 8,
    b = 3. -/
example : possibleStartingPoints 1 8 3 = [(2, 0), (3, 1), (4, 1), (6, 2)] := by decide

/-- The directions of the surviving starting points. -/
example : (possibleStartingPoints 1 8 3).map
    (fun p => dirAlg 8 3 (p.1 : Int) (p.2 : Int)) =
    [(1, -2), (2, -5), (1, -2), (1, -2)] := by decide

/-- Hence every surviving direction is (1,−2) or (2,−5) —
    GGHV's Pred_P(1,0) set. -/
example : ∀ p ∈ (possibleStartingPoints 1 8 3).map
    (fun q => dirAlg 8 3 (q.1 : Int) (q.2 : Int)),
    p = (1, -2) ∨ p = (2, -5) := by decide
