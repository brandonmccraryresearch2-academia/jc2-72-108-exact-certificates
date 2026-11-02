/- Part 29 — D4 Part E, session 2: the [GGV5] PLLC/PFL
    algorithm's first stage (arXiv:1708.07936), as a verified
    computation.

    The algorithm (1708.07936, PLLC stage): generate all
    possible last lower corners (a,b) with a ≤ x_max, using an
    auxiliary list PFL. The first-stage filter for a candidate
    (a,b) is the conjunction of the cited necessary conditions
    from Parts 21/24: b < a, b ≤ (a−b−1)² (Prop. 3.25 =
    "cota"), and b + gcd(a,b) ≠ a (Prop. 3.29 = "casos
    imposibles"). The direction assigned to a surviving
    candidate is: b = 0 → (0,−1); a > 2b > 0 → (1,−2);
    otherwise (1,−1).

    Checked below, for x_max = 9: the candidate list contains
    (8,3) (necessary conditions pass) but not (8,4) (fails
    3.29: 4 + gcd(8,4) = 8); the direction of (8,3) is (1,−2)
    (since 8 > 6 > 0), matching Prop. 4.2's setting, and the
    direction of (8,4) would be (1,−1). The full PLLC
    generation (the PFL loop over earlier pairs) and the
    completeness claim (every possible last lower corner
    appears) are [GGV5]'s, carried, not proved here — this
    session formalizes the filter and direction assignment,
    which is what the later sessions build on.

    Note on Nat subtraction: a−b−1 is truncated, but the
    filter requires b < a, and for b ≤ a−1 the bound
    a−b−1 is exact; the (8,4) exclusion does not depend on
    it (it fails on the gcd condition alone).

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- The first-stage necessary-conditions filter. -/
def pllcFilter (a b : Nat) : Bool :=
  (b < a) && (b ≤ (a - b - 1)^2) && (b + Nat.gcd a b != a)

/-- The algorithm's direction assignment. -/
def pllcDir (a b : Nat) : Int × Int :=
  if b = 0 then (0, -1)
  else if a > 2 * b then (1, -2)
  else (1, -1)

/-- Candidates with a ≤ x_max, in (a, b) order. -/
def pllcCandidates (xMax : Nat) : List (Nat × Nat) :=
  (List.range (xMax + 1)).flatMap (fun a =>
    (List.range (a + 1)).filter (fun b => pllcFilter a b)
      |>.map (fun b => (a, b)))

/-- (8,3) passes the filter; (8,4) fails it (on 3.29). -/
example : pllcFilter 8 3 = true := by decide
example : pllcFilter 8 4 = false := by decide

/-- Directions: (8,3) → (1,−2); (8,4) → (1,−1). -/
example : pllcDir 8 3 = (1, -2) := by decide
example : pllcDir 8 4 = (1, -1) := by decide

/-- The candidate list up to x_max = 9 contains (8,3) but
    not (8,4). -/
example : (8, 3) ∈ pllcCandidates 9 := by decide
example : (8, 4) ∉ pllcCandidates 9 := by decide
