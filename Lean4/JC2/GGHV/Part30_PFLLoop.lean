/- Part 30 — D4 Part E, session 3: the [GGV5] PFL loop stage
    (arXiv:1708.07936), as a verified computation.

    The algorithm's second stage (from the 1708.07936 excerpt):
    for a candidate (a,b) whose assigned direction is (1,−1),
    loop over the earlier PFL pairs ((r,s),(ρ,σ)_{r,s}) with
    r < a, s < b, and r−s < a−b. This session formalizes that
    loop condition over the first-stage PFL: the list of
    ((a,b), dir) pairs for candidates passing Part 29's filter
    (up to x_max), and the earlier-pairs filter.

    Checked below, for x_max = 9: the PFL contains
    ((8,3),(1,−2)) (Prop. 4.2's setting) and ((7,4),(1,−1));
    the earlier pairs for (7,4) include (3,1) (3 < 7, 1 < 4,
    3−1 = 2 < 3) and exclude (8,3) (8 < 7 fails). The
    algorithm's use of the loop (generating further PLLC
    entries from the earlier pairs) and its completeness are
    [GGV5]'s, carried, not proved here.

    Note on Nat subtraction: r−s and a−b are truncated, but
    the filter's r < a and s < b do not by themselves make
    them exact; the (3,1)/(7,4) instance has exact
    differences (3−1 = 2, 7−4 = 3), and the exclusion of
    (8,3) does not depend on subtraction at all.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- First-stage filter (Part 29) and direction assignment. -/
def pllcFilter (a b : Nat) : Bool :=
  (b < a) && (b ≤ (a - b - 1)^2) && (b + Nat.gcd a b != a)

def pllcDir (a b : Nat) : Int × Int :=
  if b = 0 then (0, -1)
  else if a > 2 * b then (1, -2)
  else (1, -1)

/-- The first-stage PFL: ((a,b), dir) pairs, a ≤ x_max. -/
def pfl (xMax : Nat) : List ((Nat × Nat) × (Int × Int)) :=
  (List.range (xMax + 1)).flatMap (fun a =>
    (List.range (a + 1)).filter (fun b => pllcFilter a b)
      |>.map (fun b => ((a, b), pllcDir a b)))

/-- Earlier PFL pairs for a candidate (a,b): r < a, s < b,
    r−s < a−b. -/
def earlierPairs (p : List ((Nat × Nat) × (Int × Int)))
    (a b : Nat) : List ((Nat × Nat) × (Int × Int)) :=
  p.filter (fun ((r, s), _) => (r < a) && (s < b) && (r - s < a - b))

/-- The PFL up to 9 contains ((8,3),(1,−2)) and
    ((7,4),(1,−1)). -/
example : ((8, 3), (1, -2)) ∈ pfl 9 := by decide
example : ((7, 4), (1, -1)) ∈ pfl 9 := by decide

/-- Earlier pairs for (7,4): (3,1) is in, (8,3) is out. -/
example : ((3, 1), (1, -2)) ∈ earlierPairs (pfl 9) 7 4 := by decide
example : ((8, 3), (1, -2)) ∉ earlierPairs (pfl 9) 7 4 := by decide
