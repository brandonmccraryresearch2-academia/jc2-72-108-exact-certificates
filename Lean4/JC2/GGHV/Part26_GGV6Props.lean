/- Part 26 — D4 Part D, session 2: [GGV6] Props. 6.4/6.6 and
    Ex. 6.7, instance layer ([GGV6] = arXiv:1708.09367, read
    from its TeX; published numbers mapped by content).

    Pins:

    - Prop. 6.6(2) ≈ TeX Proposition "traduccion", item (2):
      for a type-Ib regular corner, |D_τ^P| = m·b,
      |D_τ^Q| = n·b, and if st_{ρ,σ}(φ(Q)) = (k/l, 0) then
      λ_τ^Q = k/l. §3-84 instance: b = 2, m = 2 (j = 0, m =
      j+2), so |D| = 4; k = 1, l = 7, so λ^Q = 1/7. Both
      checked below, plus the per-root I_M contribution
      4·(1/7) = 4/7 and the 7-root total 7·4/7 = 4 (cleared).
    - Prop. 6.4 ≈ the collapse: the 7m top minor roots of P_ξ
      (TeX Proposition "top roots": ma minor roots with
      deg_x = 1 and leading term −x, here a = 7) correspond to
      only ONE final minor π-root τ. Instance: 7m = 14 top
      minor roots (m = 2) collapsing to 1 final minor root.
      The collapse itself is [GGV6]'s, carried as a data
      structure; the counting is checked.
    - Ex. 6.7 ≈ the q₀ computation (TeX Example "ejemplo 16"
      computes q₀ = v_{4,−1}(4,12)/gcd(v_{4,−1}(4,12), 4−1) =
      4/gcd(4,3) = 4 for family F₁). §3-84 instance: q₀ =
      v_{7,−2}(7,21)/gcd(v_{7,−2}(7,21), 7−1) = 7/gcd(7,6) =
      7. Both q₀ computations checked below. The "standard
      argument" from q₀ = a to the collapse is [GGV6]'s,
      carried, not proved here.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- Prop. 6.6(2) instance: |D| = m·b with m = 2, b = 2. -/
example : 2 * 2 = 4 := by decide

/-- Prop. 6.6(2) instance: λ^Q = k/l with k = 1, l = 7, cleared:
    7·1 = 7, so the per-root I_M contribution is 4/7 and the
    7-root total is 4. -/
example : 7 * (2 * 2) / 7 = 4 := by decide

/-- Prop. 6.4 instance: 7m top minor roots with m = 2 collapse
    to 1 final minor root (the collapse is [GGV6]'s). -/
structure MinorCollapse where
  topCount : Nat
  finalCount : Nat
  m : Nat
  htop : topCount = 7 * m
  hfinal : finalCount = 1

def s384_collapse : MinorCollapse where
  topCount := 14
  finalCount := 1
  m := 2
  htop := by decide
  hfinal := by decide

/-- Ex. 6.7, F₁ example: q₀ = v_{4,−1}(4,12)/gcd(v_{4,−1}(4,12),
    4−1) = 4. -/
example : 4 * 4 + (-1) * 12 = 4 := by decide
example : Nat.gcd 4 3 = 1 := by decide
example : 4 / 1 = 4 := by decide

/-- Ex. 6.7, §3-84 instance: q₀ = v_{7,−2}(7,21)/gcd(v_{7,−2}(7,21),
    7−1) = 7. -/
example : 7 * 7 + (-2) * 21 = 7 := by decide
example : Nat.gcd 7 6 = 1 := by decide
example : 7 / 1 = 7 := by decide

/-- The τ expansion (GGHV §3-84): τ = −x + λ₀ + λ_{−2}x^{−2} +
    πx^{−3}, so δ_τ = −3 (the least exponent: it occurs in the
    list and is ≤ every exponent). -/
example : (-3 : Int) ∈ [1, 0, -2, -3] ∧ (-3 : Int) ≤ 1 ∧
    (-3 : Int) ≤ 0 ∧ (-3 : Int) ≤ -2 := by decide
