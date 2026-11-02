/-
  JC2 / GGHV formalization — Part 10: monomial bracket
  Jacobi identity and φ-bracket factors (D2, second layer).

  Source: Guccione, Guccione, Horruitiner, Valqui,
  arXiv:2204.14178v1, §§4–5 (monomial bracket ad−bc,
  φ₄₁/φ₄₃ maps, [φ(x),φ(y)] = −x / −x²).

  STATUS (2026-10-30): Mathlib (v4.34.0) imported; this
  file is built by `lake build`, NOT by standalone `lean`
  (standalone `lean` cannot find Mathlib). No sorry and no forbidden declarations. What IS proved here (kernel-checked,
  with Mathlib's `ring` tactic — the tactic core Lean
  lacks, which is why the Jacobi identity was left open
  in Part 8):
  - Jacobi identity for monomial brackets, in coefficient
    form, for arbitrary exponents: the cyclic sum of
    [[m,n],p] coefficients is 0 (all three double brackets
    share the exponent (a+c+e−2, b+d+f−2), so the
    coefficient sum being 0 is the Jacobi identity).
  - φ-bracket factors for arbitrary monomials: for both
    φ₄₁ and φ₄₃, bracketCoeff (φ m) (φ n) = −bracketCoeff
    m n, and bracketExp (φ m) (φ n) = φ (bracketExp m n)
    + (1,0) for φ₄₁ and + (2,0) for φ₄₃. These are
    exactly the shifts in [φ(x),φ(y)] = −x and −x²
    (Part 7, concrete case), now for arbitrary monomials:
    [φ(m),φ(n)] = −[m,n] · x for φ₄₁ and −[m,n] · x²
    for φ₄₃, in coefficient/exponent form.
  What is NOT proved here: the polynomial bracket
  (finite-support polynomials, bilinearity), the
  polynomial φ chain rule, and the C/F/D expansions and
  coefficient systems of §§5–6. Those remain open in D2.
-/

import Mathlib

namespace JC2
namespace GGHV
namespace Part10

/-- Monomial bracket coefficient and exponent (as in Part 7). -/
def bracketCoeff (m n : Int × Int) : Int := m.1 * n.2 - m.2 * n.1
def bracketExp (m n : Int × Int) : Int × Int := (m.1 + n.1 - 1, m.2 + n.2 - 1)

/-- Jacobi identity, coefficient form, arbitrary exponents. -/
theorem jacobi_coeff (a b c d e f : Int) :
    bracketCoeff (a, b) (c, d) * bracketCoeff (a + c - 1, b + d - 1) (e, f) +
    bracketCoeff (c, d) (e, f) * bracketCoeff (c + e - 1, d + f - 1) (a, b) +
    bracketCoeff (e, f) (a, b) * bracketCoeff (e + a - 1, f + b - 1) (c, d) = 0 := by
  simp only [bracketCoeff]
  ring

/-- φ maps on exponent pairs (as in Part 7). -/
def phi41 (m : Int × Int) : Int × Int := (-m.1 + 3 * m.2, m.2)
def phi43 (m : Int × Int) : Int × Int := (-m.1 + 4 * m.2, m.2)

/-- φ preserves the bracket coefficient up to sign −1. -/
theorem bracketCoeff_phi41 (m n : Int × Int) :
    bracketCoeff (phi41 m) (phi41 n) = -bracketCoeff m n := by
  simp only [phi41, bracketCoeff]
  ring

theorem bracketCoeff_phi43 (m n : Int × Int) :
    bracketCoeff (phi43 m) (phi43 n) = -bracketCoeff m n := by
  simp only [phi43, bracketCoeff]
  ring

/-- φ-bracket exponent shifts: (1,0) for φ₄₁, (2,0) for φ₄₃. -/
theorem bracketExp_phi41 (m n : Int × Int) :
    bracketExp (phi41 m) (phi41 n) =
      ((phi41 (bracketExp m n)).1 + 1, (phi41 (bracketExp m n)).2) := by
  rw [Prod.ext_iff]
  constructor <;> simp only [phi41, bracketExp]; ring

theorem bracketExp_phi43 (m n : Int × Int) :
    bracketExp (phi43 m) (phi43 n) =
      ((phi43 (bracketExp m n)).1 + 2, (phi43 (bracketExp m n)).2) := by
  rw [Prod.ext_iff]
  constructor <;> simp only [phi43, bracketExp]; ring

end Part10
end GGHV
end JC2
