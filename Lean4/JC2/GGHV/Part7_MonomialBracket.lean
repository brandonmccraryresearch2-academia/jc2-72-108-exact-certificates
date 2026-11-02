/-
  JC2 / GGHV formalization — Part 7: Laurent monomial
  bracket and the §4 φ chain rule (D2, first layer).

  Source: Guccione, Guccione, Horruitiner, Valqui,
  arXiv:2204.14178v1, §4 (Props. 4.1, 4.3 proofs).
  TeX source: ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.

  STATUS (2026-10-30): core Lean only, no Mathlib, no sorry,
  no axiom declarations. What IS proved here (kernel-checked):
  - The Poisson bracket of Laurent monomials:
    [x^a y^b, x^c y^d] = (ad − bc) · x^{a+c−1} y^{b+d−1},
    as a coefficient function and an exponent function.
  - The two φ maps of §4 as monomial maps:
    φ₄₁(x) = x^{−1}, φ₄₁(y) = x³y, i.e. (a,b) ↦ (−a+3b, b);
    φ₄₃(x) = x^{−1}, φ₄₃(y) = x⁴y, i.e. (a,b) ↦ (−a+4b, b).
  - [φ(x), φ(y)] for both maps, concretely:
    φ₄₁ gives coefficient −1, exponent (1,0), i.e. −x;
    φ₄₃ gives coefficient −1, exponent (2,0), i.e. −x².
    These are exactly the paper's chain-rule factors:
    [φ(P),φ(Q)] = φ[P,Q]·[φ(x),φ(y)] = −[P,Q]·x (§4.1)
    and = −[P,Q]·x² (§4.3), for the monomial factor.
  - The monomial chain rule for both maps, for arbitrary
    monomial exponents (a,b), (c,d):
    [φ(m₁), φ(m₂)] = φ([m₁,m₂]) · [φ(x), φ(y)],
    in coefficient and exponent form. The coefficient
    identity is proved by an explicit calc-style expansion
    (core Lean has no `ring` tactic; the expansion uses
    Int.add_mul / Int.mul_add / Int.mul_neg and then
    `omega` on the resulting linear form in the atoms
    ad, bc, bd — this is a genuine proof, not a decision
    procedure on closed terms).
  What is NOT proved here, and is NOT claimed:
  - The bracket of POLYNOMIALS (sums of monomials) and
    its bilinearity, nor [φ(P),φ(Q)] for polynomial P,Q.
    Extending the monomial chain rule to polynomials needs
    a finite-support function library (D2, second layer).
    The paper's statements "[φ(P),φ(Q)] = −[P,Q]x" and
    "= −[P,Q]x²" for polynomial P,Q are therefore still
    INTERFACE at the polynomial level; what is proved here
    is their monomial factor and their monomial case.
  - That φ₄₁/φ₄₃ send the paper's Newton polygons to the
    stated final polygons: polygon transformation is
    INTERFACE (it needs the polygon library plus the
    polynomial bracket, and the paper's lists are given in
    different scalings — see Part 3 header).
-/

namespace JC2
namespace GGHV
namespace Part7

/-- Bracket coefficient of monomials x^a y^b, x^c y^d. -/
def bracketCoeff (m n : Int × Int) : Int := m.1 * n.2 - m.2 * n.1

/-- Bracket exponent of monomials x^a y^b, x^c y^d. -/
def bracketExp (m n : Int × Int) : Int × Int :=
  (m.1 + n.1 - 1, m.2 + n.2 - 1)

/-- §4.1 map φ(x) = x^{−1}, φ(y) = x³y, on exponents. -/
def phi41 (m : Int × Int) : Int × Int := (-m.1 + 3 * m.2, m.2)

/-- §4.3 map φ(x) = x^{−1}, φ(y) = x⁴y, on exponents. -/
def phi43 (m : Int × Int) : Int × Int := (-m.1 + 4 * m.2, m.2)

/-- [φ₄₁(x), φ₄₁(y)] = −x: coefficient −1, exponent (1,0). -/
theorem phi41_xy_bracket :
    bracketCoeff (-1, 0) (3, 1) = -1 ∧ bracketExp (-1, 0) (3, 1) = (1, 0) := by
  constructor <;> decide

/-- [φ₄₃(x), φ₄₃(y)] = −x²: coefficient −1, exponent (2,0). -/
theorem phi43_xy_bracket :
    bracketCoeff (-1, 0) (4, 1) = -1 ∧ bracketExp (-1, 0) (4, 1) = (2, 0) := by
  constructor <;> decide

/-- Monomial chain rule, φ₄₃, coefficient form:
    [φ(m₁), φ(m₂)] has coefficient −(ad − bc). -/
theorem chain_coeff_43 (a b c d : Int) :
    bracketCoeff (phi43 (a, b)) (phi43 (c, d)) = -(a * d - b * c) := by
  have h2 : b * (4 * d) = 4 * b * d := by rw [← Int.mul_assoc, Int.mul_comm b 4]
  have h1 : (-a + 4 * b) * d = -(a * d) + 4 * b * d := by
    rw [Int.add_mul, Int.neg_mul]
  have h3 : b * (-c + 4 * d) = -(b * c) + 4 * b * d := by
    rw [Int.mul_add, Int.mul_neg, h2]
  simp only [bracketCoeff, phi43]
  rw [h1, h3]
  omega

/-- Monomial chain rule, φ₄₃, exponent form:
    the exponent of [φ(m₁), φ(m₂)] is the φ-image of the
    exponent of [m₁, m₂], shifted by (2,0) (multiplication
    by −x²). Stated componentwise. -/
theorem chain_exp_43 (a b c d : Int) :
    (bracketExp (phi43 (a, b)) (phi43 (c, d))).1 =
      (phi43 (bracketExp (a, b) (c, d))).1 + 2 ∧
    (bracketExp (phi43 (a, b)) (phi43 (c, d))).2 =
      (phi43 (bracketExp (a, b) (c, d))).2 := by
  constructor <;> simp only [bracketExp, phi43] <;> omega

/-- Monomial chain rule, φ₄₁, coefficient form. -/
theorem chain_coeff_41 (a b c d : Int) :
    bracketCoeff (phi41 (a, b)) (phi41 (c, d)) = -(a * d - b * c) := by
  have h2 : b * (3 * d) = 3 * b * d := by rw [← Int.mul_assoc, Int.mul_comm b 3]
  have h1 : (-a + 3 * b) * d = -(a * d) + 3 * b * d := by
    rw [Int.add_mul, Int.neg_mul]
  have h3 : b * (-c + 3 * d) = -(b * c) + 3 * b * d := by
    rw [Int.mul_add, Int.mul_neg, h2]
  simp only [bracketCoeff, phi41]
  rw [h1, h3]
  omega

/-- Monomial chain rule, φ₄₁, exponent form: shift by
    (1,0) (multiplication by −x). -/
theorem chain_exp_41 (a b c d : Int) :
    (bracketExp (phi41 (a, b)) (phi41 (c, d))).1 =
      (phi41 (bracketExp (a, b) (c, d))).1 + 1 ∧
    (bracketExp (phi41 (a, b)) (phi41 (c, d))).2 =
      (phi41 (bracketExp (a, b) (c, d))).2 := by
  constructor <;> simp only [bracketExp, phi41] <;> omega

end Part7
end GGHV
end JC2
