/-
  JC2 / GGHV formalization — Part 8: maximal-valuation
  segments (D1, second layer, concrete cases) and φ
  bijectivity / bracket antisymmetry (D2, second layer).

  Source: Guccione, Guccione, Horruitiner, Valqui,
  arXiv:2204.14178v1, §§4–5. TeX source:
  ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.

  STATUS (2026-10-30): core Lean only, no Mathlib, no sorry,
  no axiom declarations. What IS proved here (kernel-checked,
  all by `decide` on concrete lists, plus `omega` for the
  two variable identities):
  - D1: for the Prop. 4.1 / §5 shapes
    P = [(0,0),(1,1),(6,16),(6,18),(0,18)] and
    Q = [(0,0),(1,0),(9,24),(9,27),(0,27)], the valuation
    lists under directions (3,−1) and (1,0), and the
    maximal-valuation facts: under (3,−1), P's valuations
    are [0,2,2,0,−18] (max 2, attained at (1,1) and (6,16));
    Q's are [0,3,3,0,−27] (max 3, attained at (1,0) and
    (9,24)); under (1,0), P's are [0,1,6,6,0] (max 6,
    attained at (6,16) and (6,18)); Q's are [0,1,9,9,0]
    (max 9, attained at (9,24) and (9,27)). These are
    exactly the §5 en/st endpoints: en_{3,−1}(P) = (6,16),
    en_{3,−1}(Q) = (9,24), st_{1,0}(P) = (6,16),
    en_{1,0}(P) = (6,18), st_{1,0}(Q) = (9,24),
    en_{1,0}(Q) = (9,27) — as maximal-valuation attainment,
    which is what this file proves. It does NOT prove the
    general en/st definitions or that these segments are
    the homogeneous parts ℓ_{ρ,σ}; that remains INTERFACE.
  - D2: φ₄₁ and φ₄₃ are bijective on exponent pairs, with
    explicit inverses: φ₄₁⁻¹(u,v) = (−u+3v, v) and
    φ₄₃⁻¹(u,v) = (−u+4v, v). Hence the §4 φ maps are
    automorphisms of the Laurent monomial lattice at the
    exponent level (the polynomial-level automorphism
    statement still needs the polynomial library).
  - D2: bracket antisymmetry for monomials:
    [m, n] = −[n, m] in coefficient form, for arbitrary
    exponents (proved from Int.mul_comm, then `omega`).
  What is NOT proved here:
  - The Jacobi identity for monomial brackets (a cubic
    exponent identity; core Lean has no `ring` tactic, and
    a manual expansion was not attempted in this run).
  - Polynomial bracket bilinearity and the polynomial
    φ chain rule (finite-support polynomial library).
  - en/st for any direction or polygon other than the
    four cases above.
-/

namespace JC2
namespace GGHV
namespace Part8

/-- Weighted valuation, as in Part 6 (restated here so
    this file is standalone). -/
def dirVal (ρ σ : Int) (a b : Int) : Int := ρ * a + σ * b

/-- Valuation list of a vertex list under a direction. -/
def valList (ρ σ : Int) (vs : List (Int × Int)) : List Int :=
  vs.map (fun v => dirVal ρ σ v.1 v.2)

/-- Prop. 4.1 / §5 P shape. -/
def shapeP : List (Int × Int) :=
  [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)]

/-- Prop. 4.1 / §5 Q shape. -/
def shapeQ : List (Int × Int) :=
  [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)]

/-- Valuation lists, computed exactly. -/
theorem val_P_3m1 : valList 3 (-1) shapeP = [0, 2, 2, 0, -18] := by decide
theorem val_Q_3m1 : valList 3 (-1) shapeQ = [0, 3, 3, 0, -27] := by decide
theorem val_P_10 : valList 1 0 shapeP = [0, 1, 6, 6, 0] := by decide
theorem val_Q_10 : valList 1 0 shapeQ = [0, 1, 9, 9, 0] := by decide

/-- Maximal-valuation attainment: every valuation in each
    list is at most the stated maximum, and the maximum
    is attained at the paper's en/st vertices. -/
theorem max_P_3m1 : (∀ x ∈ valList 3 (-1) shapeP, x ≤ 2) ∧
    dirVal 3 (-1) 6 16 = 2 := by
  constructor
  · decide
  · decide

theorem max_Q_3m1 : (∀ x ∈ valList 3 (-1) shapeQ, x ≤ 3) ∧
    dirVal 3 (-1) 9 24 = 3 := by
  constructor
  · decide
  · decide

theorem max_P_10 : (∀ x ∈ valList 1 0 shapeP, x ≤ 6) ∧
    dirVal 1 0 6 16 = 6 ∧ dirVal 1 0 6 18 = 6 := by
  refine ⟨by decide, by decide, by decide⟩

theorem max_Q_10 : (∀ x ∈ valList 1 0 shapeQ, x ≤ 9) ∧
    dirVal 1 0 9 24 = 9 ∧ dirVal 1 0 9 27 = 9 := by
  refine ⟨by decide, by decide, by decide⟩

/-- φ maps and inverses, on exponent pairs (as in Part 7). -/
def phi41 (m : Int × Int) : Int × Int := (-m.1 + 3 * m.2, m.2)
def phi41Inv (m : Int × Int) : Int × Int := (-m.1 + 3 * m.2, m.2)
def phi43 (m : Int × Int) : Int × Int := (-m.1 + 4 * m.2, m.2)
def phi43Inv (m : Int × Int) : Int × Int := (-m.1 + 4 * m.2, m.2)

/-- φ₄₁ is bijective on exponents: inverse both ways,
    stated componentwise (pair equality would need the
    same linear computation per component). Note phi41Inv
    has the same formula as phi41 because the map is an
    involution: φ(φ(a,b)) = (a,b) by direct computation. -/
theorem phi41_bijective (a b : Int) :
    (phi41 (phi41Inv (a, b))).1 = a ∧ (phi41 (phi41Inv (a, b))).2 = b ∧
    (phi41Inv (phi41 (a, b))).1 = a ∧ (phi41Inv (phi41 (a, b))).2 = b := by
  refine ⟨by simp only [phi41, phi41Inv]; omega, by simp only [phi41, phi41Inv],
    by simp only [phi41, phi41Inv]; omega, by simp only [phi41, phi41Inv]⟩

theorem phi43_bijective (a b : Int) :
    (phi43 (phi43Inv (a, b))).1 = a ∧ (phi43 (phi43Inv (a, b))).2 = b ∧
    (phi43Inv (phi43 (a, b))).1 = a ∧ (phi43Inv (phi43 (a, b))).2 = b := by
  refine ⟨by simp only [phi43, phi43Inv]; omega, by simp only [phi43, phi43Inv],
    by simp only [phi43, phi43Inv]; omega, by simp only [phi43, phi43Inv]⟩

/-- Bracket coefficient, as in Part 7 (restated standalone). -/
def bracketCoeff (m n : Int × Int) : Int := m.1 * n.2 - m.2 * n.1

/-- Bracket antisymmetry for monomials, arbitrary exponents. -/
theorem bracket_antisymm (a b c d : Int) :
    bracketCoeff (a, b) (c, d) = -bracketCoeff (c, d) (a, b) := by
  have h1 : c * b = b * c := Int.mul_comm c b
  have h2 : d * a = a * d := Int.mul_comm d a
  simp only [bracketCoeff]
  omega

end Part8
end GGHV
end JC2
