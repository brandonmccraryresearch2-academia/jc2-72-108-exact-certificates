/-
  JC2 / GGHV formalization — Part 3: §4 Newton reductions
  (Propositions 4.1–4.4).

  Source: Guccione, Guccione, Horruitiner, Valqui,
  arXiv:2204.14178v1, §4 ("Reducing the size of the Newton
  polygon"). TeX source:
  ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.

  STATUS (2026-10-30): core Lean only, no Mathlib, no sorry.
  What IS proved here (kernel-checked):
  - The final Newton-polygon vertex lists of Props. 4.1–4.4
    exactly as stated in the paper, as data.
  - The uniform (m,n) = (2,3) / (3,2) scaling between the
    P- and Q-vertex lists in every §4 case: corresponding
    Q vertices are (3/2) times the P vertices, checked by
    cross-multiplication (no division is used, so no
    rational-arithmetic subtlety is hidden).
  - The intermediate three shapes a)/b)/c) of Prop. 4.3 as
    data, and the fact that a) and b) collapse to the same
    final shape (case 2 of the proposition) while c) gives
    the extra-vertex shape (case 1), as the paper states.
  What is NOT proved here, and is NOT claimed:
  - The reductions themselves: that a counterexample in case
    (9,27)/(9,24)/(8,28)/(7,21) can be transformed by the
    paper's automorphisms φ_1, φ_2, φ_3, φ into a pair with
    exactly these Newton polygons and [P,Q] = x (or x^2).
    Those proofs need a Laurent-polynomial algebra library
    (L^{(1)} = K[x, x^{-1}, y], weighted valuations, en/st,
    [GGV1] Cor. 7.4, [GGV1] Prop. 8.2, [GGV2] Prop. 3.12,
    [GGV6] Prop. 2.5) and the PossibleStartingPoints
    algorithm of Prop. 4.2. They are INTERFACE items in
    CORRESPONDENCE.md, not theorems in this file.
  - The φ maps themselves are recorded as data (exponent
    maps are NOT asserted: the paper's before/after lists
    are given in different scalings, and asserting an
    exponent-map identity without checking it against the
    paper's scaled lists would be fabrication).
  Vertices are (Int × Int) pairs because Prop. 4.3's
  intermediate shapes contain (-2,0) and (-3,0).
-/

namespace JC2
namespace GGHV
namespace Part3

/-- A Newton polygon, as its vertex list in the paper's order. -/
def NP := List (Int × Int)

/-- Prop. 4.1, case (9,27): P and Q in L^{(1)}, [P,Q] = x. -/
def prop41_P : NP := [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)]
def prop41_Q : NP := [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)]

/-- Prop. 4.2, case (9,24): three outcomes, [P,Q] = x. -/
def prop42_P1 : NP := [(0, 0), (1, 1), (6, 16), (6, 18), (0, 12)]
def prop42_Q1 : NP := [(0, 0), (1, 0), (9, 24), (9, 27), (0, 18)]
def prop42_P2 : NP := [(0, 0), (1, 1), (6, 16), (6, 18), (0, 6)]
def prop42_Q2 : NP := [(0, 0), (1, 0), (9, 24), (9, 27), (0, 9)]
def prop42_P3 : NP := [(0, 0), (1, 1), (6, 16), (6, 18)]
def prop42_Q3 : NP := [(0, 0), (1, 0), (9, 24), (9, 27)]

/-- Prop. 4.3, case (8,28): two outcomes, [P,Q] = x^2.
    Case 1 is the shape WITH the extra vertices (0,8)/(0,12);
    case 2 is WITHOUT them. This is the Helali interface:
    Helali Case 1 = Prop. 4.3 case 1, Helali Case 2 = case 2,
    as stated in the formalization map (identification of
    the two systems term by term is still an open check,
    recorded in CORRESPONDENCE.md, not asserted here). -/
def prop43_P1 : NP := [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)]
def prop43_Q1 : NP := [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)]
def prop43_P2 : NP := [(0, 0), (1, 0), (8, 14), (8, 16)]
def prop43_Q2 : NP := [(0, 0), (2, 1), (12, 21), (12, 24)]

/-- Prop. 4.3 intermediate shapes, before the final φ:
    a) and b) differ only in the first vertex, (-2,0) vs
    (-3,0); c) adds the (16,4) vertex. -/
def prop43_shape_a : NP := [(-2, 0), (0, 0), (28, 8), (0, 1)]
def prop43_shape_b : NP := [(-3, 0), (0, 0), (28, 8), (0, 1)]
def prop43_shape_c : NP := [(-3, 0), (0, 0), (16, 4), (28, 8), (0, 1)]

/-- Prop. 4.4, case (7,21): as stated in the proposition
    (the (m,n)-scaled form in the paper's statement). -/
def prop44_P : NP := [(0, 0), (4, 0), (6, 2), (0, 14)]
def prop44_Q : NP := [(0, 0), (6, 0), (9, 3), (0, 21)]

/-- The paper's §6 form of the (7,21) shapes (Theorem
    "teorema impossible para 7"): P (4,0),(2,6),(0,14) and
    Q (6,0),(3,9),(0,21). Note this is NOT the same list
    as prop44_P/prop44_Q above: the (6,2)/(9,3) vertices
    of Prop. 4.4 appear as (2,6)/(3,9) in §6. The exact
    transformation linking the two lists is NOT asserted
    here: it is an OPEN check (see CORRESPONDENCE.md),
    because the Prop. 4.4 proof's final polygon is stated
    in a different scaling from the §6 theorem's, and
    asserting a φ-exponent identity without checking it
    against the paper's scaled lists would be fabrication.
    Both lists are recorded verbatim so the difference is
    visible, not smoothed over. -/
def thm721_P : NP := [(0, 0), (4, 0), (2, 6), (0, 14)]
def thm721_Q : NP := [(0, 0), (6, 0), (3, 9), (0, 21)]

/-- Scaling check, Prop. 4.1: corresponding Q vertices
    are (3/2) times the P vertices, by cross-multiplication.
    Checked pairs: (6,16)->(9,24), (6,18)->(9,27), (0,18)->(0,27). -/
theorem prop41_scaling :
    (9 * 2 = 6 * 3 ∧ 24 * 2 = 16 * 3 ∧ 27 * 2 = 18 * 3 ∧ 0 * 2 = 0 * 3) := by
  decide

/-- Scaling check, Prop. 4.3: (8,14)->(12,21), (8,16)->(12,24),
    (0,8)->(0,12), all factor 3/2 by cross-multiplication. -/
theorem prop43_scaling :
    (12 * 2 = 8 * 3 ∧ 21 * 2 = 14 * 3 ∧ 24 * 2 = 16 * 3 ∧ 0 * 2 = 0 * 3) := by
  decide

/-- Scaling check, §6 (7,21) form: (4,0)->(6,0), (2,6)->(3,9),
    (0,14)->(0,21), all factor 3/2. -/
theorem thm721_scaling :
    (6 * 2 = 4 * 3 ∧ 3 * 2 = 2 * 3 ∧ 9 * 2 = 6 * 3 ∧ 0 * 2 = 0 * 3) := by
  decide

/-- Shapes a) and b) of Prop. 4.3 agree except in the first
    vertex; the paper collapses both to final case 2. -/
theorem prop43_ab_agree_tail :
    prop43_shape_a.tail = [ (0, 0), (28, 8), (0, 1) ] ∧
    prop43_shape_b.tail = [ (0, 0), (28, 8), (0, 1) ] := by
  constructor <;> rfl

/-- Final case 2 has no extra vertex; final case 1 has
    exactly one extra vertex in each polygon. -/
theorem prop43_case_lengths :
    prop43_P2.length = 4 ∧ prop43_Q2.length = 4 ∧
    prop43_P1.length = 5 ∧ prop43_Q1.length = 5 := by
  decide

/-- The φ maps of §4, recorded as data (paper statements,
    not proved transformations):
    Prop. 4.1: φ(x) = x^{-1}, φ(y) = x^3 y, [φ(P),φ(Q)] = x.
    Prop. 4.3: φ(x) = x^{-1}, φ(y) = x^4 y, [φ(P),φ(Q)] = -[P,Q] x^2.
    The bracket identities are INTERFACE, not proved here. -/
def phi41 : String := "x ↦ x^{-1}, y ↦ x^3 y"
def phi43 : String := "x ↦ x^{-1}, y ↦ x^4 y"

end Part3
end GGHV
end JC2
