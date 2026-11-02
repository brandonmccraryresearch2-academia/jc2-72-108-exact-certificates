/-
  JC2 / GGHV formalization — Part 11: Lean kernel
  certificate for the §6 principal equation (D3, §6 CLOSED).

  Source: Guccione, Guccione, Horruitiner, Valqui,
  arXiv:2204.14178v1, §6, align block before
  `ecuacion principal para 7`. TeX source:
  ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.

  STATUS (2026-10-30): Mathlib (v4.34.0) imported; built
  by `lake build`, NOT by standalone `lean`. No sorry and no forbidden declarations. What IS proved here (kernel-checked,
  by Mathlib's `ring` tactic on an explicit polynomial
  identity with integer coefficients, computed by the
  tracked elimination in `elimination_certificate_s6.py`):
  - If the 9 original §6 coefficient equations hold
    (the (D̃²) equations D2_1..D2_5, D2_7 and the
    (D̃³) equations Q1, Q2, Q4 — with Q4 doubled so all
    coefficients are integers, the (1/2)y⁹ term becoming
    y⁹) and d_{−1} ≠ 0, then the §6 principal equation
    holds: 9y⁹d₁(d_{−1})⁶ + y²⁷ + 27d₀(d_{−1})⁹ = 0.
    The proof is the identity
      d_{−1} · target = Σ P_i · (original equation i),
    with the P_i explicit polynomials below, verified by
    `ring`; substituting the hypotheses makes the right
    side 0, and d_{−1} ≠ 0 cancels the left factor.
  What is NOT proved here:
  - The 9 original equations themselves: their derivation
    from the C/F/D expansions is D2 (Laurent-series
    algebra), still open. This file closes the
    elimination step (D3 for §6), not the expansions.
  - The §5 principal equation: its tracked certificate
    is NOT in this file (the §5 system differs in Q4's
    final term and in the rescaling to `nueva ecuacion
    principal`); D3 for §5 remains open, though its
    SymPy I1 verification (elimination_s5.py) stands.
-/

import Mathlib

namespace JC2
namespace GGHV
namespace Part11

theorem principal_s6
    (d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 y : Int)
    (hD2_1 : 2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4 = 0)
    (hD2_2 : dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5 = 0)
    (hD2_3 : 2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6 = 0)
    (hD2_4 : dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7 = 0)
    (hD2_5 : 2 * dm2 * dm3 + 2 * dm1 * dm4 + 2 * d0 * dm5 + 2 * d1 * dm6 + 2 * dm8 = 0)
    (hD2_7 : 2 * dm10 + 2 * dm3 * dm4 + 2 * dm2 * dm5 + 2 * dm1 * dm6 + 2 * d0 * dm7 + 2 * d1 * dm8 = 0)
    (hQ1 : 3 * d0 ^ 2 * dm1 + 3 * d1 * dm1 ^ 2 + 6 * d0 * d1 * dm2 + 3 * dm2 ^ 2 + 3 * d1 ^ 2 * dm3 + 6 * dm1 * dm3 + 6 * d0 * dm4 + 6 * d1 * dm5 + 3 * dm7 = 0)
    (hQ2 : 3 * d0 * dm1 ^ 2 + 3 * d0 ^ 2 * dm2 + 6 * d1 * dm1 * dm2 + 6 * d0 * d1 * dm3 + 6 * dm2 * dm3 + 3 * d1 ^ 2 * dm4 + 6 * dm1 * dm4 + 6 * d0 * dm5 + 6 * d1 * dm6 + 3 * dm8 = 0)
    (hQ4 : 6 * dm10 + 6 * dm1 ^ 2 * dm2 + 6 * d0 * dm2 ^ 2 + 12 * d0 * dm1 * dm3 + 12 * d1 * dm2 * dm3 + 6 * d0 ^ 2 * dm4 + 12 * d1 * dm1 * dm4 + 12 * dm3 * dm4 + 12 * d0 * d1 * dm5 + 12 * dm2 * dm5 + 6 * d1 ^ 2 * dm6 + 12 * dm1 * dm6 + 12 * d0 * dm7 + 12 * d1 * dm8 + y ^ 9 = 0)
    (hm : dm1 ≠ 0) :
    9 * y ^ 9 * d1 * dm1 ^ 6 + y ^ 27 + 27 * d0 * dm1 ^ 9 = 0 := by
  have hid : dm1 * (9 * y ^ 9 * d1 * dm1 ^ 6 + y ^ 27 + 27 * d0 * dm1 ^ 9) =
      (-27 * d0 ^ 2 * d1 * dm1 ^ 7 - 27 * d0 ^ 2 * dm1 ^ 5 * dm2 ^ 2 - 9 * d0 ^ 2 * dm1 ^ 3 * dm2 * y ^ 9 - 3 * d0 ^ 2 * dm1 * y ^ 18 - 27 * d0 * dm1 ^ 7 * dm2 - 27 * d1 ^ 2 * dm1 ^ 8 - 27 * d1 * dm1 ^ 7 * dm3 - 27 * d1 * dm1 ^ 6 * dm2 ^ 2 - 9 * d1 * dm1 ^ 4 * dm2 * y ^ 9 - 3 * d1 * dm1 ^ 2 * y ^ 18 + 27 * dm1 ^ 9 - 27 * dm1 ^ 5 * dm2 ^ 2 * dm3 - 9 * dm1 ^ 3 * dm2 * dm3 * y ^ 9 - 3 * dm1 * dm3 * y ^ 18) * (2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4)
      + (-54 * d0 * d1 ^ 2 * dm1 ^ 7 - 54 * d0 * d1 * dm1 ^ 5 * dm2 ^ 2 - 18 * d0 * d1 * dm1 ^ 3 * dm2 * y ^ 9 - 6 * d0 * d1 * dm1 * y ^ 18 + 27 * d0 * dm1 ^ 8 - 54 * d1 * dm1 ^ 7 * dm2 - 27 * dm1 ^ 5 * dm2 ^ 3 - 9 * dm1 ^ 3 * dm2 ^ 2 * y ^ 9 - 3 * dm1 * dm2 * y ^ 18) * (dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5)
      + (-27 * d1 ^ 3 * dm1 ^ 7 - 27 * d1 ^ 2 * dm1 ^ 5 * dm2 ^ 2 - 9 * d1 ^ 2 * dm1 ^ 3 * dm2 * y ^ 9 - 3 * d1 ^ 2 * dm1 * y ^ 18 - 27 * dm1 ^ 6 * dm2 ^ 2 - 9 * dm1 ^ 4 * dm2 * y ^ 9 - 3 * dm1 ^ 2 * y ^ 18) * (2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6)
      + (-54 * d0 * d1 * dm1 ^ 7 - 54 * d0 * dm1 ^ 5 * dm2 ^ 2 - 18 * d0 * dm1 ^ 3 * dm2 * y ^ 9 - 6 * d0 * dm1 * y ^ 18 - 27 * dm1 ^ 7 * dm2) * (dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7)
      + (-54 * d1 ^ 2 * dm1 ^ 7 - 54 * d1 * dm1 ^ 5 * dm2 ^ 2 - 18 * d1 * dm1 ^ 3 * dm2 * y ^ 9 - 6 * d1 * dm1 * y ^ 18 + 27 * dm1 ^ 8) * (2 * dm2 * dm3 + 2 * dm1 * dm4 + 2 * d0 * dm5 + 2 * d1 * dm6 + 2 * dm8)
      + (-27 * d1 * dm1 ^ 7 - 27 * dm1 ^ 5 * dm2 ^ 2 - 9 * dm1 ^ 3 * dm2 * y ^ 9 - 3 * dm1 * y ^ 18) * (2 * dm10 + 2 * dm3 * dm4 + 2 * dm2 * dm5 + 2 * dm1 * dm6 + 2 * d0 * dm7 + 2 * d1 * dm8)
      + (18 * d0 * d1 * dm1 ^ 7 + 18 * d0 * dm1 ^ 5 * dm2 ^ 2 + 6 * d0 * dm1 ^ 3 * dm2 * y ^ 9 + 2 * d0 * dm1 * y ^ 18 + 18 * dm1 ^ 7 * dm2) * (3 * d0 ^ 2 * dm1 + 3 * d1 * dm1 ^ 2 + 6 * d0 * d1 * dm2 + 3 * dm2 ^ 2 + 3 * d1 ^ 2 * dm3 + 6 * dm1 * dm3 + 6 * d0 * dm4 + 6 * d1 * dm5 + 3 * dm7)
      + (18 * d1 ^ 2 * dm1 ^ 7 + 18 * d1 * dm1 ^ 5 * dm2 ^ 2 + 6 * d1 * dm1 ^ 3 * dm2 * y ^ 9 + 2 * d1 * dm1 * y ^ 18 - 18 * dm1 ^ 8) * (3 * d0 * dm1 ^ 2 + 3 * d0 ^ 2 * dm2 + 6 * d1 * dm1 * dm2 + 6 * d0 * d1 * dm3 + 6 * dm2 * dm3 + 3 * d1 ^ 2 * dm4 + 6 * dm1 * dm4 + 6 * d0 * dm5 + 6 * d1 * dm6 + 3 * dm8)
      + (9 * d1 * dm1 ^ 7 + 9 * dm1 ^ 5 * dm2 ^ 2 + 3 * dm1 ^ 3 * dm2 * y ^ 9 + dm1 * y ^ 18) * (6 * dm10 + 6 * dm1 ^ 2 * dm2 + 6 * d0 * dm2 ^ 2 + 12 * d0 * dm1 * dm3 + 12 * d1 * dm2 * dm3 + 6 * d0 ^ 2 * dm4 + 12 * d1 * dm1 * dm4 + 12 * dm3 * dm4 + 12 * d0 * d1 * dm5 + 12 * dm2 * dm5 + 6 * d1 ^ 2 * dm6 + 12 * dm1 * dm6 + 12 * d0 * dm7 + 12 * d1 * dm8 + y ^ 9) := by
    ring
  rw [hD2_1, hD2_2, hD2_3, hD2_4, hD2_5, hD2_7, hQ1, hQ2, hQ4] at hid
  simp at hid
  exact hid.resolve_left hm

end Part11
end GGHV
end JC2
