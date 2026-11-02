/-
  JC2 / GGHV formalization — Part 12: Lean kernel
  certificate for the §5 principal equation (D3, §5
  unrescaled equation CLOSED, modulo compilation).

  Source: Guccione, Guccione, Horruitiner, Valqui,
  arXiv:2204.14178v1, §5, align block before
  `ecuacion principal`. TeX source:
  ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.

  STATUS (2026-10-30): Mathlib (v4.34.0) imported; built
  by `lake build`, NOT by standalone `lean`. No sorry and
  no forbidden declarations. What IS proved here
  (kernel-checked, by Mathlib's `ring` tactic on an
  explicit polynomial identity with integer coefficients,
  computed by the tracked elimination in
  `elimination_certificate_s5.py`):
  - If the 9 original §5 coefficient equations hold
    (the (D̃²) equations D2_1..D2_5, D2_7 and the
    (D̃³) equations Q1, Q2, Q4 — with Q4's final term
    F_{−4}·C₃²³, no fraction to clear) and d_{−1} ≠ 0,
    then the §5 principal equation holds:
    18·C₃²³·F_{−4}·d₁·(d_{−1})⁶ + 8·C₃⁶⁹·F_{−4}³
    + 27·d₀·(d_{−1})⁹ = 0.
    The proof is the identity
      d_{−1} · target = Σ P_i · (original equation i),
    with the P_i explicit polynomials below, verified by
    `ring`; substituting the hypotheses makes the right
    side 0, and d_{−1} ≠ 0 cancels the left factor.
  What is NOT proved here:
  - The 9 original equations themselves: their derivation
    from the C/F/D expansions is D2 (Laurent-series
    algebra), still open. This file closes the
    elimination step (D3 for §5), not the expansions.
  - The rescaling to `nueva ecuacion principal`
    (C₃ = y⁸(y+1), C₃²·F_{−4} = y(y+1)·g(y),
    d₁ = y²⁶·d̃₁, d₀ = y³⁹·d̃₀, d_{−1} = y⁵²·d̃_{−1}):
    that step, and the degree-78 endgame from the
    rescaled equation, are still open as Lean proofs
    (the degree arithmetic itself is kernel-checked in
    Part 4).
-/

import Mathlib

namespace JC2
namespace GGHV
namespace Part12

theorem principal_s5
    (d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 C3 F : Int)
    (hD2_1 : 2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4 = 0)
    (hD2_2 : dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5 = 0)
    (hD2_3 : 2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6 = 0)
    (hD2_4 : dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7 = 0)
    (hD2_5 : 2 * dm2 * dm3 + 2 * dm1 * dm4 + 2 * d0 * dm5 + 2 * d1 * dm6 + 2 * dm8 = 0)
    (hD2_7 : 2 * dm10 + 2 * dm3 * dm4 + 2 * dm2 * dm5 + 2 * dm1 * dm6 + 2 * d0 * dm7 + 2 * d1 * dm8 = 0)
    (hQ1 : 3 * d0 ^ 2 * dm1 + 3 * d1 * dm1 ^ 2 + 6 * d0 * d1 * dm2 + 3 * dm2 ^ 2 + 3 * d1 ^ 2 * dm3 + 6 * dm1 * dm3 + 6 * d0 * dm4 + 6 * d1 * dm5 + 3 * dm7 = 0)
    (hQ2 : 3 * d0 * dm1 ^ 2 + 3 * d0 ^ 2 * dm2 + 6 * d1 * dm1 * dm2 + 6 * d0 * d1 * dm3 + 6 * dm2 * dm3 + 3 * d1 ^ 2 * dm4 + 6 * dm1 * dm4 + 6 * d0 * dm5 + 6 * d1 * dm6 + 3 * dm8 = 0)
    (hQ4 : 3 * dm10 + 3 * dm1 ^ 2 * dm2 + 3 * d0 * dm2 ^ 2 + 6 * d0 * dm1 * dm3 + 6 * d1 * dm2 * dm3 + 3 * d0 ^ 2 * dm4 + 6 * d1 * dm1 * dm4 + 6 * dm3 * dm4 + 6 * d0 * d1 * dm5 + 6 * dm2 * dm5 + 3 * d1 ^ 2 * dm6 + 6 * dm1 * dm6 + 6 * d0 * dm7 + 6 * d1 * dm8 + F * C3 ^ 23 = 0)
    (hm : dm1 ≠ 0) :
    18 * C3 ^ 23 * F * d1 * dm1 ^ 6 + 8 * C3 ^ 69 * F ^ 3 + 27 * d0 * dm1 ^ 9 = 0 := by
  have hid : dm1 * (18 * C3 ^ 23 * F * d1 * dm1 ^ 6 + 8 * C3 ^ 69 * F ^ 3 + 27 * d0 * dm1 ^ 9) =
      (-12 * C3 ^ 46 * F ^ 2 * d0 ^ 2 * dm1 - 12 * C3 ^ 46 * F ^ 2 * d1 * dm1 ^ 2 - 12 * C3 ^ 46 * F ^ 2 * dm1 * dm3 - 18 * C3 ^ 23 * F * d0 ^ 2 * dm1 ^ 3 * dm2 - 18 * C3 ^ 23 * F * d1 * dm1 ^ 4 * dm2 - 18 * C3 ^ 23 * F * dm1 ^ 3 * dm2 * dm3 - 27 * d0 ^ 2 * d1 * dm1 ^ 7 - 27 * d0 ^ 2 * dm1 ^ 5 * dm2 ^ 2 - 27 * d0 * dm1 ^ 7 * dm2 - 27 * d1 ^ 2 * dm1 ^ 8 - 27 * d1 * dm1 ^ 7 * dm3 - 27 * d1 * dm1 ^ 6 * dm2 ^ 2 + 27 * dm1 ^ 9 - 27 * dm1 ^ 5 * dm2 ^ 2 * dm3) * (2 * d0 * dm1 + 2 * d1 * dm2 + 2 * dm4)
      + (-24 * C3 ^ 46 * F ^ 2 * d0 * d1 * dm1 - 12 * C3 ^ 46 * F ^ 2 * dm1 * dm2 - 36 * C3 ^ 23 * F * d0 * d1 * dm1 ^ 3 * dm2 - 18 * C3 ^ 23 * F * dm1 ^ 3 * dm2 ^ 2 - 54 * d0 * d1 ^ 2 * dm1 ^ 7 - 54 * d0 * d1 * dm1 ^ 5 * dm2 ^ 2 + 27 * d0 * dm1 ^ 8 - 54 * d1 * dm1 ^ 7 * dm2 - 27 * dm1 ^ 5 * dm2 ^ 3) * (dm1 ^ 2 + 2 * d0 * dm2 + 2 * d1 * dm3 + 2 * dm5)
      + (-12 * C3 ^ 46 * F ^ 2 * d1 ^ 2 * dm1 - 12 * C3 ^ 46 * F ^ 2 * dm1 ^ 2 - 18 * C3 ^ 23 * F * d1 ^ 2 * dm1 ^ 3 * dm2 - 18 * C3 ^ 23 * F * dm1 ^ 4 * dm2 - 27 * d1 ^ 3 * dm1 ^ 7 - 27 * d1 ^ 2 * dm1 ^ 5 * dm2 ^ 2 - 27 * dm1 ^ 6 * dm2 ^ 2) * (2 * dm1 * dm2 + 2 * d0 * dm3 + 2 * d1 * dm4 + 2 * dm6)
      + (-24 * C3 ^ 46 * F ^ 2 * d0 * dm1 - 36 * C3 ^ 23 * F * d0 * dm1 ^ 3 * dm2 - 54 * d0 * d1 * dm1 ^ 7 - 54 * d0 * dm1 ^ 5 * dm2 ^ 2 - 27 * dm1 ^ 7 * dm2) * (dm2 ^ 2 + 2 * dm1 * dm3 + 2 * d0 * dm4 + 2 * d1 * dm5 + 2 * dm7)
      + (-24 * C3 ^ 46 * F ^ 2 * d1 * dm1 - 36 * C3 ^ 23 * F * d1 * dm1 ^ 3 * dm2 - 54 * d1 ^ 2 * dm1 ^ 7 - 54 * d1 * dm1 ^ 5 * dm2 ^ 2 + 27 * dm1 ^ 8) * (2 * dm2 * dm3 + 2 * dm1 * dm4 + 2 * d0 * dm5 + 2 * d1 * dm6 + 2 * dm8)
      + (-12 * C3 ^ 46 * F ^ 2 * dm1 - 18 * C3 ^ 23 * F * dm1 ^ 3 * dm2 - 27 * d1 * dm1 ^ 7 - 27 * dm1 ^ 5 * dm2 ^ 2) * (2 * dm10 + 2 * dm3 * dm4 + 2 * dm2 * dm5 + 2 * dm1 * dm6 + 2 * d0 * dm7 + 2 * d1 * dm8)
      + (8 * C3 ^ 46 * F ^ 2 * d0 * dm1 + 12 * C3 ^ 23 * F * d0 * dm1 ^ 3 * dm2 + 18 * d0 * d1 * dm1 ^ 7 + 18 * d0 * dm1 ^ 5 * dm2 ^ 2 + 18 * dm1 ^ 7 * dm2) * (3 * d0 ^ 2 * dm1 + 3 * d1 * dm1 ^ 2 + 6 * d0 * d1 * dm2 + 3 * dm2 ^ 2 + 3 * d1 ^ 2 * dm3 + 6 * dm1 * dm3 + 6 * d0 * dm4 + 6 * d1 * dm5 + 3 * dm7)
      + (8 * C3 ^ 46 * F ^ 2 * d1 * dm1 + 12 * C3 ^ 23 * F * d1 * dm1 ^ 3 * dm2 + 18 * d1 ^ 2 * dm1 ^ 7 + 18 * d1 * dm1 ^ 5 * dm2 ^ 2 - 18 * dm1 ^ 8) * (3 * d0 * dm1 ^ 2 + 3 * d0 ^ 2 * dm2 + 6 * d1 * dm1 * dm2 + 6 * d0 * d1 * dm3 + 6 * dm2 * dm3 + 3 * d1 ^ 2 * dm4 + 6 * dm1 * dm4 + 6 * d0 * dm5 + 6 * d1 * dm6 + 3 * dm8)
      + (8 * C3 ^ 46 * F ^ 2 * dm1 + 12 * C3 ^ 23 * F * dm1 ^ 3 * dm2 + 18 * d1 * dm1 ^ 7 + 18 * dm1 ^ 5 * dm2 ^ 2) * (3 * dm10 + 3 * dm1 ^ 2 * dm2 + 3 * d0 * dm2 ^ 2 + 6 * d0 * dm1 * dm3 + 6 * d1 * dm2 * dm3 + 3 * d0 ^ 2 * dm4 + 6 * d1 * dm1 * dm4 + 6 * dm3 * dm4 + 6 * d0 * d1 * dm5 + 6 * dm2 * dm5 + 3 * d1 ^ 2 * dm6 + 6 * dm1 * dm6 + 6 * d0 * dm7 + 6 * d1 * dm8 + F * C3 ^ 23) := by
    ring
  rw [hD2_1, hD2_2, hD2_3, hD2_4, hD2_5, hD2_7, hQ1, hQ2, hQ4] at hid
  simp at hid
  exact hid.resolve_left hm

end Part12
end GGHV
end JC2
