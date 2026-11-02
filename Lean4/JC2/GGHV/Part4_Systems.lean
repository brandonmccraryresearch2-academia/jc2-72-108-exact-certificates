/-
  JC2 / GGHV formalization — Part 4: §§5–6 polynomial systems.

  Source: Guccione, Guccione, Horruitiner, Valqui,
  arXiv:2204.14178v1, §5 ("Systems of polynomial equations
  for (9,24) and (9,27)") and §6 ("Systems of polynomial
  equations for (7,21)"). TeX source:
  ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.

  STATUS (2026-10-30): core Lean only, no Mathlib, no sorry.
  What IS proved here (kernel-checked):
  - §5 endgame degree arithmetic: the paper's "nueva
    ecuacion principal" gives deg((y+1)^66 g(y)^3) = 78
    (so deg g = 4), while its own bounds give
    deg(27 d̃_0 (d̃_{-1})^9) ≤ 12 + 9*7 = 75 and
    deg(18 (y+1)^22 d̃_1 (d̃_{-1})^6 g(y)) ≤ 22+8+42+4 = 76;
    both are < 78, so the principal equation cannot hold
    with those bounds. This is proved as a conditional
    theorem: GIVEN the principal equation and the bounds,
    False. The principal equation itself is INTERFACE.
  - §6 principal-equation degree check: with d_{-1} = α y^k,
    deg d_0 = 9, deg d_1 = 6, the three terms of
    9 y^9 d_1 (d_{-1})^6 + y^27 + 27 d_0 (d_{-1})^9 = 0
    have degrees 15+6k, 27, 9+9k; at k = 2 all three are
    27, as the paper computes. The derivation of k = 2
    and the final non-square contradiction are INTERFACE.
  - §5/§6 theorem conditions as data: the en/st points,
    the C-expansion shapes, and the final contradiction
    statements.
  What is NOT proved here (the known open gap, from the
  formalization map):
  - The Mathematica (CAS) eliminations: §5's elimination
    to the principal equation (eq. (5.9) in the map's
    numbering; "ecuacion principal" / "nueva ecuacion
    principal" in the TeX labels) and §6's elimination to
    the principal equation (eq. (6.18) in the map's
    numbering; "ecuacion principal para 7"). Lean cannot
    cite a CAS. Each elimination needs explicit elimination
    identities (a certificate: the eliminated system plus
    the combination that yields the principal equation),
    or a verified elimination procedure. Until such a
    certificate is produced, Thm 5.1 and Thm 6.1 are
    CONDITIONAL on their principal equations, and that
    conditionality is part of their Lean statements.
    UPDATE 2026-10-30: BOTH eliminations have since been
    re-derived independently in SymPy (scripts
    `elimination_s6.py` and `elimination_s5.py`, logs
    `elimination_s6.log` / `elimination_s5.log`):
    sequential linear elimination plus a resultant in
    d_{−2} gives exactly −27/(64·d_{−1}³) times the
    paper's principal equation in both cases, remainder 0.
    Those are I1 (single-route CAS) verifications of the
    eliminations, NOT Lean kernel proofs; the Lean
    elimination certificates (explicit combinations) are
    still open, and Thm 5.1 / Thm 6.1 remain conditional
    in Lean until such certificates are produced.
  - The C/F expansions themselves (Props. "calculo de C"
    and "calculo de C para 7"), the D_k ∈ K[y] induction,
    the f-separability proposition, and the (D^2)/(D^3)
    coefficient systems: these need a Laurent-series
    algebra library and are INTERFACE items here.
-/

namespace JC2
namespace GGHV
namespace Part4

/-- §5 Theorem ("teorema impossible") conditions, as data:
    [P,Q] = x + g(y); en_{3,-1}(P) = st_{1,0}(P) = (6,16);
    st_{-1,1}(P) = en_{1,0}(P) = (6,18);
    en_{3,-1}(Q) = st_{1,0}(Q) = (9,24);
    st_{-1,1}(Q) = en_{1,0}(Q) = (9,27). -/
def thm5_en_P : Nat × Nat := (6, 16)
def thm5_en_Q : Nat × Nat := (9, 24)
def thm5_st_P : Nat × Nat := (6, 18)
def thm5_st_Q : Nat × Nat := (9, 27)

/-- §5 C-expansion shape (Prop. "calculo de C"), recorded:
    P = C^2, Q = C^3 + α_2 C^2 + α_1 C + α_0 + α_{-1} C^{-1} + F,
    with v_{1,0}(F) = -4. The existence of C, F with these
    properties is INTERFACE (needs Laurent-series algebra). -/
def thm5_vF : Int := -4

/-- §5 degree bounds from the paper's endgame, kernel-checked:
    12 + 9*7 = 75 and 22 + 8 + 42 + 4 = 76. -/
theorem thm5_bounds : (12 + 9 * 7 = 75 ∧ 22 + 8 + 42 + 4 = 76) := by
  decide

/-- §5: deg((y+1)^66 g(y)^3) = 78 forces deg g = 4, since
    66 + 3 * deg g = 78. -/
theorem thm5_g_degree : 66 + 3 * 4 = 78 := by rfl

/-- §5 endgame, conditionally: if the principal equation
    equates a degree-78 term with terms bounded by 75 and
    76, that is impossible. Stated with the bounds as
    hypotheses so the conditionality is explicit. -/
theorem thm5_endgame (h78 : Nat) (h_bound : h78 ≤ 76) (h_eq : h78 = 78) :
    False := by
  rw [h_eq] at h_bound
  exact absurd h_bound (by decide : ¬ (78 : Nat) ≤ 76)

/-- §5 Corollary (Corollary 5.7 in the map's numbering):
    no P, Q with [P,Q] = x and the (9,27) Newton shapes
    of Prop. 4.1. This follows from Thm 5.1 plus the
    Succ/ψ argument in the paper's proof, which is
    INTERFACE here (it needs the (m,n)-pair machinery
    of [GGV1] Def. 4.3 / Cor. 7.2). Recorded as the
    corollary's shapes, not as a proved corollary. -/
def cor57_P : List (Nat × Nat) := [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)]
def cor57_Q : List (Nat × Nat) := [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)]

/-- §6 Theorem ("teorema impossible para 7") conditions, as data:
    [P,Q] = x; N(P) = {(0,0),(4,0),(2,6),(0,14)};
    N(Q) = {(0,0),(6,0),(3,9),(0,21)}. -/
def thm6_P : List (Nat × Nat) := [(0, 0), (4, 0), (2, 6), (0, 14)]
def thm6_Q : List (Nat × Nat) := [(0, 0), (6, 0), (3, 9), (0, 21)]

/-- §6 principal equation degrees: with d_{-1} = α y^k,
    deg d_0 = 9, deg d_1 = 6, the three terms have degrees
    15 + 6k, 27, 9 + 9k. At k = 2 all three are 27. -/
theorem thm6_principal_degrees_at_k2 :
    (15 + 6 * 2 = 27 ∧ 9 + 9 * 2 = 27) := by
  decide

/- §6: the paper's final step — (27 α^9 d_0 - 2 y^9)^2 /
    (108 α^10) = α^3 y^8 - 2λ y^10, whose right side is not
    a square of a polynomial for α, λ ≠ 0 — is INTERFACE
    (needs polynomial square / degree-in-y arguments in a
    polynomial algebra library). No non-square theorem is
    claimed here. -/

/-- §6 C-expansion shape (Prop. "calculo de C para 7"),
    recorded: C, F ∈ K[y, y^{-1}]((x^{-1})),
    v_{1,0}(F) = -4, same α-coefficient shape as §5.
    Existence is INTERFACE. -/
def thm6_vF : Int := -4

end Part4
end GGHV
end JC2
