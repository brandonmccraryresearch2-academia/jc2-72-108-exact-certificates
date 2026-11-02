# D4 — Cited [GGV*] results: instance status (2026-10-30)

Status: **OPEN — not formalized.** This document lists each
cited result, the exact instance this formalization uses,
and what formalizing it would require. Nothing here closes
D4; formalizing these results is a programme of its own
(they are separate papers' theorems, not lemmas of GGHV
2022 itself).

## What is NOT the cited theorem (do not confuse)

The kernel-checked arithmetic in Parts 1–6 (gcd(2,7) = 1,
(3/2) and (3/4) scaling by cross-multiplication, degree
bounds 75/76 vs 78, §6 degrees at k = 2, direction
valuations, I_M = 4 / I_m = 5 as numbers) is arithmetic
about the *inputs* to the cited theorems. It is not the
cited theorems themselves, and must not be cited as them.

## Cited results and their instances

- **[GGV6] Thm 7.3** — used in Part 2 (`discard_84`) as an
  explicit hypothesis: I_M ≥ I_m, applied at the §3-84
  numbers I_M = 4, I_m = 5. Formalizing it needs [GGV6]'s
  π-root / major–minor root theory (major roots at
  A₁ = (11/7,2), minor roots at A₁ = (9/7,1), δ-values).
- **[GGV6] Props. 6.4 / 6.6, Ex. 6.7** — §3-84 minor/major
  root data (one final minor π-root τ, δ_τ = −3; λ^Q = 1/7
  at k = 1, l = 7). Same theory as above.
- **[GGV6] Prop. 2.5** — Prop. 4.3 instance:
  Pred_P(1,0) ∈ {(1,−2), (1,−3)}. Needs Pred theory (D1).
- **[GGV1] Prop. 8.2** — Props. 4.1/4.3 instance: k = 1
  gives (en(Q), en(P)) = ((2,1), (−1,0)); k = 2 impossible
  (edges not parallel). Needs [GGV1] direction/edge theory.
- **[GGV1] Cor. 7.4** — Props. 4.2/4.3 instances:
  (ρ₀,σ₀) = (−1,3), l = 1, (a/l, b) = (24,9), q = 3 (Prop.
  4.2); (−1,4), q = 4, en(R) = (7,2) (Prop. 4.3). Needs
  [GGV1] ℓ_{ρ,σ} theory (D1/D2).
- **[GGV1] Thm 7.6(5)** — §3-120 instance: q₁ = 4
  (q₁ = 4 | d₀), d₀ ≤ 4 from st_{1,0}(P) = (8,28) = 4·(2,7).
  Needs [GGV1] corner theory.
- **[GGV1] Prop. 2.11(3), Cor. 7.2, Def. 4.3, Props. 1.13/2.1**
  — §3-84 ℓ form, §5 corollary ψ argument (x ↦ x^{1/2},
  (m,n)-pair machinery). Needs [GGV1] homogeneous-part
  theory.
- **[GGV2] Prop. 3.29, Prop. 3.12, Def. 3.21, Remark 3.31**
  — §3-120 last-corner argument; Prop. 4.2 algorithm
  setting (`PossibleStartingPoints`, l = 1, a = 8, b = 3,
  Pred_P(1,0) ∈ {(1,−2), (2,−5)}); §2 note on (8,32).
  Needs [GGV2] Newton-polygon / corner theory, and the
  algorithm itself must be formalized as a verified
  computation, not transcribed.
- **[GGV5] enumeration** — §2 premise: every
  counterexample with max degree < 125 lies in one of
  the 10 table rows ([GGV5] §§5–6). This is the
  enumeration premise of Part 5's `AssemblyPremises`;
  formalizing it needs [GGV5] in full.

## Consequence for the assembly

Part 5's Theorem 2.1 remains CONDITIONAL on these
instances (as explicit `AssemblyPremises` fields). D4
closes only when each instance above is a proved Lean
theorem (or the general cited theorem is), at which point
the corresponding premise field can be replaced by the
proof. No premise field has been replaced in this run.
