# D4 remaining work — split into parts with session estimates

D4 as a whole is the formalization of the cited [GGV*] theories behind Part 5's
`AssemblyPremises`. Item 1 at the support level is done (Part 13, face lists).
What remains is split below into parts. A "session" means one sustained work
turn of the size of the 2026-10-30 D1–D6 / D4–D5 runs (several hours of
Lean writing + compile cycles on this VM; Mathlib files add ~10–20 min per
build). Estimates are for the part as a whole, not promises: a part is done
only when its files compile and the correspondence is updated.

## Part A — Polynomial ℓ_{ρ,σ} (gateway, D1 remainder) — 3 sessions

- A1 (1 session): coefficient-carrying face terms for monomial lists:
  `faceTerms` (terms attaining maximal valuation, coefficients kept),
  membership / nonemptiness lemmas, concrete §5 faces with coefficients.
  Status: Part 14 written 2026-10-30 (this run), compiles standalone.
- A2 (1 session): face endpoints from face terms — DONE as Part 15
  (2026-10-30): endpoints lie in the face, attain maximal valuation,
  and match Part 8's §5 endpoint pairs under (3,−1) and (1,0); the
  (−1,1) endpoints on the Prop. 4.1 list are both (0,18). Note
  (clarified by Part 17, 2026-10-31): that list is Prop. 4.1's
  polygon, not Thm 5.1's §5 polygon, so this is not a contradiction
  with Thm 5.1; the paper's en/st definition itself is now given in
  Part 17 via the secondary-direction formula.
- A3 (1 session): Pred/Succ for general polygons + maximal segments
  beyond the §5 shapes (generalizing Part 8). Status: DONE as Part 16
  (2026-10-30): list-order Pred/Succ (first-occurrence decompositions,
  inverse in decomposition form), segment predecessor/successor
  neighbour theorems for arbitrary term lists, §5 segment neighbours,
  and a general (0,1)-face example. The paper's Pred/Succ and en/st
  from ℓ remain open (Part B, [GGV1]).

## Part B — [GGV1] direction/edge theory — 4 sessions

Instances actually used by Part 3/Part 5: Prop. 8.2, Cor. 7.4, Thm 7.6(5),
Prop. 2.11(3), Cor. 7.2, Def. 4.3, Props. 1.13/2.1. Each instance is a
separate formalization target; the theory is stated as hypotheses until
proved, never as axioms presented as progress.

- B session 1 DONE as Part 17 (2026-10-31): definitions layer
  (V/V_{>0}, homogeneous term lists, st/en via the secondary-direction
  formula, cross product), sourced from the [GGV1] TeX (arXiv:1401.1784).
- B session 2 DONE as Part 18 (2026-10-31): Prop. 8.2 instance layer
  (numbering pin: GGHV Prop. 8.2 = TeX "esquina de 83" item (2);
  proportionality, k-family non-proportionality, k = 1 instance,
  item (2) as a hypothesis bundle).
- B session 3 DONE as Part 19 (2026-10-31): Cor. 7.4 / Thm 7.6(5)
  instance layer (see README), with the condition-(3) open question
  recorded.
- B session 4 DONE as Part 20 (2026-10-31): remaining [GGV1]
  instances + Pred/Succ from ℓ (see README). Part B COMPLETE.
  Still open from Part B (carried forward, not closed by Part B):
  proof of Prop. 8.2 item (2), k = 2 exclusion, Cor. 7.4
  condition-(3) question (published-text check), full Dir/Succ
  theory (Succ uniqueness, consecutive directions < 180°).

## Part C — [GGV2] corner theory — 4 sessions

Prop. 3.29 (§3-120 last-corner argument), Prop. 3.12 (Prop. 4.2 algorithm
setting), Def. 3.21, Remark 3.31. Includes formalizing the Prop. 4.2
algorithm as a verified computation, not a transcription.

- C session 1 DONE as Part 21 (2026-10-31): corner-condition
  instance layer (see README). [GGV2] itself (J. Algebra 471
  (2017) 13–74) is not among the six TeX sources; conditions are
  as cited in 1605.09430/1708.07936.
- C session 2 DONE as Part 22 (2026-10-31): Prop. 3.12 / Def. 3.21
  / Remark 3.31 as cited (see README).
- C session 3 DONE as Part 23 (2026-10-31):
  PossibleStartingPoints as a verified computation (see README).
- C session 4 DONE as Part 24 (2026-10-31): [GGV2]'s own text
  checked (arXiv:1605.09430 — corrected identification), the
  orientation identity proved in general. Part C COMPLETE.
  (Remark 3.31 not located as a separate TeX remark; its pin
  remains citation-level.)

## Part D — [GGV6] root theory — 3 sessions

Thm 7.3 (I_M ≥ I_m — the instance behind Part 2's `discard_84`
hypothesis), Props. 6.4/6.6, Ex. 6.7 (π-roots, major/minor roots,
δ-values). Closing this part is what first discharges a Part 5 premise.

- D session 1 DONE as Part 25 (2026-10-31): root-theory instance
  layer (see README).
- D session 2 DONE as Part 26 (2026-10-31): Props. 6.4/6.6,
  Ex. 6.7 instance layer (see README).
- D session 3 DONE as Part 27 (2026-10-31): Prop. 2.5 instance
  as cited (TeX analogue not located; carried bundle).
  Part D COMPLETE.

## Part E — [GGV5] enumeration — 5 sessions (largest single part)

The §2 premise: every counterexample below degree 125 lies in one of the
10 table rows ([GGV5] §§5–6). This is the largest formalization target
in D4 and the least decomposable; split internally by table row if a
single session stalls.

- E session 1 DONE as Part 28 (2026-10-31): the §2 table as data.
- E session 2 DONE as Part 29 (2026-10-31): PLLC/PFL first stage
  (filter + direction assignment) as a verified computation.
- E session 3 DONE as Part 30 (2026-10-31): PFL loop stage.
- E session 4 DONE as Part 31 (2026-10-31): row-to-degree
  computation.
- E session 5 DONE as Part 32 (2026-10-31): degree pairs +
  source count. Part E COMPLETE.

## Part F — Premise replacement in Part 5 — 2 sessions

One `AssemblyPremises` field at a time, replaced by the proved instance
from Parts B–E, with `lake build` re-run after each replacement.
Part 5's Theorem 2.1 becomes unconditional only when the last field is
replaced; until then every intermediate state stays CONDITIONAL and is
recorded as such.

- F session 1 DONE as Part 33 (2026-10-31): discharge ledger +
  survivor computation.
- F session 2 DONE as Part 34 (2026-10-31): reduced structure
  + `assemble`, installed additively into Part 5 (standalone
  compile + lake build PASS). Part F COMPLETE.

## D4 COMPLETE (2026-10-31)

All 21 sessions done (Parts 13–34, with Part A = 14–16, B = 17–20,
C = 21–24, D = 25–27, E = 28–32, F = 33–34 + Part 5 edit). D4 is
complete AS A FORMALIZATION PROGRAMME: every cited instance is
formalized at data/arithmetic level, the premise structure is
reduced 7 → 5 + 2 bundles, and the survivor is computed. It is
NOT a proof of Theorem 2.1 (still CONDITIONAL), moves no grade,
and leaves A1/A2 as the programme priority.

## Totals

Parts A–F: 3 + 4 + 4 + 3 + 5 + 2 = **21 sessions** estimated.
Order is dependency order: A, then B/C/D in parallel where independent
(B needs A; C needs A; D needs A+B), then E, then F. No part's estimate
includes Mathlib build-queue time beyond one full `lake build` per part.
