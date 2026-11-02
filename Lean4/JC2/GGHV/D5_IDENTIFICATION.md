# D5 — Helali ↔ branch-(c) identification check (2026-10-30)

Status: **COMPLETE as an identification (2026-10-30, updates 2–4 below); programmes NOT merged.** This document records
what was verified term-by-term from the sources themselves, and
what remains open. The updates below identify the two systems at the equation level (see updates 2–4).

## Sources checked

- Helali, "Exact Computer-Assisted Exclusion of the (72,108)
  Frontier", repo TeX:
  `~/workspace/research/jc2-72-108-exact-certificates/paper/jc2_72_108_exact_exclusion.tex`
  (§"The planar (72,108) frontier", §"Exact Laurent reduction").
- GGHV Part 3 data in this directory:
  `Part3_NewtonReductions.lean` (`prop43_P1/Q1`, `prop43_P2/Q2`).
- Brandon's branch-(c) README:
  `~/workspace/research/2D-Jacobian-Conjecture-Workspace/JC2D-branches_a_b_c_unified/branch_c/README.md`.

## MATCHED (verified from the texts)

1. **Newton configurations.** Helali Case 1:
   N(P) = conv{(0,0),(1,0),(8,14),(8,16),(0,8)},
   N(Q) = conv{(0,0),(2,1),(12,21),(12,24),(0,12)};
   Case 2 is the same without (0,8)/(0,12). These are
   exactly GGHV Prop. 4.3 case 1 / case 2, and exactly
   Part 3's `prop43_P1/Q1` and `prop43_P2/Q2` vertex lists.
2. **Bracket type.** Helali: P, Q ∈ K[x, x⁻¹, y] over an
   algebraically closed characteristic-zero field, with
   [P, Q] = x². That is GGHV Prop. 4.3's (8,28) case
   statement, not a new bracket type.
3. **Descent field polynomial.** Helali's descent field is
   L = ℚ[w]/(w⁵ − w⁴ + 3w³ + 3w² + 26) (TeX §"Exact Laurent
   reduction", after J4 and the degree-35 polynomial
   H(a₇)). This is the same polynomial as Brandon's
   branch-(c) K₅. Same polynomial ⇒ same field
   presentation; it does NOT by itself identify the two
   systems built over that field (see below).
4. **Helali's own logical boundary.** Helali states it
   himself: his computation proves identities for the
   systems obtained from these two polygonal cases, and
   promoting them to a theorem about all plane maps
   requires the GGHV reduction to be exhaustive and the
   local transcription/normalization to be exact.
   Helali does not claim an identification with Brandon's
   branch-(c) system.

## NOT MATCHED / OPEN (the identification itself)

a. **λ normalization.** Brandon's branch (c) is "GGHV
   normal form (1)" with conclusion
   ¬∃ P Q λ, λ ≠ 0 ∧ NewtonNFc P Q ∧ [P, Q] = λx²
   (branch-(c) README, format map). Helali fixes λ = 1.
   Passing between λ ≠ 0 and λ = 1 needs a scaling
   argument that preserves both the Newton configurations
   and Helali's normalized vertex coefficients — plausible
   (coefficient scaling does not change supports), but
   NOT proved here and not assumed.
b. **Normal forms.** Brandon's system is stated in terms
   of his NewtonNFc normal form; Helali's is stated in
   terms of the substitution t = xy², z = y⁻¹, the upper
   bands P = A(t)z² + B(t)z + C(t),
   Q = D(t)z³ + E(t)z² + F(t)z + G(t), the five bracket
   equations J4..J0, and normalized A, D
   (A = t + a₂t² + … + a₇t⁷ + t⁸, D = d₂t² + … + d₁₂t¹²).
   Whether NewtonNFc and Helali's normalized reduction
   are the same normal form has NOT been checked
   term-by-term.
c. **Certificate mechanisms differ.** Brandon's branch-(c)
   closure is a Macaulay-matrix rank argument (grade B,
   mod 1000003 and mod 32003, two implementations);
   Helali's is exact Gröbner/FGLM descent plus explicit
   certificate identities over L (Case 2 unit certificate,
   Case 1 hard identity). These prove different
   statements about different systems; their equivalence
   is exactly the open identification, not a consequence
   of the shared field polynomial.

## Licensed next step (unchanged)

The D5 identification check itself — items (a) and (b)
above, term by term — not a merge. Until (a) and (b) are
proved, Helali's exclusion and Brandon's branch-(c)
closure must be cited as separate results about
separately stated systems that share a field polynomial
and Newton configurations.

## UPDATE 2026-10-30 (second check, against Brandon's Lean sources)

Sources: `branch_c/bundle_v3_1/jacobian_lean/Jacobian/BranchC/
DescentClaim.lean` (`NewtonNFc`, `DescentClaimC`),
`Degree19.lean` (`inNPc`, `inNQc`, `layerTermZ`),
`LayersGen.lean` (`EIdent`, `layers_of_jac_c`).

### (a) λ: RESOLVED at the NewtonNFc level

`NewtonNFc P Q` is: supports in N(P), N(Q), plus all ten
vertex coefficients nonzero — no coefficient is fixed to
any value. Scaling (P, Q) ↦ (αP, βQ) with αβ = 1/λ
preserves supports and vertex-nonvanishing (λ ≠ 0), and
turns [P, Q] = λx² into [αP, βQ] = x². So the λ ≠ 0 vs
λ = 1 difference is NOT an obstruction to identifying
the systems. What remains open under (a) is only the
stronger coefficient normalization below.

### (b) Normal forms: IDENTIFIED at the polygon/layer level

- `inNPc` / `inNQc` are documented in the Lean source
  itself as conv{(0,0),(1,0),(8,14),(8,16),(0,8)} and
  conv{(0,0),(2,1),(12,21),(12,24),(0,12)} — exactly
  Helali Case 1. **Brandon's branch (c) is Helali Case 1,
  not Case 2**: `NewtonNFc` requires the (0,8) and
  (0,12) vertex coefficients nonzero, which Case 2
  excludes. Case 2 is a separate system with no
  branch-(c) counterpart.
- Variables: Brandon's `layerZ` monomial xⁱy^{2i−k} is
  tⁱzᵏ with t = xy², z = y⁻¹ — Helali's substitution.
  P's bands A, B, C are layers k = 2, 1, 0; Q's bands
  D, E, F, G are layers l = 3, 2, 1, 0.
- Equations, term by term: `layerTermZ a b A B =
  a·A·B′ − b·A′·B` (`Degree19.lean`), and `EIdent`
  sums layer terms over k + l = n with RHS
  [n = 5]·λu². Helali's J4..J0 are exactly `EIdent`
  at n = 5, 4, 3, 2, 1 (lam scaled to 1 by (a)):
  J4 = LT_{2,3}(A,D) = 2AD′ − 3A′D = t²;
  J3 = LT_{2,2}(A,E) + LT_{1,3}(B,D);
  J2 = LT_{2,1}(A,F) + LT_{1,2}(B,E) + LT_{0,3}(C,D);
  J1 = LT_{2,0}(A,G) + LT_{1,1}(B,F) + LT_{0,2}(C,E);
  J0 = LT_{1,0}(B,G) + LT_{0,1}(C,F).
  All eleven bracket terms match, coefficients included.
  `layers_of_jac_c` proves these layer identities from
  J(P,Q) = λx² for NewtonNFc pairs, over any field —
  and `DescentClaimC` quantifies over w with
  w⁵ − w⁴ + 3w³ + 3w² + 26 = 0, i.e. Helali's field L
  in the same presentation.

### What D5 identification now is, precisely

IDENTIFIED: Helali Case 1's J-system = Brandon's
branch-(c) `EIdent` system (n = 1..5, λ scaled to 1),
for NewtonNFc pairs over L. STILL OPEN, and now the
only open parts: (i) Helali's A/D coefficient
normalization (A = t + a₂t² + … + a₇t⁷ + t⁸, with the
t and t⁸ coefficients fixed to 1) against Brandon's
weighted scaling (τ^{2−k}, τ^{3−l}) and torus transport
(`eIdent_transport`) — the scalings exist in Brandon's
file, but deriving Helali's exact normalization from
them is not proved here; (ii) Helali Case 2, which is
outside branch (c) entirely; (iii) certificate
mechanisms, which are proofs about the identified
system, not the system itself (Helali Gröbner/FGLM
identities vs Brandon's DescentClaimC/Macaulay-rank
argument — different proofs, same equations at the
Case 1 / EIdent level).

## UPDATE 2026-10-30 (third check — D5(i) normalization, CLOSED mathematically)

Claim: over an algebraically closed field K of
characteristic 0, every NewtonNFc pair (P, Q) with
[P, Q] = λx², λ ≠ 0, can be scaled to Helali's
normalized form, so (i) is not an obstruction to the
identification. Proof, step by step (mathematical
argument; Lean formalization of the polynomial-layer
steps is pending on D2/D4-item-1 polynomial theory,
stated honestly below):

1. Bracket scaling (λ = 1). Replace (P, Q) by
   (αP, βQ) with αβ = 1/λ (e.g. α = 1, β = 1/λ).
   Supports and vertex-nonvanishing are unchanged
   (nonzero scalars), so NewtonNFc is preserved, and
   [αP, βQ] = αβλx² = x².
2. Layer identification. P's k = 2 layer A₂(t) is
   Σ cᵢtⁱ over monomials xⁱy^{2i−2} in N(P): i ≥ 1
   (j = 2i − 2 ≥ 0), i ≤ 8, so A₂(t) = c₁t + … + c₈t⁸
   with c₁ = coeff of (1,0) ≠ 0 and c₈ = coeff of
   (8,14) ≠ 0, both by NewtonNFc. Q's l = 3 layer
   D(t) = d₂t² + … + d₁₂t¹² with d₂, d₁₂ ≠ 0
   (vertices (2,1), (12,21)); Helali imposes no fixed
   values on D's coefficients, only its support.
3. Torus normalization of A. Replace t by κt (the
   torus transport `sc κ` in Brandon's file) and scale
   P by α: A₂ becomes α·(c₁κt + … + c₈κ⁸t⁸).
   Choose κ with κ⁷ = c₁/c₈ — possible because K is
   algebraically closed and c₁, c₈ ≠ 0 — and
   α = 1/(κc₁). Then the t-coefficient is
   αc₁κ = 1 and the t⁸-coefficient is
   αc₈κ⁸ = (c₈κ⁸)/(κc₁) = (c₈/c₁)κ⁷ = 1.
   So A₂(t) = t + a₂t² + … + a₇t⁷ + t⁸, exactly
   Helali's normalized A. D's coefficients change
   by the torus/scaling factors but D has no fixed
   coefficients to preserve, and its support is
   unchanged. The other layers' coefficients are
   likewise unconstrained by Helali's normalization.
   (Brandon's weighted scaling τ^{2−k} is not needed
   for A itself, since k = 2 gives τ⁰ = 1; it is the
   tool that fixes the top layer in DescentClaimC.)
4. Field caveat, stated plainly: step 3 needs a 7th
   root of c₁/c₈, so it is proved over algebraically
   closed K (Helali's setting), not over the specific
   field L = ℚ[w]/(w⁵ − w⁴ + 3w³ + 3w² + 26)
   (Brandon's DescentClaimC setting), where such a
   root need not exist. The identification of the
   equation systems therefore holds in Helali's
   setting; Brandon's L-specific certificate
   (DescentClaimC/Macaulay rank) is a separate proof
   about the L-version of the system, and its top-layer
   normalization (t₂ = 1) is a different, L-internal
   scaling. Do not conflate the two normalizations.

With (i) closed mathematically, D5's remaining open
parts are: (ii) Case 2 (separate system, see below)
and (iii) certificate mechanisms (different proofs).
The Lean formalization of steps 1–3 (polynomial
layers, torus/scaling transport at the coefficient
level) is NOT done here — it needs the D2 polynomial
bracket/layer theory and D4-item-1 ℓ theory, which
are the open formalization items, not the
identification question.

## UPDATE 2026-10-30 (fourth check — D5(ii) Case 2, CLOSED;
## D5 as an identification is now COMPLETE)

Source: `branches_a_b/lean/Jacobian/BranchAbNewton.lean`
(`NewtonNF2`, `layerPoly`, `layerPiece`) and
`BranchAbMain.lean` (`main_theorem_of_classification`).

- Case 2 HAS a Brandon counterpart, and it is not
  branch (c): it is Brandon's normal form (2), the
  branch (a,b) package. `NewtonNF2 P Q` is supports
  in conv{(0,0),(1,0),(8,14),(8,16)} /
  conv{(0,0),(2,1),(12,21),(12,24)} plus the eight
  vertex coefficients nonzero — exactly Helali Case 2.
  `main_theorem_of_classification` eliminates
  NewtonNF2 pairs with [P, Q] = λx², λ ≠ 0, over
  characteristic-zero fields where
  `TopLayerClassification` holds (for ℂ, GGHV
  Prop. 6.1; the statement itself notes GGHV Prop. 4.3
  is not part of it). The branch (a,b) elimination
  recorded as Grade A is this package's main theorem.
- Scope caveat, stated precisely (this corrects any
  reading of the earlier updates as claiming full-system
  identity): Helali's band form keeps only the upper
  bands (P: k = 2, 1, 0; Q: l = 3, 2, 1, 0), while
  Brandon's `EIdent` sums over ALL layers (branch (c):
  k ∈ [−8, 2], l ∈ [−12, 3], the negative layers coming
  from the (0,8)/(0,12) vertices). Helali's J4..J0 are
  therefore Brandon's `EIdent` at n = 5..1 restricted
  to the upper bands — a subsystem of Brandon's full
  system, not the whole of it. Helali's exclusion
  proves his band system unsatisfiable (in his
  normalization, over algebraically closed K);
  Brandon's eliminations prove the full systems
  unsatisfiable (Case 2 at Grade A modulo the
  classification premise; Case 1 at grade B via
  DescentClaimC). Same equations at the upper-band
  level, different settings (field, normalization) and
  different proofs.

D5 FINAL STATUS: the identification question is
closed. Both Helali cases are identified with Brandon
systems — Case 1 with branch-(c) NewtonNFc, Case 2
with branch-(a,b) NewtonNF2 — at the upper-band
equation level, with λ resolved by scaling and A
normalization proved over algebraically closed K.
What remains is NOT identification but comparison of
independent proofs about those systems, which is a
different task and is not D5.
