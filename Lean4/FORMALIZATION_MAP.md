# Lean 4 formalization map — the (72,108) frontier papers

**Status: MAP ONLY, 2026-10-29.** Nothing in this folder proves anything.
Every paper statement below is listed as a target with its dependencies and
its difficulty; statements taken as inputs are marked `INTERFACE` (assumed,
not proved, in the phase that uses them). No grade in Brandon's programme
moves because of this map. The repo paper's own conclusion is conditional,
and this map preserves that conditional exactly.

## 1. Which "entire paper" this map covers

Two papers, in dependency order, because the repo paper cannot be stated
without the first:

1. **GGHV 2022** — Guccione, Guccione, Horruitiner, Valqui,
   "Increasing the degree of a possible counterexample to the Jacobian
   Conjecture from 100 to 108", arXiv:2204.14178v1.
   Uploaded PDF read 2026-10-29 (42 pages; pages 2, 8, 11, 16, 17, 33 are
   figures only and were not text-read — they carry no theorem statements
   in the text layer, but figure contents are unchecked).
2. **Helali 2026-07-21** — Billel Helali, "Exact Computer-Assisted
   Exclusion of the (72,108) Frontier in the Two-Dimensional Jacobian
   Problem" (`paper/jc2_72_108_exact_exclusion.tex` in the uploaded
   v1.0.1 zip; Codex-assisted, per its own disclosure).
   This is the paper in the repo being cloned
   (`brandonmccraryresearch2-academia/jc2-72-108-exact-certificates`).
   Its README states its own boundary verbatim in substance: the
   computation excludes both *transcribed* coefficient systems, and the
   conclusion that (72,108) is impossible "remains conditional on the
   correctness and exhaustiveness of the published reduction and on its
   faithful transcription. This is not a proof of the full two-dimensional
   Jacobian conjecture."

Formalization is therefore split into phases, and the phases must not be
collapsed: **Phase 1** formalizes Helali's conditional exclusion with
GGHV Prop. 4.3 as an interface hypothesis. **Phase 2** formalizes GGHV
itself. Only Phase 1 + Phase 2 together would give an unconditional
Lean statement "no plane counterexample of degree pair (72,108)" — and
even that is *not* JC(2), which also needs all degrees ≥ 125.

## 2. The logical spine (what must be proved, in order)

```
Keller pair (P,Q), [P,Q] ∈ Kˣ, char K = 0, K alg. closed
  └─ GGHV Thm 2.1 (Phase 2): max(deg P, deg Q) ≥ 125
     or (deg P, deg Q) ∈ {(72,108), (108,72)}
  └─ GGHV Prop. 4.3, case (8,28) (Phase 2 → Phase 1 interface):
     a (72,108) counterexample yields P,Q ∈ K[x,x⁻¹,y] with [P,Q] = x²
     in exactly one of two Newton configurations:
       Case 1: N(P)=conv{(0,0),(1,0),(8,14),(8,16),(0,8)},
               N(Q)=conv{(0,0),(2,1),(12,21),(12,24),(0,12)}
       Case 2: N(P)=conv{(0,0),(1,0),(8,14),(8,16)},
               N(Q)=conv{(0,0),(2,1),(12,21),(12,24)}
  └─ Helali Thm (Phase 1): both transcribed Case 1 / Case 2 coefficient
     systems over ℚ (in fact over L, below) have no solution
  └─ Helali Cor. (conditional): IF Prop. 4.3 is exhaustive AND the
     transcription/normalization is faithful, THEN (72,108) is impossible
     and every hypothetical plane counterexample has max degree ≥ 125.
```

## 3. Phase 1 module map — Helali, section by section

### 3.0 `DimSplit.lean` — §1–§2, the dimensional split [EASY, do first]
- Statement: Alpöge's map F = (P,Q,R) with
  P = (1+xy)³z + y²(1+xy)(4+3xy),
  Q = y + 3x(1+xy)²z + 3xy²(4+3xy),
  R = 2x − 3x²y − x³z,
  has det JF = −2 (degrees (7,6,4)) and
  F(0,0,−1/4) = F(1,−3/2,13/2) = F(−1,3/2,13/2) = (−1/4,0,0).
- Lean content: pure `MvPolynomial` expansion + evaluation. This is the
  only part of the paper that is a short, self-contained kernel check.
  It was already verified in Singular on 2026-10-21 (det −2, same
  collision set) — that Singular check is *not* a Lean check.
- Then: adjoining identity coordinates gives JC(n) false for n ≥ 3.
  This needs no input from GGHV and does not touch JC(2).

### 3.1 `Frontier.lean` — §3, the statement interface [INTERFACE]
- Definitions: Newton polygon `N(P)` as convex hull of support in ℕ²
  (here, in the Laurent ring, support in ℤ × ℕ), Jacobian bracket
  `[P,Q] = P_x Q_y − P_y Q_x` on `K[X, X⁻¹, Y]`.
- `axiom`/`hypothesis` (labelled INTERFACE, not proved in Phase 1):
  GGHV Prop. 4.3 as above, in the exact vertex lists. The two cases
  differ only by the extra vertices (0,8) / (0,12) in Case 1.
- Hard part, deferred to Phase 2: the passage polynomial → Laurent,
  the automorphisms φ(x)=x⁻¹, φ(y)=x⁴y, and the bracket rescaling
  [φ(P),φ(Q)] = −[P,Q]·x². Each of those is a formalizable computation
  *once* the GGHV direction machinery exists; it is not free.

### 3.2 `LaurentReduction.lean` — §4 [MEDIUM-HARD]
- Change of variables t = x·y², z = y⁻¹, with [t,z] = −1 (coordinate
  bracket in x,y) and x² = t²z⁴. Lean needs: Laurent polynomial ring,
  the bracket as a derivation-pair, and the band decompositions
  P = A(t)z² + B(t)z + C(t), Q = D(t)z³ + E(t)z² + F(t)z + G(t).
- The five coefficient equations J4..J0, exactly as in the paper:
  J4: 2AD′ − 3A′D = t²
  J3: 2(AE′ − A′E) + (BD′ − 3B′D) = 0
  J2: (2AF′ − A′F) + (BE′ − 2B′E) − 3C′D = 0
  J1: 2AG′ + (BF′ − B′F) − 2C′E = 0
  J0: BG′ − C′F = 0
  (primes = d/dt). These are identities to be *proved by expansion*
  from [P,Q] = x², not assumed.
- Normal forms: A = t + a₂t² + … + a₇t⁷ + t⁸,
  D = d₂t² + … + d₁₂t¹² (nonzero vertex coefficients normalized).
  J4 solves the 11 coefficients of D and leaves 6 compatibility
  equations in a₂..a₇.
- **The first genuinely hard formalization step:** "exact rational
  Gröbner and FGLM calculations yield an irreducible degree-35
  polynomial H(a₇) together with five relations linear in a₂..a₆",
  and the descent to L = ℚ[w]/(w⁵ − w⁴ + 3w³ + 3w² + 26).
  In Lean this cannot be "Gröbner said so": it needs either a
  verified Gröbner implementation, or the output (H, the five linear
  relations, and the descent data) stated as explicit polynomials with
  the elimination identities checked by expansion. The replay scripts
  (`firstblock_*`, `case1_descent_checkpoint.py`, lex relations,
  "LEX_relations 6 H_degree 35 H_terms 6, H_irreducible_Q True" in
  `verify_all_final.out`) are the place to mine those explicit data —
  they are not yet extracted into this map.

### 3.3 `Case2.lean` — §5, Case 2 [MEDIUM, certificate-shaped]
- Input: exact elimination in J3..J0 leaves four residual generators
  R₁..R₄ over a degree-35 field.
- Certificate to formalize: a Macaulay system of degree 8, dimensions
  165×182, producing exact multipliers with
  1 = T₁R₁ + T₂R₂ + T₃R₃ + T₄R₄.
- Lean strategy: import the multipliers as *data* (from
  `case2_exact_certificate.pkl`, re-serialized to a Lean-readable
  format), then prove `1 = Σ TᵢRᵢ` by expansion over the number
  field. The certificate file itself is not a proof; the Lean proof is
  the expansion check. Hashes in `verification/RECONSTRUCTED_CERTIFICATES.sha256`
  must be re-checked on import (case2 certificate SHA-256
  cfbc3c39… in the paper's table).
- Consequence, elementary: the Rᵢ have no common zero, so Case 2
  has no solution. This step is the template for all certificate
  modules: *data + expansion check*, never "the pickle says pass".

### 3.4 `Case1Branching.lean` — §5, Case 1 branching [HARD]
- Input: the negative z-bands produce 13 compatibility equations.
  Their first factorization forces the exhaustive split s = c or
  s = −c, c ≠ 0. Lean must prove exhaustiveness of the split
  (a factorization identity), not merely assert the two branches.
- In each branch, a checked relation E₆ − λE₂ = S·Λ², S ≠ 0,
  forces an affine-linear form Λ to vanish, eliminating one variable
  "without division by a variable expression". Formalizing this needs
  the elimination step as an explicit substitution + verification that
  no solution is lost — the paper's warning about pre-division
  equations (below) is the point to get right.

### 3.5 `Case1HZero.lean` — §5, the h = 0 specialization [MEDIUM]
- For h = 0, exact unit-ideal certificates, separately per branch,
  using the seven *pre-division* equations: 1 = Σ AᵢEᵢ|_{h=0}.
- Lean strategy: same as Case 2 (data + expansion), with the
  additional bookkeeping that the equations used are the pre-division
  ones. Certificate hashes: h0_branch1 664de005…, h0  d7844c2f….
- Consequence: neither branch has a solution with h = 0.

### 3.6 `HardCertificate.lean` — §5–§6, the hard identity [HARDEST, size-bound]
- For branch s = c, four reduced generators in L[h,u₁,u₂] admit
  h = T₁E₁ + T₂E₂ + T₃E₃ + T₄E₄.
  Hence every common zero satisfies h = 0, which §3.5 excludes.
- Construction data (paper §6): multiplier ansatz 385 coefficients
  in L, 402 coefficient equations in L, i.e. a rational linear system
  of **2010 equations in 1925 unknowns**. A fixed 1925×1925 minor,
  selected by exact elimination mod 71, has det ≡ 10 (mod 71), hence
  is nonsingular over ℚ. The FLINT solution has 1925 nonzero rational
  coordinates; largest numerator 85,342 bits, largest denominator
  85,275 bits; serialized identity 89,105,967 bytes
  (SHA-256 0e48ffab…).
- Lean strategy, and its limits — read before attempting:
  1. Do NOT try to state the 89 MB identity as a Lean term by hand,
     and do NOT let the kernel re-solve the system. Import the
     multipliers as data, verify the minor's determinant mod 71
     (cheap, and it justifies the *selection*), then verify the full
     identity by substitution into all 402 equations over L
     (equivalently all 2010 rational rows). That check is the proof.
  2. The independent gmpy2 verifier (13,410 coefficient-field
     products = 335,250 scalar products) is a *second implementation*,
     i.e. HLRE I1 at best, not a Lean kernel check. A Lean expansion
     check would be the kernel-level version; its feasibility at
     85k-bit rationals × 2010 rows must be benchmarked before
     promising it — `decide` will not do this, and `native_decide`
     is not a kernel proof. If the kernel check is infeasible, the
     honest statement is: "certificate data verified by two exact
     implementations outside Lean; Lean formalization stops at the
     certificate *interface* (the identity as a hypothesis with its
     hash)". Do not blur that line.
  3. The replay's `verify_all.sh` terminal markers
     (ALL_SERIALIZED_EXACT_CERTIFICATES_PASS, GMPY2_EXACT_PASS,
     SYSTEM_SYMMETRY_PASS, BRANCH1/2_EXACT_IDENTITY_PASS,
     JC2_72_108_EXACT_REPLAY_PASS) are *not* Lean theorems and must
     never be quoted as such.

### 3.7 `Symmetry.lean` — §5, branch transport [EASY-MEDIUM]
- Involution (h,u₁,u₂) ↦ (h,−u₁,−u₂) transports the equations and
  the hard identity exactly to s = −c. Lean: polynomial substitution
  + expansion check; the replay already evaluates this as a polynomial
  identity rather than inferring it from dimensions — copy that
  discipline.
- Assembly: Case 2 empty (§3.3) + Case 1 both branches empty
  (§3.4–§3.7) = Helali's theorem: the two transcribed systems have
  no solutions. Then the conditional corollary (§2 spine) with the
  interface hypothesis from §3.1 made explicit in the theorem
  statement — never dropped.

## 4. Phase 2 module map — GGHV 2022, section by section

GGHV is the *larger* formalization job, because it needs the whole
direction/Newton-polygon library that Helali's paper takes as input.
Do not start Phase 2 by formalizing Theorem 2.1's statement; start
with the library, in this order:

### 4.0 `Directions.lean` — the shared library [HARDEST, foundational]
Everything below depends on it, and it is also the library the six
Guccione papers (see synthesis) share:
- Weighted valuations v_{ρ,σ}, (ρ,σ)-homogeneous parts ℓ_{ρ,σ},
  start/end points st/en, directions Dir, Succ/Pred, "last possible
  corner", (m,n)-pairs, standard minimal pairs.
- The key lemmas used across GGHV: [6] Prop. 1.13 (bracket vs leading
  parts), Prop. 2.1 (powers / homogeneous elements), Cor. 7.4, Thm 7.6,
  Prop. 8.2 (the k-lemma used in Props. 4.1/4.3), and [4] Prop. 3.12
  (the [R,G] = R^i classification with its PossibleStartingPoints
  algorithm — that algorithm *is* formalizable as a terminating
  enumeration, unlike the CAS steps below).
- Note on sources: GGHV cites [6] = the shape paper (paper [6] in the
  synthesis list) and [4] = the lower-side paper (paper [4]) by
  theorem number; the arXiv versions read for this programme may
  number theorems differently from the journal versions. Every
  citation must be pinned to the version actually read.

### 4.1 `SmallCases.lean` — GGHV §2, Theorem 2.1's table [MEDIUM]
- The 10 cases from [1] §5–§6 tables, with (A₀,(m,n), max degree):
  (4,12),(3,4) → 64; (4,12),(5,7) → 112; (5,20),(2,3) → 75;
  (5,20),(3,2) → 75; (7,21),(2,3) → 84; (8,24),(2,3) → 96;
  (8,28),(3,2) → 108; (8,32),(3,2) → 120; (9,24),(2,3) → 99;
  (9,27),(2,3) → 108.
- Five are taken as already discarded (Moh [9], Heitmann [7],
  [5] §3.5, [3] §5). In Lean each "already discarded" is either a
  proved lemma (with its own module) or an explicit INTERFACE
  hypothesis — never silently absorbed into Thm 2.1.
- Theorem 2.1 statement: for a counterexample (P,Q), either
  max(deg P, deg Q) ≥ 125 or (deg P, deg Q) ∈ {(72,108),(108,72)}.
  Note: (72,108) arises as (8,28) with (m,n)=(3,2) after the §4
  reductions, and (9,27)/(9,24) are the cases killed in §5.

### 4.2 `Cases84_120.lean` — GGHV §3 [MEDIUM]
- max = 120 discarded via [4] Remark 3.31 / Prop. 3.29: after the
  shift y ↦ y + λ₁, (8,4) would be a last possible corner, which
  Prop. 3.29 forbids. Needs the "last possible corner" library.
- max = 84 discarded via [2] Thm 7.3, the intersection-number
  inequality I_M ≥ I_m: for family F₉, A₀=(7,21), A₀′=(1,0),
  A₁=(11/7,2), k=1, m=j+2, n=2j+3; at j=0, I_M = 4 vs I_m = 5,
  contradiction. The §3 proof is short *because* it imports the
  whole intersection-number machine of paper [2] — formalizing
  Thm 7.3 is a Phase-2 subproject in its own right (see synthesis).
- §6 of GGHV gives a second proof of (56,84) without intersection
  numbers — that is the (7,21) system of §4.4 below, and it is the
  proof to formalize first if the intersection machine is deferred.

### 4.3 `NewtonReductions.lean` — GGHV §4 [HARD, many small steps]
- Prop. 4.1, case (9,27): automorphisms φ₁ (swap), φ₂ (y ↦ y+α₁x⁻²),
  φ₃ (y ↦ y+α₂x⁻³), the divisibility table eliminating all but
  (5,2),(13,5) for the opposite vertex, Prop. 8.2 giving k=1 and
  ends {(−1,0),(2,1)} in direction (−3,8), then the Laurent morphism
  φ(x)=x⁻¹, φ(y)=x³y with [φ(P),φ(Q)] = −[P,Q]·x, yielding
  N(P)={(0,0),(1,1),(6,16),(6,18),(0,18)},
  N(Q)={(0,0),(1,0),(9,24),(9,27),(0,27)}.
- Prop. 4.2, case (9,24): three outcomes (extra vertices (0,12)/(0,18),
  (0,6)/(0,9), or none), via the PossibleStartingPoints algorithm,
  Cor. 7.4 with q=3, and the R-factor analysis (1, 2, or 3 linear
  factors in z = x²y; the 3-factor case killed by Prop. 3.12(2)).
- Prop. 4.3, case (8,28) — **the Prop. 4.3 of the Helali interface**:
  three lower-side shapes a), b), c) (corners (−2,0) / (−3,0) /
  (−3,0),(16,4) times (m,n)=(3,2)), then φ₃ (y ↦ y+αx⁻⁴), Prop. 8.2
  with k∈{1,2} (k=2 impossible: edges would not be parallel),
  k=1 ends ((2,1),(−1,0)), then φ(x)=x⁻¹, φ(y)=x⁴y with
  [φ(P),φ(Q)] = −[P,Q]·x², yielding the two Helali cases:
  (1) with (0,8)/(0,12) [case c)], (2) without [cases a),b)].
  **This is the exact junction between Phase 1 and Phase 2: the
  vertex lists in §3.1 must match these outputs term for term.**
- Prop. 4.4, case (7,21): N(P)={(0,0),2(2,0),2(3,1),2(0,7)},
  N(Q)={(0,0),3(2,0),3(3,1),3(0,7)} via φ₁, φ₂ (y ↦ y+λx⁻²),
  φ₃ (x ↦ x⁻¹, y ↦ yx³). This is the input to §4.4.

### 4.4 `PolynomialSystems.lean` — GGHV §5–§6 [HARDEST, CAS-bound]
- Thm 5.1 (cases (9,24),(9,27)): no P,Q with [P,Q] = x + g(y) and
  the stated end/start conditions. Proof skeleton to formalize:
  Prop. 5.2 (inductive construction of C with C²=P, Q = C³+α₂C²+
  α₁C+α₀+α₋₁C⁻¹+F, v_{1,0}(F)=−4, with valuation bounds
  v_{−1,1}, v_{3,−1}); Prop. 5.4 (f = C₃²F_{−4} separable, divisible
  by y(y+1), deg 6 — via an explicit ODE for f₁ with a CAS-found
  solution that must be *checked*, not trusted); Prop. 5.5
  (D_k = C_k·C₃^{5−2k} ∈ K[y]); Prop. 5.6 (valuations −39 / 51);
  elimination to (5.9) 18C₃²³d₁(d_{−1})⁶F_{−4} + 8C₃⁶⁹F_{−4}⁹ +
  27d₀(d_{−1})⁹ = 0; the (5.11) divisibility + degree-count
  contradiction (k≥8 impossible by multiplicity 66; k≤7 impossible
  by degrees 76/75 < 78).
- Cor. 5.7: the (9,27) polygon case follows via ψ(x)=x^{1/2} and
  the sixth-power argument.
- Thm 6.1 (case (7,21)): same skeleton with C₃ replaced by y,
  F_{−4} = (1/2)y⁻¹, D_k = C_k·y^{2−k}, elimination to (6.18)
  9y⁹d₁(d_{−1})⁶ + y⁹ + 27d₀(d_{−1})⁹ = 0, and the final
  non-square contradiction.
- **The CAS problem, stated plainly:** both eliminations are
  reported as "using a CAS (for example Mathematica) we eliminate
  …". A Lean formalization cannot cite Mathematica. Each elimination
  must be replaced by either (a) explicit elimination identities
  (a Gröbner/certificate witness, checked by expansion), or
  (b) a verified elimination procedure. Until one of those exists,
  Thm 5.1 / Thm 6.1 formalize only up to the pre-elimination system,
  with the elimination as a flagged INTERFACE gap. This is the
  single largest known gap in Phase 2, and it is *not* a gap in
  Phase 1 (Helali's certificates are explicit identities, not CAS
  eliminations — that asymmetry is why Phase 1 is the right first
  phase).

## 5. Proposed Lean4 folder layout (to be placed in the repo)

```
Lean4/
  README.md                  -- this map, condensed; status table
  lakefile.lean / lean-toolchain   -- Lean 4.34.0 (workspace env),
                                     Mathlib dependency TBD at setup
  JC2/
    Basic.lean               -- Keller pair, bracket, degrees, Laurent ring
    NewtonPolygon.lean       -- support, conv, vertices (shared lib)
    Directions.lean          -- §4.0 library (Phase 2, largest)
    DimSplit.lean            -- §3.0 (Phase 1, first compilable target)
    Frontier.lean            -- §3.1 interface (axioms labelled INTERFACE)
    LaurentReduction.lean    -- §3.2 (J4..J0, H, descent to L)
    Case2.lean               -- §3.3 certificate module
    Case1Branching.lean      -- §3.4
    Case1HZero.lean          -- §3.5
    HardCertificate.lean     -- §3.6 (data import + expansion check;
                                     kernel-feasibility benchmark first)
    Symmetry.lean            -- §3.7
    Exclusion.lean           -- Helali theorem + conditional corollary
    GGHV/
      SmallCases.lean        -- §4.1
      Cases84_120.lean       -- §4.2
      NewtonReductions.lean  -- §4.3 (incl. Prop. 4.3 junction)
      PolynomialSystems.lean -- §4.4 (CAS gaps flagged)
      Theorem21.lean         -- assembly of Thm 2.1
  Data/
    README.md                -- hashes, provenance, import scripts;
                                NO certificate data committed until the
                                import format + hash re-check is fixed
```

Conventions for every file: no `sorry` in a file presented as proved;
`axiom` only under an `INTERFACE` section header with the paper
reference and the phase that will discharge it; every certificate
module states its data hash and the exact expansion it checks.

## 6. Relationship to Brandon's existing branch-(c) programme — DO NOT MERGE

Brandon's own programme (repo `2D-Jacobian-Conjecture-Workspace`)
also treats GGHV Prop. 4.3 case (1), degree (72,108): branches (a),(b)
eliminated in Lean at Grade A; branch (c) closed under the grade-B
premise ChartEmptyC_T1ne0 (3199×3199 Macaulay matrix at
p = 1000003 and p = 32003, two project-internal implementations,
I1); grade-A deliverables A1 (packed kernel check C·M_S = I mod
32003) and A2 (M_S as evaluated Macaulay block) outstanding.

Striking coincidence to check, not a conclusion: Helali's descent
field L = ℚ[w]/(w⁵ − w⁴ + 3w³ + 3w² + 26) is the *same polynomial*
as Brandon's K₅. Whether Helali's Case 1/Case 2 systems and Brandon's
branch-(c) system are two transcriptions of the same system, two
subcases, or unrelated systems sharing a field, is **unverified**.
Do not merge the two programmes, do not cite one as confirming the
other, and do not let Helali's conditional corollary upgrade
ChartEmptyC_T1ne0 (or vice versa) until that identification is
checked term by term. If they are the same system, the two
certificate architectures (2010×1925 rational identity vs
3199×3199 modular Macaulay at two primes) would be a genuine
cross-check — that would be valuable, and it is exactly why the
identification check is the first cross-programme task, ahead of
any Lean work on either side.

## 7. Order of work (recommended)

1. Repo clone finishes → move this folder into the repo as `Lean4/`,
   confirm no tracked `Lean4/` already exists there (if it does, stop
   and reconcile before overwriting).
2. `DimSplit.lean`: the Alpöge check — first real Lean proof in the
   folder, small, and it also serves as the toolchain smoke test
   (Lean 4.34.0 + Mathlib in the workspace env).
3. Certificate-import prototype on Case 2 (smallest certificate):
   format, hash re-check, expansion check, kernel-feasibility
   benchmark. If the expansion check is infeasible in-kernel, decide
   the interface policy for §3.6 *before* building on it.
4. Laurent reduction + H/descent data extraction from the replay
   scripts (explicit polynomials, not "Gröbner said so").
5. Case 1 branching / h=0 / hard certificate, in that order.
6. Phase 2 library (`Directions.lean`) — only after Phase 1 is
   assembled, since Phase 2 is larger and its CAS gaps are known.
7. Guccione six-paper library (see synthesis): the direction
   machinery of §4.0 is shared; do not duplicate it per paper.

## 8. Sources and versions pinned

- GGHV: arXiv:2204.14178v1 (uploaded PDF, 2026-10-29 read).
- Helali: `paper/jc2_72_108_exact_exclusion.tex`, v1.0.1 zip
  (2026-07-21 snapshot, author Billel Helali), plus
  `verification/verify_all_final.out` and
  `verification/RECONSTRUCTED_CERTIFICATES.sha256` in the same zip.
  The 90 MB `release_bundle/jc2_72_108_exact_replay_v1.0.1.zip`
  inside the zip was NOT unpacked or run in this session; replay
  claims are the paper/README's, not re-verified here.
- The GitHub clone landed 2026-10-29 (HEAD c530fe4, "Correct
  mathematical typography in X post"; Zenodo DOI
  10.5281/zenodo.21479814 in the repo README, one commit past the
  v1.0.1 zip snapshot d9ea4fd). This folder now lives in the repo
  working tree as `Lean4/`, **uncommitted and unpushed** — nothing
  has been committed to the repo in this session.
