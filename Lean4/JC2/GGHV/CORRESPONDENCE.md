# GGHV paper ↔ Lean correspondence (1-to-1)

Paper: Guccione, Guccione, Horruitiner, Valqui, "Increasing the
degree of a possible counterexample to the Jacobian Conjecture
from 100 to 108", arXiv:2204.14178v1.
TeX source read: `~/workspace/research/rss-monitor/tex/2204.14178/main.tex`
(2,262 lines). Lean files: this directory (Parts 1–13:
Parts 1–9 and 13 core Lean 4.34.0 standalone, Parts 10–12
Mathlib via lake). All files compile (`bash compile_all.sh`
for the standalone parts, `lake build` in the parent
`Lean4/` directory for the Mathlib parts), with **no
`sorry`, no `admit`, and no `axiom` declarations at
all** (2026-10-30 checks, re-run after Parts 9–13 were
added and after the lake build).
Conditionality is carried as explicit theorem hypotheses,
not as axioms — so nothing here is a hidden unproved claim.

## How to read this file

Every numbered paper item has exactly one row. "Lean structure"
names the file and the definition/theorem that is its counterpart.
Status codes:

- **KERNEL** — proved by the Lean kernel in the named file, for
  that narrow claim only. Under HLRE v5.1, a KERNEL row is
  Grade A *for that narrow claim*, and for nothing wider.
- **DATA** — the paper's statement is recorded verbatim as a
  Lean definition (vertex list, degree pair, coefficient shape).
  DATA is not a proof of the statement: it pins the statement
  so a later proof can be checked against it.
- **CONDITIONAL** — a Lean theorem whose hypotheses are exactly
  the unproved premises. The theorem is proved; the paper
  claim is proved only when the hypotheses are discharged.
- **INTERFACE** — not formalized. The row names the library or
  certificate that must discharge it. Do not cite an INTERFACE
  row as proved.
- **EXTERNAL** — a result cited by GGHV from another paper
  ([GGV1]–[GGV6], [M], [H]). It is not GGHV's own theorem and
  is not formalized here; it is listed because the assembly
  depends on it.

**Headline, stated plainly:** coverage is 1-to-1 (every paper
item below has a Lean counterpart), but the paper is **NOT
100% kernel-proved**. The kernel-proved part is the §2 table
combinatorics, the §3 numeric computations, the §4/§6 scaling
and vertex-list data checks, the §5/§6 conditional
endgames, the §3–§4 direction-valuation arithmetic (Part 6),
the monomial bracket / φ chain rule (Part 7), and the
maximal-valuation segments for the §5 directions plus φ
bijectivity and bracket antisymmetry (Part 8). Both CAS
eliminations are independently verified in SymPy (I1) and
also kernel-proved as Parts 11–12. The open gaps are:
(1) the full Directions theory (en/st as homogeneous
parts, Pred/Succ; face lists at the support level are
Part 13), (2) the polynomial Laurent algebra
(bilinearity, polynomial φ chain rule, polynomial
Jacobi — monomial Jacobi is Part 10), (3) the
§5 rescaling to `nueva ecuacion principal` as a Lean
proof and the derivation of the original coefficient
systems (D2),
(4) the cited [GGV*] machinery, (5) the Helali ↔ branch-(c)
identification. (D6, the lake + Mathlib build, closed
2026-10-30 — see the D6 gap entry.)
Anyone who says "GGHV is formalized in Lean" from this
directory alone is overstating it; the correct statement is
"GGHV is mapped 1-to-1, with Parts 1–9 and 13 compiling standalone, Parts 10–12 via lake, and the remaining gaps are items D1–D5 below (D5 complete as an identification, D6 closed)."

## §2 — Complete list of small cases

| Paper item | Paper mathematics | Lean structure | Status |
|---|---|---|---|
| Thm 2.1 (§2, unnumbered theorem) | If (P,Q) is a counterexample, then max{deg P, deg Q} ≥ 125 or (deg P, deg Q) ∈ {(72,108), (108,72)} | `Part5_Assembly.lean`: `theorem21_conditional`, `theorem21_degree_pairs`, `AssemblyPremises` | CONDITIONAL (premises = enumeration + all discards; see Part 5 header for the row-vs-degree-pair correction) |
| §2 table, 10 rows | A₀, (m,n), max degree: (4,12)(3,4)64, (4,12)(5,7)112, (5,20)(2,3)75, (5,20)(3,2)75, (7,21)(2,3)84, (8,24)(2,3)96, (8,28)(3,2)108, (8,32)(3,2)120, (9,24)(2,3)99, (9,27)(2,3)108 | `Part1_Cases.lean`: `table` | DATA |
| §2 degree-pair formula | degree pair = (m·(a+b), n·(a+b)) for A₀ = (a,b) | `Part1_Cases.lean`: `degreePair` | DATA (formula as defined) |
| §2 table arithmetic | Every row's degree pair has the paper's stated max degree; pairs in order: (48,64), (80,112), (50,75), (75,50), (56,84), (64,96), (108,72), (120,80), (66,99), (72,108) | `Part1_Cases.lean`: `table_max_degrees`, `table_degree_pairs` | KERNEL |
| §2 table bound | Every row has maxDeg < 125 | `Part1_Cases.lean`: `table_below_125` | KERNEL |
| §2 red rows (5) | (4,12)(3,4), (4,12)(5,7), (5,20)(2,3), (5,20)(3,2), (8,24)(2,3) discarded by cited papers | `Part1_Cases.lean`: `redDiscarded` | DATA + EXTERNAL (citations: [GGV4] §3.5, [M], [H], [GGV3] §5, [GGV5] Prop. 6.1) |
| §2 survivors (after §2+§3 discards) | Remaining degree pairs: (108,72), (66,99), (72,108) | `Part1_Cases.lean`: `section2Remaining`, `section2_survivors` | KERNEL (as a filter computation on the paper's discard data; the discards themselves are Parts 2–4) |
| (72,108) arithmetic | gcd(72,108) = 36; reduced ratio (2,3) | `Part1_Cases.lean`: `deg_72_108_gcd`, `deg_72_108_ratio` | KERNEL |
| (72,108) / (108,72) rows | (9,27) row and (8,28) row are in the table | `Part1_Cases.lean`: `row_72_108_in_table`, `row_108_72_in_table` | KERNEL |
| §2 enumeration premise | Every counterexample with max < 125 lies in one of the 10 rows (from [GGV5] §§5–6) | `Part5_Assembly.lean`: `AssemblyPremises.enumeration` | INTERFACE (D5: [GGV5] enumeration library) |

## §3 — Discards: max = 120 and max = 84

| Paper item | Paper mathematics | Lean structure | Status |
|---|---|---|---|
| §3-120 data | A₀ = (8,32), A₁ = (8,28), A₂ = (11/4,7); (ρ₁,σ₁) = (4,−1) from v(A₁) = v(A₂) | `Part2_Discards.lean`: `corner_120_a0`, `corner_120_a1` | DATA |
| §3-120 en computation | en_{4,−1}(F₁) = (6,21) = (3/4)·A₁; (6,21) is the only point μ(8,28) with v = 3 | `Part2_Discards.lean`: `discard_120_data` (6·4 = 3·8, 21·4 = 3·28); `Part6_Directions.lean`: `val_120_a1`, `val_120_a2_scaled`, `val_120_equal` | KERNEL (cross-multiplication form of the (3/4) identity; the en computation itself, as a polygon extremum, is INTERFACE) |
| §3-120 q₁, d₀ | q₁ = 4 by [GGV1] Thm 7.6(5) (q₁ = 4 | d₀); d₀ ≤ 4 since st_{1,0}(P) = (8,28) = 4·(2,7), gcd(2,7) = 1 | `Part2_Discards.lean`: `discard_120_gcd` | KERNEL (gcd only); Thm 7.6(5) application = EXTERNAL |
| §3-120 ℓ formula | ℓ_{1,0}(P) = R^{4m} = (λ_P x²y⁷(y−λ₁))^{4m}; after φ(x)=x, φ(y)=y+λ₁, ℓ_{1,0}(φ(P)) = (λ_P x²y(y+λ₁)⁷)^{4m} | (no Lean counterpart beyond the corner data) | INTERFACE (D1: Directions library) |
| §3-120 transformed corner | A₀′ = (8,4) would be the last possible corner of φ(P) ([GGV2] Def. 3.21) | `Part2_Discards.lean`: `corner_120_transformed`, `corner_120_transformed_eq` | DATA |
| §3-120 impossibility | (8,4) is not a last possible corner, by [GGV2] Prop. 3.29 — hence the (8,32) case is discarded | `Part2_Discards.lean`: `discard_120_argument_shape` | CONDITIONAL-shape only (the two premises are abstract Props; no discard theorem is claimed) |
| §3-84 family data | F₉ smallest case: A₀ = (7,21), A₀′ = (1,0), A₁ = (11/7,2), k = 1, m = j+2, n = 2j+3 | `Part2_Discards.lean`: `f9_m` | DATA |
| §3-84 en / ℓ | en_{7,−2}(F) = (5,15); F = xy·f̄(z⁷), f̄ degree 2; ℓ_{7,−2}(P) = x·p̄(z⁷), p̄ degree 3m, at most two factors, multiplicities multiples of m; hence ℓ_{7,−2}(P) = ((z⁷−α₁)²(z⁷−α₂))^m, 14 factors | (no Lean counterpart beyond the family data) | INTERFACE (D1 + D2; [GGV1] Prop. 2.11(3) = EXTERNAL) |
| §3-84 major roots | 7 major final π-roots at A₁ = (11/7,2); per root |D| = mb = 2m, λ^Q = 1/7 (k=1, l=7) by [GGV6] Prop. 6.6(2) | (computation folded into I_M below) | EXTERNAL (Prop. 6.6(2)) + INTERFACE (π-root machinery) |
| §3-84 I_M | I_M = Σ |D|λ = 7·(2m)·(1/7) = 2(j+2); at j = 0, I_M = 4 | `Part2_Discards.lean`: `im_84_sum_at_j0` (7·(2·2) = 28), `im_84_at_j0` (28/7 = 4) | KERNEL (Nat form; the Rat cancellation 7·(2m)·(1/7) = 2m is the paper's formula — core Lean Rat does not reduce by rfl/decide, so it is not claimed as a Lean Rat proof) |
| §3-84 minor roots | 7 minor roots at A₁ = (9/7,1), δ = −9/7; one final minor π-root τ = −x + λ₀ + λ_{−2}x^{−2} + πx^{−3}, δ_τ = −3 ([GGV6] Props. 6.4, Ex. 6.7) | (computation folded into I_m below) | EXTERNAL + INTERFACE |
| §3-84 I_m | I_m = 1 − Σ(δ+1) = 1 − (−3+1) − 7·(−9/7+1) = 5 | `Part2_Discards.lean`: `im_minor_84` (Int form: 1 − (−2) − (7·(−2)/7) = 5) | KERNEL (Int form; the −9/7 + 1 = −2/7 step is the paper's fraction) |
| §3-84 contradiction | I_M ≥ I_m by [GGV6] Thm 7.3, but 4 < 5 — case discarded | `Part2_Discards.lean`: `discard_84_numeric`, `discard_84` (hypotheses: IM ≥ IMm, IM = 4, IMm = 5) | CONDITIONAL (Thm 7.3 = EXTERNAL; the "4 ≥ 5" statement is deliberately NOT axiomatized — that would be inconsistent) |
| §3-84 alternative proof | "In the last section we will give a proof very similar to the proofs in the other cases" — i.e. §6 | See §6 rows below | CONDITIONAL (via §6 principal equation) |

## §4 — Reducing the size of the Newton polygon

| Paper item | Paper mathematics | Lean structure | Status |
|---|---|---|---|
| Prop. 4.1, case (9,27) | If a counterexample exists in case (9,27), then P,Q ∈ L^{(1)} with [P,Q] = x and N(P) = {(0,0),(1,1),(6,16),(6,18),(0,18)}, N(Q) = {(0,0),(1,0),(9,24),(9,27),(0,27)} | `Part3_NewtonReductions.lean`: `prop41_P`, `prop41_Q` | DATA (vertex lists); the reduction proof = INTERFACE (D1+D2) |
| Prop. 4.1 proof steps | φ₁(x)=y, φ₁(y)=x; φ₂(y)=y+α₁x^{−2}; edge {(24,9),(0,1)} = y(yx³−α₂)⁸; φ₃(y)=y+α₂x^{−3}; (a′,b′) divisibility table (only (5,2),(13,5) survive); [GGV1] Prop. 8.2 gives k = 1, {en} = {(−1,0),(2,1)}, direction (−3,8); st_{−3,8}(P) = (42,16), st_{−3,8}(Q) = (63,24); φ(x)=x^{−1}, φ(y)=x³y; [φ(P),φ(Q)] = −[P,Q]x, rescaled to x | `Part3_NewtonReductions.lean`: `phi41` (map recorded as a string); `Part6_Directions.lean`: `val_41_edge` (the (−3,8) edge valuations, both 2); `Part7_MonomialBracket.lean`: `phi41_xy_bracket`, `chain_coeff_41`, `chain_exp_41` (monomial chain rule, factor −x) | DATA (map only) + KERNEL (edge valuations, monomial chain rule); the polygon reductions and the polynomial chain rule = INTERFACE (D1+D2); Prop. 8.2, Cor. 7.4 = EXTERNAL |
| Prop. 4.1 scaling | Q vertices are (3/2) × P vertices: (6,16)→(9,24), (6,18)→(9,27), (0,18)→(0,27) | `Part3_NewtonReductions.lean`: `prop41_scaling` | KERNEL (cross-multiplication) |
| Prop. 4.2, case (9,24) | If a counterexample exists in case (9,24), then P,Q ∈ L^{(1)} with [P,Q] = x and one of three outcomes: (1) N(P) = {(0,0),(1,1),(6,16),(6,18),(0,12)}, N(Q) = {(0,0),(1,0),(9,24),(9,27),(0,18)}; (2) …(0,6) / …(0,9); (3) …no extra vertex / …no extra vertex | `Part3_NewtonReductions.lean`: `prop42_P1/Q1`, `prop42_P2/Q2`, `prop42_P3/Q3` | DATA; reduction proof = INTERFACE |
| Prop. 4.2 proof steps | φ₁ swap; [GGV1] Cor. 7.4 with (ρ₀,σ₀) = (−1,3), l = 1, (a/l,b) = (24,9), q = 3; ℓ_{ρ,σ}(P) = λR^{3m}; [R,G] = R^i for some i (eq. `condicion`); [GGV2] Prop. 3.12; algorithm `PossibleStartingPoints` (l=1, a=8, b=3) giving Pred_P(1,0) ∈ {(1,−2),(2,−5)} | (no Lean counterpart beyond the three outcome lists) | INTERFACE (D1+D2); algorithm = OPEN (its enumeration must be formalized as a verified computation, not transcribed) |
| Prop. 4.3, case (8,28) | If a counterexample exists in case (8,28), then P,Q ∈ L^{(1)} with [P,Q] = x² and one of: (1) N(P) = {(0,0),(1,0),(8,14),(8,16),(0,8)}, N(Q) = {(0,0),(2,1),(12,21),(12,24),(0,12)}; (2) same without (0,8)/(0,12) | `Part3_NewtonReductions.lean`: `prop43_P1/Q1`, `prop43_P2/Q2` | DATA; reduction proof = INTERFACE. **Helali interface:** case 1 = Helali Case 1, case 2 = Helali Case 2 (map's identification; term-by-term system identification is still OPEN — see below) |
| Prop. 4.3 intermediate shapes | a) (m,n)·{(−2,0),(0,0),(28,8),(0,1)}; b) (m,n)·{(−3,0),(0,0),(28,8),(0,1)}; c) (m,n)·{(−3,0),(0,0),(16,4),(28,8),(0,1)} | `Part3_NewtonReductions.lean`: `prop43_shape_a/b/c` | DATA |
| Prop. 4.3 a/b collapse | a) and b) give the same final shape (case 2); c) gives case 1 | `Part3_NewtonReductions.lean`: `prop43_ab_agree_tail`, `prop43_case_lengths` | KERNEL (list facts) |
| Prop. 4.3 proof steps | [GGV1] Cor. 7.4 (−1,4), q = 4, en(R) = (7,2); [GGV6] Prop. 2.5: Pred_P(1,0) ∈ {(1,−2),(1,−3)}; φ₃(y) = y+αx^{−4}; Succ_P(−1,4) = Succ_Q(−1,4) = (−2,7); [GGV1] Prop. 8.2 with (a,b) ∈ {(24,7),(17,5),(10,3),(3,1)}, k ∈ {1,2}; k = 2 impossible (edges not parallel); k = 1 gives (en(Q),en(P)) = ((2,1),(−1,0)); φ(x)=x^{−1}, φ(y)=x⁴y; [φ(P),φ(Q)] = −[P,Q]x² | `Part3_NewtonReductions.lean`: `phi43` (map recorded as a string); `Part6_Directions.lean`: `val_43_edge` (the (−1,4) edge valuations, both 4); `Part7_MonomialBracket.lean`: `phi43_xy_bracket`, `chain_coeff_43`, `chain_exp_43` (monomial chain rule, factor −x²) | DATA (map only) + KERNEL (edge valuations, monomial chain rule); the polygon reductions and the polynomial chain rule = INTERFACE; cited props = EXTERNAL |
| Prop. 4.3 scaling | Q vertices are (3/2) × P vertices: (8,14)→(12,21), (8,16)→(12,24), (0,8)→(0,12) | `Part3_NewtonReductions.lean`: `prop43_scaling` | KERNEL |
| Prop. 4.4, case (7,21) | If a counterexample exists in case (7,21), then P,Q ∈ K[x,y] with [P,Q] = x and N(P) = {(0,0),2(2,0),2(3,1),2(0,7)}, N(Q) = {(0,0),3(2,0),3(3,1),3(0,7)} — i.e. P {(0,0),(4,0),(6,2),(0,14)}, Q {(0,0),(6,0),(9,3),(0,21)} | `Part3_NewtonReductions.lean`: `prop44_P`, `prop44_Q` | DATA (the 2·/3· reading of the paper's notation is stated in the file header); reduction proof = INTERFACE |
| Prop. 4.4 proof steps | φ₁ swap; q = 7 for direction (−2,7); ℓ_{1,−2}(P) = x²⁸λ_p(y−λx^{−2})¹⁴, ℓ_{1,−2}(Q) = x⁴²λ_q(y−λx^{−2})²¹; φ₂(y) = y+λx^{−2}; φ₃(x) = x^{−1}, φ₃(y) = yx³ | (no Lean counterpart beyond the vertex lists) | INTERFACE |
| Prop. 4.4 vs §6 lists | §6 theorem uses P {(0,0),(4,0),(2,6),(0,14)}, Q {(0,0),(6,0),(3,9),(0,21)} — the (6,2)/(9,3) vertices appear as (2,6)/(3,9) | `Part3_NewtonReductions.lean`: `thm721_P`, `thm721_Q` (both lists recorded verbatim) | DATA + OPEN: the transformation linking the two lists is NOT asserted (the Prop. 4.4 proof's final polygon is stated in a different scaling from §6's; asserting a φ-exponent identity unchecked would be fabrication) |

## §5 — Systems of polynomial equations for (9,24) and (9,27)

| Paper item | Paper mathematics | Lean structure | Status |
|---|---|---|---|
| Thm 5.1 ("teorema impossible") | No P,Q ∈ K[x,y] with (1) [P,Q] = x + g(y), (2) en_{3,−1}(P) = st_{1,0}(P) = 2(3,8) = (6,16), st_{−1,1}(P) = en_{1,0}(P) = 2(3,9) = (6,18), (3) en_{3,−1}(Q) = st_{1,0}(Q) = 3(3,8) = (9,24), st_{−1,1}(Q) = en_{1,0}(Q) = 3(3,9) = (9,27) | `Part4_Systems.lean`: `thm5_en_P/Q`, `thm5_st_P/Q`; `Part8_MaxSegments.lean`: `max_P_3m1`, `max_Q_3m1`, `max_P_10`, `max_Q_10` (max-attainment for the (3,−1) and (1,0) endpoints; the (−1,1) endpoints are not covered) | DATA (conditions) + KERNEL (max-attainment for (3,−1)/(1,0)); theorem = CONDITIONAL (via principal equation, now I1-verified, above) |
| Prop. "calculo de C" | C,F ∈ K[y,C₃^{−1}]((x^{−1})), v_{1,0}(F) = −4, α₂,α₁,α₀,α_{−1} ∈ K, P = C², Q = C³ + α₂C² + α₁C + α₀ + α_{−1}C^{−1} + F; ℓ_{1,0}(P) = R², ℓ_{1,0}(Q) = R³, R = x³C₃, C₃ = y⁸(a₀+a₁y), normalized to y⁸(y+1) | `Part4_Systems.lean`: `thm5_vF` (= −4) | DATA (v-value only); existence = INTERFACE (D2: Laurent-series algebra) |
| Prop. (f separable) | f := C₃²F_{−4} ∈ K[y] is separable, y(y+1) | f, deg f = 6 | (no Lean counterpart) | INTERFACE (D2) |
| Eq. `ecuacion de C 3-k` | Coefficient equations for C_{3−k} | (no Lean counterpart) | INTERFACE (D2) |
| Eq. `igualdad para Q` | Q-coefficient identity | (no Lean counterpart) | INTERFACE (D2) |
| Eq. `F casi esta en K[y]` | F is almost in K[y] (stated form) | (no Lean counterpart) | INTERFACE (D2) |
| Eq. `F con cunmutador` | F bracket identity (TeX label as written, sic) | (no Lean counterpart) | INTERFACE (D2) |
| Eq. `ecuaciones basicas` | Basic coefficient equations | (no Lean counterpart) | INTERFACE (D2) |
| Eq. `ecuaciones polinomiales` | Polynomial coefficient equations | (no Lean counterpart) | INTERFACE (D2) |
| Prop. + eq. `ecuaciones polinomiales nuevas` | Transformed polynomial equations (D-system) | (no Lean counterpart) | INTERFACE (D2) |
| Eq. `ecuacion principal` | Principal equation: 18 C₃²³ d₁ (d_{−1})⁶ F_{−4} + 8 C₃⁶⁹ F_{−4}³ + 27 d₀ (d_{−1})⁹ = 0, obtained by CAS elimination of d_{−10},d_{−8},d_{−7},d_{−6},d_{−5},d_{−4},d_{−3},d_{−2} from the 9-equation system | `elimination_s5.py` + `elimination_s5.log` (independent SymPy re-derivation, 2026-10-30) | EXTERNALLY VERIFIED, I1: sequential linear elimination, then resultant in d_{−2} between Q2 and Q4 = −27/(64·d_{−1}³) × the paper's principal equation, remainder 0 (divisibility checked by expanding resultant − factor × target = 0, since SymPy's polynomial `div` does not handle the d_{−1}^{−3} factor). NOT a Lean kernel proof by itself; the Lean elimination certificate (D3) is now compiled as Part 12 (2026-10-30). The §5 system is identical to §6's except Q4's final term (F_{−4}C₃²³ instead of F_{−4}y¹⁰), which is why the resultant factor matches §6's exactly. |
| Prop. + eq. `cota para el grado de los d` | deg(d₁) ≤ 34, deg(d₀) ≤ 51 (pre-scaling form in the proof) | (no Lean counterpart; the endgame uses the rescaled bounds below) | INTERFACE (D2) |
| Eq. `nueva ecuacion principal` | Rescaled principal equation, giving deg((y+1)⁶⁶g(y)³) = 78 | `Part4_Systems.lean`: `thm5_g_degree` (66 + 3·4 = 78); unrescaled equation verified in `elimination_s5.py` | KERNEL (degree arithmetic); the equation itself = EXTERNALLY VERIFIED, I1 (via the elimination above plus the paper's rescaling identities, which are not kernel-checked as a whole) |
| §5 endgame bounds | deg(18(y+1)²²d̃₁(d̃_{−1})⁶g(y)) ≤ 22+8+42+4 = 76; deg(27d̃₀(d̃_{−1})⁹) ≤ 12+9·7 = 75; both < 78, contradiction; k ≥ 8 and k ≤ 7 both impossible | `Part4_Systems.lean`: `thm5_bounds`, `thm5_endgame` | KERNEL (bounds arithmetic) + CONDITIONAL (endgame theorem: given a degree-78 term bounded by 76, False) |
| Cor. 5.7 (unnumbered corollary after Thm 5.1) | No P,Q ∈ K[x,y] with [P,Q] = x and N(P) = {(0,0),(1,1),(6,16),(6,18),(0,18)}, N(Q) = {(0,0),(1,0),(9,24),(9,27),(0,27)} (the Prop. 4.1 shapes) | `Part4_Systems.lean`: `cor57_P`, `cor57_Q` | DATA (shapes); corollary proof = INTERFACE (Succ argument, eq. `sucesores`, ψ: x ↦ x^{1/2} (m,n)-pair machinery of [GGV1] Def. 4.3 / Cor. 7.2 = EXTERNAL) |
| Cor. 5.7 consequence | The (9,27) ROW is eliminated. It does NOT eliminate the degree pair (72,108), which also arises from the (8,28) row swapped — see Part 5 header | `Part5_Assembly.lean`: `theorem21_degree_pairs` | CONDITIONAL (assembly by rows) |

## §6 — Systems of polynomial equations for (7,21)

| Paper item | Paper mathematics | Lean structure | Status |
|---|---|---|---|
| Thm 6.1 ("teorema impossible para 7") | No P,Q ∈ K[x,y] with [P,Q] = x and N(P) = {(0,0),(4,0),(2,6),(0,14)}, N(Q) = {(0,0),(6,0),(3,9),(0,21)} | `Part4_Systems.lean`: `thm6_P`, `thm6_Q` | DATA (shapes); theorem = CONDITIONAL (via principal equation, below) |
| Prop. "calculo de C para 7" | C,F ∈ K[y,y^{−1}]((x^{−1})), v_{1,0}(F) = −4, same α-shape as §5; ℓ_{1,0}(P) = x⁶y², ℓ_{1,0}(Q) = x⁹y³ after linear change | `Part4_Systems.lean`: `thm6_vF` (= −4) | DATA (v-value only); existence = INTERFACE (D2) |
| Eq. `ecuacion de C 3-k para 7` | Coefficient equations for C_{3−k} in the (7,21) case | (no Lean counterpart) | INTERFACE (D2) |
| Eq. `igualdad para Q` (§6 version) | Q-coefficient identity | (no Lean counterpart) | INTERFACE (D2) |
| Eq. `ecuaciones basicas para 7` / `ecuaciones polinomiales para 7` | Basic / polynomial coefficient equations | (no Lean counterpart) | INTERFACE (D2) |
| Prop. D_k ∈ K[y] | D_k := C_k·y^{2−k} ∈ K[y], by induction from D₃ = 1, D₂ = C₂ = P₅/(2y), y | P₅ | (no Lean counterpart) | INTERFACE (D2) |
| Eq. `ecuaciones polinomiales nuevas para 7` | (D²)_{−k} = 0 (k = 1…8), (D³)_{−1} = (D³)_{−2} = 0, (D³)_{−3} + λy⁸ = 0, (D³)_{−4} − λD₂y⁸ + F_{−4}y^{10} = 0 | (no Lean counterpart) | INTERFACE (D2) |
| §6 coefficient system | The 12 displayed (D̃²)/(D̃³) coefficient equations, with F_{−4} = (1/2)y^{−1}, D̃ = x³ + xd₁ + d₀ + x^{−1}d_{−1} + … (d₂ = 0) | (no Lean counterpart) | INTERFACE (D2) |
| Eq. `ecuacion principal para 7` | 9y⁹d₁(d_{−1})⁶ + y²⁷ + 27d₀(d_{−1})⁹ = 0, obtained "using a CAS (for example Mathematica)" by eliminating d_{−10},d_{−8},d_{−7},d_{−6},d_{−5},d_{−4},d_{−3},d_{−2} | `elimination_s6.py` + `elimination_s6.log` (independent SymPy re-derivation, 2026-10-30) | EXTERNALLY VERIFIED, I1 (single-route CAS): sequential linear elimination of d_{−4},d_{−5},d_{−6},d_{−7},d_{−8},d_{−3},d_{−10}, then resultant in d_{−2} between the two remaining equations = −27/(64·d_{−1}³) × the paper's principal equation, remainder 0. NOT a Lean kernel proof by itself; the Lean principal-equation certificate (D3) is now compiled as Part 11 (2026-10-30). Transcription note: the TeX (D̃²)_{−7} line reads "2 d_{−1}0", read as 2 d_{−10} (coefficient pattern + the correctly-braced 2 d_{−11} in the (D̃²)_{−8} line). The intermediate Q2 equation after substitution is d_{−2}³ + d₁d_{−1}²d_{−2} + d₀d_{−1}³ = 0 (up to the factor −3/(2d_{−1})). |
| §6 principal degrees | d_{−1} = αy^k; deg(d₀) = 9, deg(d₁) = 6; hence k = 2 (at k = 2 the three terms have degrees 15+6k = 27, 27, 9+9k = 27) | `Part4_Systems.lean`: `thm6_principal_degrees_at_k2` | KERNEL (degree check at k = 2); the derivation that k must be 2 = INTERFACE |
| §6 auxiliary identities | 2d_{−3}y⁹ = 3d₀(d_{−1})⁴; 3(d_{−1})²d_{−2} = y⁹; hence d₁, d_{−2}, d_{−3} formulas | (no Lean counterpart) | INTERFACE (D2/D3) |
| §6 final contradiction | Substituting into 0 = 2(D̃³)_{−3} − 3((D̃²)_{−6} + d₁(D̃²)_{−4} + d₀(D̃²)_{−3} + d_{−1}(D̃²)_{−2} + d_{−2}(D̃²)_{−1}) gives (27α⁹d₀ − 2y⁹)²/(108α^{10}) = α³y⁸ − 2λy^{10}, whose right side is not a square of a polynomial (α,λ ≠ 0) | (no Lean counterpart; noted in `Part4_Systems.lean` as INTERFACE) | INTERFACE (D2: polynomial-square argument) |

## External dependencies (cited by GGHV, not formalized here)

| Reference | Used for | Status |
|---|---|---|
| [GGV5] §§5–6 tables, Prop. 6.1 | §2 enumeration; (8,24) red discard | EXTERNAL |
| [GGV4] §3.5 | Red discards (64, 112) | EXTERNAL |
| [M] Moh, [H] Heitmann | Red discards (64, 75 — "no detail" for 75 in [M] per GGHV §2) | EXTERNAL (and GGHV itself notes [M]'s 75 case lacks detail) |
| [GGV3] §5 | Red discards (75) | EXTERNAL |
| [GGV2] Def. 3.21, Prop. 3.29, Prop. 3.12, Remark 3.31 | §3-120 last-corner argument; Prop. 4.2 algorithm setting; §2 note on (8,32) | EXTERNAL |
| [GGV1] Thm 7.6(5), Prop. 2.11(3), Cor. 7.4, Cor. 7.2, Prop. 8.2, Def. 4.3, Props. 1.13/2.1 | §3-120 q₁; §3-84 ℓ form; §4 reductions; §5 corollary ψ argument | EXTERNAL |
| [GGV6] Thm 7.3, Props. 6.4/6.6, Ex. 6.7, Prop. 2.5 | §3-84 I_M ≥ I_m; §4.3 Pred values | EXTERNAL |

## Open gaps (what "100% proved" would still need)

- **D1 — Directions / Newton-polygon library.** FIRST LAYER
  DONE (Part 6): weighted valuations and edge-valuation
  equalities at the paper's stated points. SECOND LAYER,
  CONCRETE CASES DONE (Part 8, 2026-10-30): maximal-
  valuation attainment for directions (3,−1) and (1,0) on
  the Prop. 4.1 / §5 shapes — P valuations [0,2,2,0,−18]
  (max 2 at (1,1),(6,16)), Q [0,3,3,0,−27] (max 3 at
  (1,0),(9,24)); under (1,0), P [0,1,6,6,0] (max 6 at
  (6,16),(6,18)), Q [0,1,9,9,0] (max 9 at (9,24),(9,27)).
  These are exactly the §5 en/st endpoints for those
  two directions, proved as attainment. GENERAL
  INFRASTRUCTURE DONE (Part 9, 2026-10-30): a general
  maximal-valuation vertex function `maxVertDir`
  (last-max tie-break) with kernel-checked membership
  and maximality lemmas, and a minimal-valuation vertex
  `minVertDir` (negated direction) with membership and
  minimality. NEGATIVE RESULT (Part 9): valuation
  extremum does NOT define en/st in general — under
  (−1,1), maxVertDir on the P shape is (0,18) and
  minVertDir is (1,1), whereas Thm 5.1's st_{−1,1}(P) is
  (6,18), which is neither. The [GGV*] face definition
  (with its ordering, tied to ℓ_{ρ,σ}) is therefore still
  needed. Still open: en/st as a general definition,
  maximal segments for other directions/polygons
  (including §3-120/§3-84), Pred/Succ,
  (ρ,σ)-homogeneous parts ℓ_{ρ,σ}. FIRST STEP DONE
  (Part 13, 2026-10-30, core Lean, compiles standalone):
  the (ρ,σ)-face list — vertices attaining maximal
  valuation — with membership, subset, maximality, and
  nonemptiness lemmas, and the concrete §5 faces
  (P [(1,1),(6,16)], Q [(1,0),(9,24)] under (3,−1);
  P [(6,16),(6,18)], Q [(9,24),(9,27)] under (1,0)).
  SECOND STEP DONE (Part 14, 2026-10-30, D4 Part A
  session 1): the same faces with coefficients kept
  (`faceTerms`, membership, subset, maximality,
  nonemptiness). THIRD STEP DONE (Part 15, 2026-10-30,
  D4 Part A session 2): face endpoints (first/last
  face terms, membership, maximality), matching Part 8's
  §5 endpoint pairs under (3,−1) and (1,0), plus the
  negative result that the (−1,1) endpoints are both
  (0,18), not Thm 5.1's st = (6,18). The polynomial ℓ
  itself (a polynomial, with bracket identities) and
  the paper's en/st definition are still open (Part A
  session 3: Pred/Succ + general maximal segments;
  en/st-as-in-paper needs [GGV1], Part B). FOURTH STEP
  DONE (Part 16, 2026-10-30, D4 Part A session 3):
  list-order Pred/Succ for general term lists
  (first-occurrence decompositions, membership, inverse
  in decomposition form) and segment predecessor/
  successor neighbour theorems for arbitrary faces,
  with §5 segment neighbours under (3,−1), (1,0) and
  (−1,1). Part A is now complete. Part B session 1 DONE
  (Part 17, 2026-10-31): [GGV1] definitions layer —
  V/V_{>0}, homogeneous term lists, st/en of a face via
  the paper's secondary-direction formula — plus the
  clarification that Parts 8/13/15's shape list is Prop.
  4.1's polygon, not Thm 5.1's §5 polygon, so the
  (−1,1) endpoints on that list do not contradict Thm
  5.1. Part B session 2 DONE (Part 18, 2026-10-31):
  Prop. 8.2 instance layer — the numbering pin (GGHV
  Prop. 8.2 = TeX "esquina de 83" item (2)),
  proportionality, the k-family non-proportionality,
  the k = 1 instance, and item (2) as a hypothesis
  bundle (Part 19, 2026-10-31, with the condition-(3)
  open question recorded). Part B session 4 DONE
  (Part 20, 2026-10-31): remaining [GGV1] instances
  (Props. 1.13/2.1, Def. 4.3, Cor. 7.2, Prop. 2.11(3))
  and Pred/Succ from ℓ — Part B COMPLETE. Still open
  from Part B: proof of Prop. 8.2 item (2), k = 2
  exclusion, Cor. 7.4 condition-(3) question, full
  Dir/Succ theory. Parts C–F remain. Discharges:
  §3-120 en extremality, §3-84 derivation of I_M/I_m from
  roots, Props. 4.1–4.4 reductions.
- **D2 — Laurent-polynomial / Laurent-series algebra library.**
  FIRST LAYER DONE (Part 7): monomial bracket and the φ
  chain rule for monomials. SECOND LAYER, CONCRETE CASES
  DONE (Part 8, 2026-10-30): φ₄₁ and φ₄₃ are bijective on
  exponent pairs (both are involutions, componentwise
  kernel-checked), and monomial bracket antisymmetry
  [m,n] = −[n,m] for arbitrary exponents. SECOND LAYER,
  MATHLIB (Part 10, 2026-10-30, COMPILED via `lake build`,
  640s, after two linter warnings fixed): the monomial
  Jacobi identity for arbitrary exponents (by Mathlib's
  `ring`, which core Lean lacks), and the φ-bracket
  factors for arbitrary monomials — bracketCoeff (φ m)
  (φ n) = −bracketCoeff m n, with exponent shift (1,0)
  for φ₄₁ and (2,0) for φ₄₃, i.e. [φ(m),φ(n)] = −[m,n]·x
  and −[m,n]·x² in coefficient/exponent form. Still open:
  finite-support polynomials, bilinearity, polynomial φ
  chain rule, C/F/D expansions and coefficient systems.
  Discharges: §5/§6 expansions and coefficient equations,
  polynomial [φ(P),φ(Q)] identities.
- **D3 — Elimination certificates for the two principal
  equations.** BOTH INDEPENDENTLY VERIFIED in SymPy
  (I1) — §6 in `elimination_s6.py`, §5 in
  `elimination_s5.py` (2026-10-30); in both cases the
  resultant in d_{−2} is exactly −27/(64·d_{−1}³) times
  the paper's principal equation, remainder 0. §6 LEAN
  CERTIFICATE COMPILED (Part 11, 2026-10-30, `lake build`,
  1285s): an explicit integer polynomial identity
  d_{−1} · target = Σ P_i · (original equation i),
  computed by tracked linear elimination
  (`elimination_certificate_s6.py`, certificate PASSED,
  clearing denominator D = 1, Q4 doubled so all
  coefficients are integers), from which the §6
  principal equation follows by `ring` plus d_{−1} ≠ 0
  (first build failed only on the final step because
  `simp` had already split the product into a
  disjunction; fixed by using the disjunction directly).
  §5 LEAN CERTIFICATE COMPILED (Part 12, 2026-10-30,
  `lake build`, 1285s): the same shape, Q4's final term
  F_{−4}C₃²³, tracked elimination in
  `elimination_certificate_s5.py`, D = 1. The 9 original
  equations themselves remain hypotheses (their
  derivation is D2). D3 is now CLOSED for the two
  unrescaled principal equations; what remains of D3 is
  the §5 rescaling to `nueva ecuacion principal` as a
  Lean proof, plus the D2 derivation of the original
  systems.
- **D4 — Cited [GGV*] results as formalized theorems.**
  OPEN, documented in `D4_CITED_RESULTS.md` and roadmap in `D4_FORMALIZATION_ROADMAP.md` (2026-10-30):
  Thm 7.3, Prop. 3.29, Prop. 8.2, Cor. 7.4, Prop. 3.12,
  Prop. 2.5, Thm 7.6(5), Prop. 2.11(3), Cor. 7.2, Def. 4.3,
  Props. 1.13/2.1, Def. 3.21, Remark 3.31, Props. 6.4/6.6,
  Ex. 6.7, and the [GGV5] enumeration — each with the
  exact instance used here and what formalizing it would
  require. These are separate papers' results;
  formalizing them is a programme of its own, not a
  sub-step of this file set. Part 5's Theorem 2.1 remains
  CONDITIONAL on these instances as `AssemblyPremises`
  fields; no premise field has been replaced.
- **D5 — Helali ↔ branch-(c) / Prop. 4.3 identification.**
  COMPLETE as an identification (2026-10-30, four
  checks, see `D5_IDENTIFICATION.md`): Case 1 =
  branch-(c) NewtonNFc, Case 2 = branch-(a,b)
  NewtonNF2; Helali's J4..J0 = Brandon's `EIdent` at
  n = 5..1 restricted to the upper bands (P layers
  k = 2,1,0; Q layers l = 3,2,1,0), term by term via
  `layerTermZ a b = a·A·B′ − b·A′·B`; λ resolved by
  scaling; A normalization proved over algebraically
  closed K (7th root of c₁/c₈). Scope: Helali's band
  systems are upper-band subsystems of Brandon's full
  layer systems (which include negative layers from
  the (0,8)/(0,12) vertices); settings differ (Helali:
  algebraically closed K, A normalized; Brandon:
  L / t₂ = 1 chart, DescentClaimC grade B for Case 1,
  Grade A classification-conditional main theorem for
  Case 2); certificate mechanisms are independent
  proofs, not part of the identification.
- **D6 — Lake project + Mathlib.** DONE (2026-10-30):
  the lake project in the parent `Lean4/` directory
  (`lakefile.toml` requiring Mathlib v4.34.0,
  `lean-toolchain` = leanprover/lean4:v4.34.0, `GGHV` lib
  with roots = Parts 1–8 only, so the uncompiled
  `JC2/ExclusionSkeleton.lean` map skeleton is NOT a
  build target, `defaultTargets = ["GGHV"]`) is fully
  installed and built: Mathlib rev
  5ed2965256430c3649e86755f9576b54eca72435 (tag
  v4.34.0, verified by `git describe --tags`),
  `.lake/` 8.0 GB under `~/workspace` (home persists
  across VM replacements), `lake exe cache get`
  decompressed 8,908 files with nothing to download,
  `Mathlib.olean` present, and `lake build` succeeds
  (10 jobs, all 8 Parts as oleans). The project lives
  in the workspace and the toolchain is symlinked into
  the `jacobian-conjecture-2d` conda env bin; a
  one-command restore script is `Lean4/restore-mathlib.sh`.
  What D6 completion did not change at the time: no Part
  imported Mathlib yet, so Mathlib was available
  infrastructure for future D2 work, not a proof step
  used by any current theorem. (Superseded 2026-10-30:
  Parts 10–12 import Mathlib and use it for D2/D3.)

## What this run moves forward (programme level)

1. GGHV Parts 2–5 now exist and compile; before this run only
   Part 1 existed. The assembly is now a single conditional
   structure (`AssemblyPremises`) instead of a loose list of
   "later parts".
2. The Helali interface is now tied to Lean data: Prop. 4.3
   case 1 / case 2 vertex lists (`prop43_P1/Q1`, `prop43_P2/Q2`)
   are the exact shapes Helali's Case 1 / Case 2 must match.
   The next licensed step is the D5 identification check,
   not a merge.
3. The §5/§6 endgames are now conditional theorems with the
   CAS gap isolated to two named equations, instead of a
   blanket "Mathematica steps" caveat.
4. Nothing in this run moves a grade on branch (c) A1/A2,
   Theorem R, or the sieve, and nothing here is a proof of
   JC(2). The A1/A2 priority from 2026-10-29 is unchanged.
5. 2026-10-30 continuation: Part 8 (maximal-valuation
   segments for the §5 directions, φ bijectivity, bracket
   antisymmetry) compiles; the §5 elimination is now
   independently verified in SymPy (I1) on the same
   footing as §6, so D3 is narrowed to Lean certificates
   for both equations; a lake project requiring Mathlib
   v4.34.0 is set up in `Lean4/` (D6 DONE 2026-10-30, see
   below — `lake build` succeeds) — Parts 10–12 import Mathlib and use it (D2/D3, compiled 2026-10-30).

## 2026-10-30 update — Parts 6–7 and the §6 elimination check

5. Part 6 (`Part6_Directions.lean`) proves the direction
   valuation arithmetic of §§3–4; Part 7
   (`Part7_MonomialBracket.lean`) proves the monomial
   bracket and both φ chain rules. D1 and D2 are now
   first-layer done, second-layer open (see gaps above).
6. The §6 principal equation is independently verified in
   SymPy (`elimination_s6.py`, log `elimination_s6.log`):
   resultant = −27/(64·d_{−1}³) × target, remainder 0.
   That is I1 verification, not a kernel proof. D3 is now
   narrowed to Lean elimination certificates for both
   equations (the §5 elimination was verified the same
   day; see the §5 principal-equation row).
7. Parts 1–9 and 13 compile via `bash compile_all.sh`
   (PASS on every file, no sorry/admit/axiom declarations);
   Parts 10–12 compile via `lake build`.
   The paper is still NOT 100% kernel-proved; the remaining
   kernel work is D1-polynomial-ℓ, D2-polynomial theory,
   D4 items 2–5.
   (D6 closed 2026-10-30; Part 8 added the same day — see
   the 2026-10-30 continuation item 5 above.)
