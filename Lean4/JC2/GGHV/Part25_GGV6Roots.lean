/- Part 25 — D4 Part D, session 1: [GGV6] root theory, instance
    layer. [GGV6] = "The Jacobian Conjecture: Approximate roots
    and intersection numbers" (Pro Mathematica 30 (2019) 51–89),
    arXiv:1708.09367 — among the TeX sources, read here from its
    TeX.

    Pins, checked in the TeX:

    - Major/minor final π-roots (TeX Definition "major and minor
      roots"): a final π-root τ of P is minor iff λ_τ = 0, major
      iff λ_τ > 0. P_m / P_M are the sets of minor / major final
      π-roots.
    - I_M = I(P,Q) (TeX Theorem "Interseccion con raices
      mayores"): I_M = Σ_{τ ∈ P_M} |D_τ^{P_ξ}| λ_τ^Q equals the
      intersection number. I_m ≤ I(P,Q) (TeX Theorem "numero de
      interseccion con raices menores"): I_m =
      1 − Σ_{τ ∈ P_m} (δ_τ + 1) is at most I(P,Q). Combined:
      I_m ≤ I_M — this is GGHV's "Thm 7.3: I_M ≥ I_m". The two
      theorems themselves are [GGV6]'s, carried as a bundle;
      the combination is arithmetic.
    - §3-84 instance (GGHV): I_M = Σ |D| λ^Q = 7·(2m)·(1/7) =
      2(j+2); at j = 0 (m = 2), I_M = 4. Minor roots: one final
      minor root with δ_τ = −3, and seven final minor roots at
      A₁ = (9/7,1) with δ_τ = −9/7 each. Hence I_m =
      1 − (−3+1) − 7·(−9/7+1) = 1 + 2 + 2 = 5. Since 5 ≤ 4 is
      false, the case is discarded. All of this arithmetic is
      checked below (fractions cleared: 7·(−9/7+1) = −2).
    - The §3-84 λ value: λ^Q = 1/7 at k = 1, l = 7 (the major
      root's λ, positive, hence major by the definition).

    Still open in Part D (sessions 2–3): Props. 6.4/6.6 and
    Ex. 6.7 as statements (their published numbers do not appear
    in the arXiv TeX's name-labels; the §3-84 δ/λ data above are
    their instance content), and Prop. 2.5 (Prop. 4.3 instance:
    Pred_P(1,0) ∈ {(1,−2), (1,−3)}).

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- Minor vs major final π-root, by the sign of λ_τ (TeX
    Definition "major and minor roots"). λ is carried as an
    integer numerator over a positive denominator where needed;
    the sign is what the definition uses. -/
def isMinorRoot (lam : Int) : Prop := lam = 0
def isMajorRoot (lam : Int) : Prop := 0 < lam

/-- §3-84: λ^Q = 1/7 > 0, hence a major root. (Numerator 1 over
    denominator 7; positivity is the numerator's sign.) -/
example : isMajorRoot 1 := by
  show 0 < (1 : Int)
  decide

/-- I_M = I(P,Q) and I_m ≤ I(P,Q) combine to I_m ≤ I_M
    (GGHV's Thm 7.3), as a carried bundle: the two theorems are
    [GGV6]'s; only the combination is proved here. -/
structure IntersectionFormulas where
  IM : Int
  Im : Int
  IPQ : Int
  hM : IM = IPQ
  hm : Im ≤ IPQ

theorem im_le_IM (F : IntersectionFormulas) : F.Im ≤ F.IM := by
  rw [F.hM]
  exact F.hm

/-- §3-84, I_M: 7·(2m)·(1/7) = 2m; at j = 0, m = j+2 = 2,
    I_M = 4. Cleared: 7·(2·2) = 28, 28/7 = 4. -/
example : 7 * (2 * 2) / 7 = 4 := by decide
example : 0 + 2 = 2 := by decide

/-- §3-84, I_m pieces: (−3+1) = −2; 7·(−9/7+1) = −2, cleared as
    7·(−9+7)/7 = −2. -/
example : -3 + 1 = -2 := by decide
example : 7 * (-9 + 7) / 7 = -2 := by decide

/-- §3-84, I_m: 1 − (−2) − (−2) = 5. -/
example : 1 - (-2) - (-2) = 5 := by decide

/-- §3-84 discard, as arithmetic: I_M = 4, I_m = 5, and
    I_m ≤ I_M together are contradictory. -/
theorem discard_84_arith (IM Im : Int) (hM : IM = 4) (hm : Im = 5)
    (hle : Im ≤ IM) : False := by omega

/-- §3-84 root data, carried: one final minor root with
    δ = −3; seven final minor roots with δ = −9/7 (numerator
    −9 over denominator 7); major root λ^Q numerator 1 over
    denominator 7 at k = 1, l = 7. -/
structure S384Roots where
  minorDeltas : List (Int × Int)
  majorLamNum : Int
  majorLamDen : Int
  hmajor : 0 < majorLamNum

def s384_roots : S384Roots where
  minorDeltas := [(-3, 1), (-9, 7), (-9, 7), (-9, 7), (-9, 7), (-9, 7), (-9, 7), (-9, 7)]
  majorLamNum := 1
  majorLamDen := 7
  hmajor := by decide
