/- Part 19 — D4 Part B, session 3: [GGV1] Cor. 7.4 / Thm 7.6(5),
    instance layer. [GGV1] = arXiv:1401.1784.

    Pins, checked against the TeX (published numbering differs
    from the TeX's name-labels, as with Prop. 8.2 in Part 18):

    - GGHV's Cor. 7.4 matches the TeX Corollary "fracciones de F"
      (and its st-variant "fracciones de F1") by conclusion-shape:
      if en_{ρ₀,σ₀}(F) = (p/q)(a/l,b) with p,q coprime, then for
      every direction (ρ,σ) in the interval past (ρ₀,σ₀) there is
      a (ρ,σ)-homogeneous R with ℓ_{ρ,σ}(P) = R^{qm}. GGHV's two
      clean instances are Prop. 4.2 (q = 3) and Prop. 4.3 (q = 4),
      verified below as exact rational scalings.

    - OPEN QUESTION recorded here, not papered over: the TeX
      "fracciones de F" carries hypothesis (3) b > a/l for
      (a/l,b) := (1/m)en_{ρ₀,σ₀}(P), but GGHV's Prop. 4.2 instance
      gives (a/l,b) = (24,9), where 9 < 24. Either the published
      Cor. 7.4 states condition (3) differently, or the pair is
      ordered differently in the published version, or the
      instance runs through the st-variant (whose condition is
      b < a/l — satisfied by (24,9) — but whose conclusion is
      about st, not en). Until the published [GGV1] text is
      checked, the instance data below are recorded WITHOUT
      condition (3), and no claim is made that the TeX corollary
      as printed applies to the Prop. 4.2 instance.

    - GGHV's Thm 7.6(5) matches the TeX Theorem "divisibilidad"
      (the divisibility theorem for regular corners): item (5)
      q_j | d_i for i > j > 0, and the type-II clause q_0 | d_i.
      The published item (5) is one of these clauses up to the
      version's index shift; the §3-120 instance uses the
      consequence q₁ | d₀, which is what is formalized below.
      The bound d₀ ≤ 4 (from st_{1,0}(P) = (8,28) = 4·(2,7)) is
      carried as a hypothesis: its proof needs the
      ℓ_{1,0}(P) = R^{md₀} theory, not the arithmetic here.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- Rational scaling, cleared of denominators: q • enF = p • (a,b),
    componentwise. This is en_{ρ₀,σ₀}(F) = (p/q)(a,b) in integers. -/
def scaling (p q : Int) (enF ab : Int × Int) : Prop :=
  q * enF.1 = p * ab.1 ∧ q * enF.2 = p * ab.2

/-- Prop. 4.2 instance (GGHV): (ρ₀,σ₀) = (−1,3), (a/l,b) = (24,9),
    en(F) = (16,6) = (2/3)(24,9). -/
example : scaling 2 3 (16, 6) (24, 9) := ⟨by decide, by decide⟩
example : Nat.gcd 2 3 = 1 := by decide

/-- Prop. 4.3 instance (GGHV): (ρ₀,σ₀) = (−1,4), (a/l,b) = (28,8),
    en(F) = (21,6) = (3/4)(28,8). -/
example : scaling 3 4 (21, 6) (28, 8) := ⟨by decide, by decide⟩
example : Nat.gcd 3 4 = 1 := by decide

/-- The Cor. 7.4 conclusion exponents: ℓ_{ρ,σ}(P) = R^{qm}, with
    the (m,n) = (2,3) pair parameter m = 2: q = 3 gives exponent 6,
    q = 4 gives exponent 8. -/
example : 3 * 2 = 6 := by decide
example : 4 * 2 = 8 := by decide

/-- Cor. 7.4 instance data (without condition (3) — see the open
    question in the header). `dir` is (ρ₀,σ₀); `ab` is (a/l,b)
    with l = 1 in both GGHV instances; `enF` is en_{ρ₀,σ₀}(F). -/
structure Cor74Data where
  dir : Int × Int
  ab : Int × Int
  p : Int
  q : Int
  hcop : Nat.gcd p.natAbs q.natAbs = 1
  enF : Int × Int
  hscale : scaling p q enF ab

/-- The Prop. 4.2 instance satisfies the Cor. 7.4 data. -/
def cor74_prop42 : Cor74Data where
  dir := (-1, 3)
  ab := (24, 9)
  p := 2
  q := 3
  hcop := by decide
  enF := (16, 6)
  hscale := ⟨by decide, by decide⟩

/-- The Prop. 4.3 instance satisfies the Cor. 7.4 data. -/
def cor74_prop43 : Cor74Data where
  dir := (-1, 4)
  ab := (28, 8)
  p := 3
  q := 4
  hcop := by decide
  enF := (21, 6)
  hscale := ⟨by decide, by decide⟩

/-- Divisibility arithmetic behind the §3-120 step: a positive
    integer divisible by q and bounded above by q equals q. -/
theorem eq_of_dvd_of_le {q d : Nat} (hd : 0 < d) (hdiv : q ∣ d)
    (hle : d ≤ q) : d = q := by
  have h1 := Nat.le_of_dvd hd hdiv
  omega

/-- §3-120 data: st_{1,0}(P) = (8,28) = 4·(2,7), with (2,7) primitive. -/
example : (4 * 2, 4 * 7) = (8, 28) := by decide
example : Nat.gcd 2 7 = 1 := by decide

/-- Thm 7.6(5) instance bundle: q₁ = 4 divides d₀, and d₀ ≤ 4.
    The bound is a hypothesis (see header); the conclusion d₀ = 4
    is then arithmetic. -/
structure Thm76Instance where
  q : Nat
  d : Nat
  hd : 0 < d
  hdiv : q ∣ d
  hle : d ≤ q

theorem thm76_instance_eq (I : Thm76Instance) : I.d = I.q :=
  eq_of_dvd_of_le I.hd I.hdiv I.hle

/-- The §3-120 instance: q₁ = 4, d₀ = 4. -/
example : (Thm76Instance.mk 4 4 (by decide) (by decide) (by decide)).d = 4 := by
  decide
