/- Part 20 — D4 Part B, session 4: remaining [GGV1] instances and
    Pred/Succ from ℓ. [GGV1] = arXiv:1401.1784.

    Contents, each pinned to the TeX:

    - Dir(P) (TeX Definition "forma debil"): the directions whose
      (ρ,σ)-face has more than one support point. At list level:
      a direction is in Dir when its face contains two terms with
      distinct exponents. Checked: (3,−1) is in Dir of the Prop. 4.1
      P list (face (1,1),(6,16)); (−1,1) is not (face [(0,18)] alone).
    - The CCW order on directions via cross product, with
      irreflexivity and asymmetry.
    - The "formula basica de orden" lemma: for exponents a,b, the
      (ρ,σ)-valuation comparison is exactly the cross-product
      comparison against the perpendicular direction — proved here
      as an identity of integer expressions, not as the paper's
      geometric lemma (whose Dir/order setup is the surrounding
      theory).
    - Succ/Pred (TeX Definition "Sucesor y predecesor"): Succ is
      the first Dir element encountered running counterclockwise
      from (ρ,σ); Pred the first clockwise. Formalized as the
      "no Dir element strictly between" characterization, plus
      the GGHV instance Succ_P(−1,4) = Succ_Q(−1,4) = (−2,7)
      (cross product 1 > 0, checked) and the Pred_P(−1,3) interval
      condition (Pred lies strictly between (0,−1) and (1,−1) in
      CCW order, as a condition, not a computed value).
    - Props. 1.13/2.1 instance (§5, GGHV): ℓ_{1,0}(P) = R² and
      ℓ_{1,0}(Q) = R³ with R = x³C₃, C₃ = y⁸(y+1). At list level:
      R's terms are (3,8),(3,9); pairwise exponent sums give R²
      endpoints (6,16),(6,18) and R³ endpoints (9,24),(9,27) —
      exactly the §5 face endpoints.
    - Def. 4.3 / Cor. 7.2 instance (§5 ψ-argument data): the
      (m,n) = (2,3) scalings (1/2)(6,16) = (1/3)(9,24) = (3,8) and
      (1/2)(6,18) = (1/3)(9,27) = (3,9), checked.
    - Prop. 2.11(3) instance data (§3-84): direction (7,−2) ∈ V_{>0},
      and the ℓ-form data (associated polynomial degree 3m,
      at most two factors, multiplicities multiples of m) carried
      as a record — the factor theorem itself is [GGV1]'s, not
      proved here.

    Still OPEN after Part B (carried forward, not closed by this
    session): the proof of Prop. 8.2 item (2), the k = 2
    parallel-edges exclusion, the Cor. 7.4 condition-(3) question,
    and the full Dir/Succ theory (uniqueness of Succ, consecutive
    directions < 180° apart). Part B's four sessions are done;
    what remains of D4 is Parts C–F.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- Weighted valuation (restated from Part 17). -/
def dirVal (ρ σ : Int) (a b : Int) : Int := ρ * a + σ * b

/-- Maximal-valuation vertex, last-max tie-break (Part 13, restated). -/
def maxVertDir (ρ σ : Int) : List (Int × Int) → Option (Int × Int)
  | [] => none
  | v :: vs =>
    match maxVertDir ρ σ vs with
    | none => some v
    | some w => if dirVal ρ σ v.1 v.2 ≤ dirVal ρ σ w.1 w.2 then some w else some v

/-- A term: exponent paired with its coefficient. -/
abbrev Term := (Int × Int) × Int

/-- Exponents of a term list. -/
def termExps (terms : List Term) : List (Int × Int) := terms.map Prod.fst

/-- Terms attaining maximal (ρ,σ)-valuation (Part 14, restated). -/
def faceTerms (ρ σ : Int) (terms : List Term) : List Term :=
  match maxVertDir ρ σ (termExps terms) with
  | none => []
  | some m => terms.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2)

/-- Cross product of two exponent/direction pairs. -/
def crossProd (a b : Int × Int) : Int := a.1 * b.2 - a.2 * b.1

/-- Dir(P) at list level: the face has two terms with distinct
    exponents (TeX "forma debil": #Supp(ℓ_{ρ,σ}(P)) > 1). -/
def isDir (ρ σ : Int) (terms : List Term) : Prop :=
  ∃ a b, a ∈ faceTerms ρ σ terms ∧ b ∈ faceTerms ρ σ terms ∧ a.1 ≠ b.1

/-- Prop. 4.1 P list (Part 3 `prop41_P`), unit coefficients. -/
def shapePTerms : List Term :=
  [((0, 0), 1), ((1, 1), 1), ((6, 16), 1), ((6, 18), 1), ((0, 18), 1)]

/-- (3,−1) is in Dir of the Prop. 4.1 P list. -/
example : isDir 3 (-1) shapePTerms :=
  ⟨((1, 1), 1), ((6, 16), 1), by decide, by decide, by decide⟩

/-- (−1,1) is not in Dir of the Prop. 4.1 P list: its face is a
    single term. -/
example : ¬ isDir (-1) 1 shapePTerms := by
  intro h
  obtain ⟨a, b, ha, hb, hne⟩ := h
  have hface : faceTerms (-1) 1 shapePTerms = [((0, 18), 1)] := by decide
  rw [hface] at ha hb
  simp only [List.mem_singleton] at ha hb
  exact hne (by rw [ha, hb])

/-- CCW order on directions: (ρ,σ) < (ρ',σ') iff the cross product
    is positive. -/
def dirLt (a b : Int × Int) : Prop := 0 < crossProd a b

theorem dirLt_irrefl (a : Int × Int) : ¬ dirLt a a := by
  show ¬ 0 < crossProd a a
  simp only [crossProd]
  rw [Int.mul_comm a.2 a.1]
  simp

theorem dirLt_asymm {a b : Int × Int} (h : dirLt a b) : ¬ dirLt b a := by
  show ¬ 0 < crossProd b a
  simp only [dirLt, crossProd] at h ⊢
  rw [Int.mul_comm b.1 a.2, Int.mul_comm b.2 a.1]
  omega

/-- "Formula basica de orden", algebraic core: the (ρ,σ)-valuation
    difference of two exponents equals the cross product of
    (ρ,σ) with the perpendicular direction. Hence the valuation
    comparison is exactly the CCW-order comparison. -/
theorem valuation_diff_eq_cross {ρ σ : Int} {a b : Int × Int} :
    dirVal ρ σ a.1 a.2 - dirVal ρ σ b.1 b.2 =
    crossProd (ρ, σ) (b.2 - a.2, a.1 - b.1) := by
  simp only [dirVal, crossProd]
  rw [Int.mul_sub, Int.mul_sub]
  omega

theorem valuation_gt_iff_dirLt {ρ σ : Int} {a b : Int × Int} :
    dirVal ρ σ a.1 a.2 > dirVal ρ σ b.1 b.2 ↔
    dirLt (ρ, σ) (b.2 - a.2, a.1 - b.1) := by
  show dirVal ρ σ a.1 a.2 > dirVal ρ σ b.1 b.2 ↔
    0 < crossProd (ρ, σ) (b.2 - a.2, a.1 - b.1)
  rw [← valuation_diff_eq_cross]
  omega

/-- Succ from a direction, "no Dir element strictly between"
    characterization (TeX "Sucesor y predecesor"): δ is the
    successor of `from` among `dirs` when δ is in `dirs`, lies
    strictly counterclockwise from `from`, and no other element of
    `dirs` lies strictly between `from` and δ. -/
def isSuccFrom (src δ : Int × Int) (dirs : List (Int × Int)) : Prop :=
  δ ∈ dirs ∧ dirLt src δ ∧
  ∀ δ' ∈ dirs, dirLt src δ' → dirLt δ' δ → δ' = δ

/-- GGHV instance: Succ_P(−1,4) = Succ_Q(−1,4) = (−2,7) lies
    strictly counterclockwise from (−1,4) (cross product 1). -/
example : dirLt (-1, 4) (-2, 7) := by
  show 0 < crossProd (-1, 4) (-2, 7)
  decide

/-- GGHV instance condition: Pred_P(−1,3) lies strictly between
    (0,−1) and (1,−1) in CCW order — recorded as the condition a
    predecessor must satisfy, not as a computed value. -/
def predInInterval (p : Int × Int) : Prop :=
  dirLt (0, -1) p ∧ dirLt p (1, -1)

/-- Monomial product of two term lists: exponents add, coefficients
    multiply. -/
def termMul (terms1 terms2 : List Term) : List Term :=
  terms1.flatMap (fun t1 => terms2.map (fun t2 =>
    ((t1.1.1 + t2.1.1, t1.1.2 + t2.1.2), t1.2 * t2.2)))

/-- R = x³C₃, C₃ = y⁸(y+1): terms (3,8),(3,9). -/
def rTerms : List Term := [((3, 8), 1), ((3, 9), 1)]

/-- Props. 1.13/2.1 instance, P side: R² has endpoints
    (6,16),(6,18) — the §5 P face endpoints. -/
example : ((6, 16), 1) ∈ termMul rTerms rTerms := by decide
example : ((6, 18), 1) ∈ termMul rTerms rTerms := by decide

/-- Props. 1.13/2.1 instance, Q side: R³ has endpoints
    (9,24),(9,27) — the §5 Q face endpoints. -/
example : ((9, 24), 1) ∈ termMul (termMul rTerms rTerms) rTerms := by decide
example : ((9, 27), 1) ∈ termMul (termMul rTerms rTerms) rTerms := by decide

/-- Def. 4.3 / Cor. 7.2 instance (§5 ψ-argument data): the
    (m,n) = (2,3) scalings to the common base points (3,8),(3,9). -/
example : (6 / 2, 16 / 2) = (3, 8) := by decide
example : (9 / 3, 24 / 3) = (3, 8) := by decide
example : (6 / 2, 18 / 2) = (3, 9) := by decide
example : (9 / 3, 27 / 3) = (3, 9) := by decide

/-- Prop. 2.11(3) instance data (§3-84): direction (7,−2) ∈ V_{>0},
    associated-polynomial degree 3m (m = 2, so 6), at most two
    factors, multiplicities multiples of m. The factor theorem is
    [GGV1]'s; this record carries its instance data only. -/
structure Prop211Data where
  dir : Int × Int
  hdir : Int.gcd dir.1 dir.2 = 1 ∧ 0 < dir.1 + dir.2
  m : Nat
  degree : Nat
  hdeg : degree = 3 * m
  maxFactors : Nat
  hfac : maxFactors ≤ 2

def prop211_s384 : Prop211Data where
  dir := (7, -2)
  hdir := ⟨by decide, by decide⟩
  m := 2
  degree := 6
  hdeg := by decide
  maxFactors := 2
  hfac := by decide
