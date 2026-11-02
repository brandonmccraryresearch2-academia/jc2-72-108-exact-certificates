/-
  JC2 / GGHV formalization — Part 9: general
  valuation-extremum vertices (D1, general infrastructure).

  Source: Guccione, Guccione, Horruitiner, Valqui,
  arXiv:2204.14178v1, §§3–5. TeX source:
  ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.

  STATUS (2026-10-30): core Lean only, no Mathlib, no sorry,
  no axiom declarations. What IS proved here (kernel-checked):
  - A general maximal-valuation vertex function `maxVertDir`
    for a finite vertex list and a direction (ρ,σ), with
    last-max tie-breaking, and the two properties a
    maximal-valuation vertex must have: it lies in the list
    (`maxVert_mem`), and every vertex of the list has
    valuation at most its valuation (`maxVert_max`). The
    proofs are by induction on the list.
  - A minimal-valuation vertex `minVertDir`, defined as the
    maximal-valuation vertex for the negated direction,
    with the analogous membership and minimality theorems.
  - Concrete values for the Prop. 4.1 / §5 shapes: under
    (3,−1), maxVert is (6,16) for P and (9,24) for Q;
    under (1,0), maxVert is (6,18) for P and (9,27) for Q
    (the paper's en endpoints for those directions).
  What is NOT proved here, and must NOT be read into it:
  - `maxVertDir` / `minVertDir` are NOT the paper's en/st.
    Counterexample, proved here by `decide`: under
    (−1,1), maxVertDir on the P shape is (0,18), whereas
    the paper's Thm 5.1 condition is st_{−1,1}(P) = (6,18)
    (see Part 4 / CORRESPONDENCE.md, Thm 5.1 row).
    Neither the maximal nor the minimal valuation vertex
    under (−1,1) is (6,18) (minVertDir gives (1,1)).
    Hence en/st cannot be defined as valuation extremum
    alone: the paper's en/st must come from the [GGV*]
    definition (the (ρ,σ)-face of the Newton polygon with
    its own ordering, tied to the homogeneous part
    ℓ_{ρ,σ}), which is still INTERFACE. This file is
    valuation-extremum infrastructure; it does NOT
    discharge §3-120 en extremality, §3-84 I_M/I_m, or
    the Props. 4.1–4.4 reductions, and any claim that it
    does would be false.
-/

namespace JC2
namespace GGHV
namespace Part9

/-- Weighted valuation, as in Part 6 (restated standalone). -/
def dirVal (ρ σ : Int) (a b : Int) : Int := ρ * a + σ * b

/-- Maximal-valuation vertex of a list, last-max tie-break:
    scanning left to right, a later vertex replaces the
    current best only when its valuation is strictly
    greater (equivalently: when the current best is ≤ it,
    the later vertex wins). -/
def maxVertDir (ρ σ : Int) : List (Int × Int) → Option (Int × Int)
  | [] => none
  | v :: vs =>
    match maxVertDir ρ σ vs with
    | none => some v
    | some w => if dirVal ρ σ v.1 v.2 ≤ dirVal ρ σ w.1 w.2 then some w else some v

/-- Membership: the maximal-valuation vertex lies in the list. -/
theorem maxVert_mem {ρ σ : Int} {vs : List (Int × Int)} {v : Int × Int} :
    maxVertDir ρ σ vs = some v → v ∈ vs := by
  induction vs with
  | nil => simp [maxVertDir]
  | cons x xs ih =>
    intro h
    simp only [maxVertDir] at h
    cases hxs : maxVertDir ρ σ xs with
    | none =>
      simp only [hxs] at h
      have hv : x = v := Option.some.inj h
      subst hv
      exact List.mem_cons_self
    | some w =>
      simp only [hxs] at h
      by_cases hle : dirVal ρ σ x.1 x.2 ≤ dirVal ρ σ w.1 w.2
      · simp only [hle, ite_true] at h
        have hw : w = v := Option.some.inj h
        subst hw
        exact List.mem_cons_of_mem x (ih hxs)
      · simp only [hle, ite_false] at h
        have hv : x = v := Option.some.inj h
        subst hv
        exact List.mem_cons_self

/-- The maximal-valuation vertex is `none` only for the
    empty list. -/
theorem maxVert_none {ρ σ : Int} {vs : List (Int × Int)} :
    maxVertDir ρ σ vs = none → vs = [] := by
  induction vs with
  | nil => intro _; rfl
  | cons x xs _ =>
    intro h
    simp only [maxVertDir] at h
    cases hxs : maxVertDir ρ σ xs with
    | none => simp [hxs] at h
    | some w =>
      by_cases hle : dirVal ρ σ x.1 x.2 ≤ dirVal ρ σ w.1 w.2
      · simp [hxs, hle] at h
      · simp [hxs, hle] at h

/-- Maximality: every vertex of the list has valuation at
    most the maximal-valuation vertex's valuation. -/
theorem maxVert_max {ρ σ : Int} {vs : List (Int × Int)} {v w : Int × Int} :
    maxVertDir ρ σ vs = some v → w ∈ vs →
    dirVal ρ σ w.1 w.2 ≤ dirVal ρ σ v.1 v.2 := by
  induction vs generalizing v w with
  | nil => intro _ h; cases h
  | cons x xs ih =>
    intro h hmem
    simp only [maxVertDir] at h
    cases hxs : maxVertDir ρ σ xs with
    | none =>
      simp only [hxs] at h
      have hv : x = v := Option.some.inj h
      have hxs' : xs = [] := maxVert_none hxs
      subst hxs'; subst hv
      rcases List.mem_cons.mp hmem with rfl | hm
      · omega
      · cases hm
    | some u =>
      simp only [hxs] at h
      by_cases hle : dirVal ρ σ x.1 x.2 ≤ dirVal ρ σ u.1 u.2
      · simp only [hle, ite_true] at h
        have hu : u = v := Option.some.inj h
        subst hu
        rcases List.mem_cons.mp hmem with rfl | hm
        · exact hle
        · exact ih hxs hm
      · simp only [hle, ite_false] at h
        have hv : x = v := Option.some.inj h
        subst hv
        rcases List.mem_cons.mp hmem with rfl | hm
        · omega
        · have h1 := ih hxs hm
          omega

/-- Minimal-valuation vertex, via the negated direction. -/
def minVertDir (ρ σ : Int) (vs : List (Int × Int)) : Option (Int × Int) :=
  maxVertDir (-ρ) (-σ) vs

theorem dirVal_neg (ρ σ a b : Int) :
    dirVal (-ρ) (-σ) a b = -(dirVal ρ σ a b) := by
  simp only [dirVal, Int.neg_mul, ← Int.neg_add]

theorem minVert_mem {ρ σ : Int} {vs : List (Int × Int)} {v : Int × Int} :
    minVertDir ρ σ vs = some v → v ∈ vs :=
  maxVert_mem

theorem minVert_min {ρ σ : Int} {vs : List (Int × Int)} {v w : Int × Int} :
    minVertDir ρ σ vs = some v → w ∈ vs →
    dirVal ρ σ v.1 v.2 ≤ dirVal ρ σ w.1 w.2 := by
  intro h hmem
  have h2 := maxVert_max h hmem
  simp only [dirVal_neg] at h2
  omega

/-- Prop. 4.1 / §5 shapes (as in Part 8). -/
def shapeP : List (Int × Int) :=
  [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)]
def shapeQ : List (Int × Int) :=
  [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)]

/-- Concrete maximal-valuation vertices (last-max tie-break):
    these are the paper's en endpoints for (3,−1) and (1,0). -/
theorem maxVert_P_3m1 : maxVertDir 3 (-1) shapeP = some (6, 16) := by decide
theorem maxVert_Q_3m1 : maxVertDir 3 (-1) shapeQ = some (9, 24) := by decide
theorem maxVert_P_10 : maxVertDir 1 0 shapeP = some (6, 18) := by decide
theorem maxVert_Q_10 : maxVertDir 1 0 shapeQ = some (9, 27) := by decide

/-- The (−1,1) discrepancy: the maximal-valuation vertex
    under (−1,1) on the P shape is (0,18), and the
    minimal-valuation vertex is (1,1). The paper's
    Thm 5.1 condition is st_{−1,1}(P) = (6,18), which is
    neither. Hence valuation extremum alone does NOT
    define en/st; the [GGV*] face definition is still
    needed (see the file header). -/
theorem maxVert_P_m11 : maxVertDir (-1) 1 shapeP = some (0, 18) := by decide
theorem minVert_P_m11 : minVertDir (-1) 1 shapeP = some (1, 1) := by decide
theorem st_m11_not_extremum :
    maxVertDir (-1) 1 shapeP ≠ some (6, 18) ∧
    minVertDir (-1) 1 shapeP ≠ some (6, 18) := by
  constructor <;> decide

end Part9
end GGHV
end JC2
