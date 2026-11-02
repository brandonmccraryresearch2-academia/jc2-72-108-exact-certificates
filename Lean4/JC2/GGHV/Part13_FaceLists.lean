/-
  JC2 / GGHV formalization — Part 13: (ρ,σ)-face lists
  (D4 item 1, support level).

  Source: Guccione, Guccione, Horruitiner, Valqui,
  arXiv:2204.14178v1, §§3–5. TeX source:
  ~/workspace/research/rss-monitor/tex/2204.14178/main.tex.

  STATUS (2026-10-30): core Lean only, no Mathlib, no
  sorry, no axiom declarations. What IS proved here
  (kernel-checked):
  - `dirVal`, `maxVertDir`, `maxVert_mem`,
    `maxVert_none`, `maxVert_max` restated standalone
    from Part 9 (verbatim, so this file compiles alone).
  - The (ρ,σ)-face list `faceList`: the vertices of a
    list attaining the maximal valuation. Membership
    characterization (`faceList_mem`), subset
    (`faceList_subset`), maximality
    (`faceList_max`: every face vertex dominates every
    list vertex in valuation), and nonemptiness for
    nonempty lists (`faceList_nonempty`).
  - Concrete faces for the Prop. 4.1 / §5 shapes:
    under (3,−1), P-face [(1,1),(6,16)] and
    Q-face [(1,0),(9,24)]; under (1,0), P-face
    [(6,16),(6,18)] and Q-face [(9,24),(9,27)] —
    exactly the §5 en/st endpoints of Part 8, now as
    full faces rather than single vertices.
  What is NOT proved here:
  - The polynomial homogeneous part ℓ_{ρ,σ} itself:
    this file is the support level (which vertices lie
    on the face). The polynomial ℓ (coefficients,
    bilinearity, the bracket of homogeneous parts) needs
    the D2 polynomial theory and is still open.
  - The paper's en/st as a general definition: the
    Part 9 negative result stands — under (−1,1) the
    face of the P shape is NOT {(6,18)}, so en/st is
    not this face in general. This file gives the face
    infrastructure D4 item 1 needs; it does not close
    D4.
-/

namespace JC2
namespace GGHV
namespace Part13

/-- Weighted valuation, as in Parts 6/9 (restated standalone). -/
def dirVal (ρ σ : Int) (a b : Int) : Int := ρ * a + σ * b

/-- Maximal-valuation vertex of a list, last-max tie-break
    (from Part 9, restated standalone). -/
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

/-- The (ρ,σ)-face list: vertices attaining the maximal
    valuation. Empty when the list is empty. -/
def faceList (ρ σ : Int) (vs : List (Int × Int)) : List (Int × Int) :=
  match maxVertDir ρ σ vs with
  | none => []
  | some m => vs.filter (fun v => dirVal ρ σ v.1 v.2 = dirVal ρ σ m.1 m.2)

/-- Membership characterization of the face. -/
theorem faceList_mem {ρ σ : Int} {vs : List (Int × Int)} {v : Int × Int} :
    v ∈ faceList ρ σ vs ↔
      ∃ m, maxVertDir ρ σ vs = some m ∧ v ∈ vs ∧
        dirVal ρ σ v.1 v.2 = dirVal ρ σ m.1 m.2 := by
  cases h : maxVertDir ρ σ vs with
  | none =>
    constructor
    · intro hv
      simp only [faceList, h] at hv
      cases hv
    · rintro ⟨m, hm, -, -⟩
      exact absurd hm.symm (Option.some_ne_none m)
  | some m =>
    have hface : faceList ρ σ vs =
        vs.filter (fun v => dirVal ρ σ v.1 v.2 = dirVal ρ σ m.1 m.2) := by
      simp only [faceList, h]
    constructor
    · intro hv
      rw [hface, List.mem_filter] at hv
      exact ⟨m, rfl, hv.1, of_decide_eq_true hv.2⟩
    · rintro ⟨m', hm', hv, hval⟩
      have hmm : m' = m := (Option.some.inj hm').symm
      subst hmm
      rw [hface, List.mem_filter]
      exact ⟨hv, by simp [hval]⟩

/-- Face vertices lie in the list. -/
theorem faceList_subset {ρ σ : Int} {vs : List (Int × Int)} {v : Int × Int} :
    v ∈ faceList ρ σ vs → v ∈ vs :=
  fun hv => (faceList_mem.mp hv).choose_spec.2.1

/-- Every face vertex dominates every list vertex in
    valuation. -/
theorem faceList_max {ρ σ : Int} {vs : List (Int × Int)} {v w : Int × Int} :
    v ∈ faceList ρ σ vs → w ∈ vs →
    dirVal ρ σ w.1 w.2 ≤ dirVal ρ σ v.1 v.2 := by
  intro hv hw
  obtain ⟨m, hm, -, hval⟩ := faceList_mem.mp hv
  have hle := maxVert_max hm hw
  omega

/-- A nonempty list has a nonempty face. -/
theorem faceList_nonempty {ρ σ : Int} {vs : List (Int × Int)} :
    vs ≠ [] → faceList ρ σ vs ≠ [] := by
  intro hne hface
  cases h : maxVertDir ρ σ vs with
  | none =>
    exact hne (maxVert_none h)
  | some m =>
    have hm : m ∈ faceList ρ σ vs :=
      faceList_mem.mpr ⟨m, h, maxVert_mem h, rfl⟩
    rw [hface] at hm
    cases hm

/-- Prop. 4.1 / §5 shapes (as in Parts 8/9). -/
def shapeP : List (Int × Int) :=
  [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)]
def shapeQ : List (Int × Int) :=
  [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)]

/-- Concrete faces: the §5 en/st endpoints, as full faces. -/
theorem face_P_3m1 : faceList 3 (-1) shapeP = [(1, 1), (6, 16)] := by decide
theorem face_Q_3m1 : faceList 3 (-1) shapeQ = [(1, 0), (9, 24)] := by decide
theorem face_P_10 : faceList 1 0 shapeP = [(6, 16), (6, 18)] := by decide
theorem face_Q_10 : faceList 1 0 shapeQ = [(9, 24), (9, 27)] := by decide

end Part13
end GGHV
end JC2
