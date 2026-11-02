/- Part 15 — D4 Part A, session 2: face endpoints.
    D4 roadmap item 1, polynomial level, second step.

    Part 14 gave coefficient-carrying face terms. This file adds the
    endpoints of a face: the first and last face terms in list order
    (list order = the polygon traversal order as given). The endpoints
    lie in the face and attain maximal valuation, and for the §5 shapes
    they are exactly Part 8's en/st endpoint pairs under (3,−1) and
    (1,0), as unordered pairs.

    Scope, stated plainly: this is NOT the paper's en/st definition.
    The paper's st_{−1,1}(P) = (6,18) (Thm 5.1) is not an endpoint of
    the (−1,1)-face — the (−1,1)-face of the P shape is [(0,18)] alone,
    proved below — so the paper's en/st must come from the [GGV*] face
    definition tied to ℓ, whose primary text ([GGV1]) is Part B work,
    not something reconstructed here. Session 2 closes the endpoint
    layer; it does not close en/st as in the paper.

    Core Lean only, standalone. `dirVal` / `maxVertDir` / `maxVert_mem` /
    `maxVert_none` / `maxVert_max` / `termExps` / `faceTerms` /
    `faceTerms_mem` are restated verbatim from Parts 13–14, following
    this project's standalone-file convention. No sorry and no
    forbidden declarations. -/

/-- Weighted valuation, as in Parts 6/9/13 (restated standalone). -/
def dirVal (ρ σ : Int) (a b : Int) : Int := ρ * a + σ * b

/-- Maximal-valuation vertex of a list, last-max tie-break
    (from Part 13, restated standalone). -/
def maxVertDir (ρ σ : Int) : List (Int × Int) → Option (Int × Int)
  | [] => none
  | v :: vs =>
    match maxVertDir ρ σ vs with
    | none => some v
    | some w => if dirVal ρ σ v.1 v.2 ≤ dirVal ρ σ w.1 w.2 then some w else some v

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

/-- A term: exponent paired with its coefficient. -/
abbrev Term := (Int × Int) × Int

/-- Exponents of a term list. -/
def termExps (terms : List Term) : List (Int × Int) := terms.map Prod.fst

/-- Terms attaining maximal (ρ,σ)-valuation (from Part 14). -/
def faceTerms (ρ σ : Int) (terms : List Term) : List Term :=
  match maxVertDir ρ σ (termExps terms) with
  | none => []
  | some m => terms.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2)

/-- Membership characterization of the face terms (from Part 14). -/
theorem faceTerms_mem {ρ σ : Int} {terms : List Term} {t : Term} :
    t ∈ faceTerms ρ σ terms ↔
    ∃ m, maxVertDir ρ σ (termExps terms) = some m ∧ t ∈ terms ∧
      dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2 := by
  cases h : maxVertDir ρ σ (termExps terms) with
  | none =>
    constructor
    · intro hv
      simp only [faceTerms, h] at hv
      cases hv
    · rintro ⟨m, hm, -, -⟩
      exact absurd hm.symm (Option.some_ne_none m)
  | some m =>
    have hface : faceTerms ρ σ terms =
        terms.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2) := by
      simp only [faceTerms, h]
    constructor
    · intro hv
      rw [hface, List.mem_filter] at hv
      exact ⟨m, rfl, hv.1, of_decide_eq_true hv.2⟩
    · rintro ⟨m', hm', hv, hval⟩
      have hmm : m' = m := (Option.some.inj hm').symm
      subst hmm
      rw [hface, List.mem_filter]
      exact ⟨hv, by simp [hval]⟩

/-- The endpoints of a face: first and last face terms in list order.
    `none` exactly when the term list is empty. -/
def faceEndpoints (ρ σ : Int) (terms : List Term) : Option (Term × Term) :=
  match faceTerms ρ σ terms with
  | [] => none
  | t :: ts => some (t, List.getLast (t :: ts) (by simp))

/-- Both endpoints lie in the face. -/
theorem faceEndpoints_mem {ρ σ : Int} {terms : List Term} {a b : Term}
    (h : faceEndpoints ρ σ terms = some (a, b)) :
    a ∈ faceTerms ρ σ terms ∧ b ∈ faceTerms ρ σ terms := by
  cases hf : faceTerms ρ σ terms with
  | nil => simp [faceEndpoints, hf] at h
  | cons t ts =>
    simp only [faceEndpoints, hf] at h
    have hpair : (t, List.getLast (t :: ts) (by simp)) = (a, b) :=
      Option.some.inj h
    obtain ⟨ha, hb⟩ := Prod.mk.inj hpair
    constructor
    · rw [← ha]; exact List.mem_cons_self
    · rw [← hb]; exact List.getLast_mem (by simp : (t :: ts) ≠ [])

/-- Both endpoints attain maximal valuation: every exponent of the
    term list has valuation at most each endpoint's valuation. -/
theorem faceEndpoints_max {ρ σ : Int} {terms : List Term} {a b : Term}
    (h : faceEndpoints ρ σ terms = some (a, b)) {v : Int × Int}
    (hv : v ∈ termExps terms) :
    dirVal ρ σ v.1 v.2 ≤ dirVal ρ σ a.1.1 a.1.2 ∧
    dirVal ρ σ v.1 v.2 ≤ dirVal ρ σ b.1.1 b.1.2 := by
  obtain ⟨ham, hbm⟩ := faceEndpoints_mem h
  obtain ⟨m, hm, -, haval⟩ := faceTerms_mem.mp ham
  obtain ⟨m', hm', -, hbval⟩ := faceTerms_mem.mp hbm
  have h1 := maxVert_max hm hv
  have h2 := maxVert_max hm' hv
  omega

/-- §5 P-shape with unit coefficients (placeholders, as in Part 14). -/
def shapePTerms : List Term :=
  [((0, 0), 1), ((1, 1), 1), ((6, 16), 1), ((6, 18), 1), ((0, 18), 1)]

/-- §5 Q-shape with unit coefficients (placeholders, as in Part 14). -/
def shapeQTerms : List Term :=
  [((0, 0), 1), ((1, 0), 1), ((9, 24), 1), ((9, 27), 1), ((0, 27), 1)]

/-- §5 endpoints under (3,−1): exactly Part 8's en/st endpoint pairs. -/
example : faceEndpoints 3 (-1) shapePTerms =
    some ((((1, 1), 1), ((6, 16), 1))) := by decide
example : faceEndpoints 3 (-1) shapeQTerms =
    some ((((1, 0), 1), ((9, 24), 1))) := by decide

/-- §5 endpoints under (1,0): exactly Part 8's en/st endpoint pairs. -/
example : faceEndpoints 1 0 shapePTerms =
    some ((((6, 16), 1), ((6, 18), 1))) := by decide
example : faceEndpoints 1 0 shapeQTerms =
    some ((((9, 24), 1), ((9, 27), 1))) := by decide

/-- Negative result: the (−1,1)-face of the P shape is a single vertex,
    so its endpoints are both (0,18) — not Thm 5.1's st_{−1,1}(P) = (6,18).
    The paper's en/st is therefore not this endpoint construction. -/
example : faceEndpoints (-1) 1 shapePTerms =
    some ((((0, 18), 1), ((0, 18), 1))) := by decide

theorem faceEndpoints_m11_ne_st51 :
    (faceEndpoints (-1) 1 shapePTerms).map (fun p => p.1.1) ≠ some (6, 18) := by
  decide
