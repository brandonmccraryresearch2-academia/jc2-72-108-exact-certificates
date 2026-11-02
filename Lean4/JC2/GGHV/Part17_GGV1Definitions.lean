/- Part 17 — D4 Part B, session 1: [GGV1] direction/edge definitions layer.
    [GGV1] = Guccione–Guccione–Valqui, "On the shape of possible
    counterexamples to the Jacobian conjecture", arXiv:1401.1784
    (the shape paper; GGHV §3 cites it as the source of the
    direction/edge theory). Primary text read from
    `guccione-papers/tex/1401.1784/main.tex`.

    Definitions formalized here, at the term-list level:
    - V = coprime integer directions; V_{>0} = {ρ+σ > 0} ([GGV1] §1).
    - (ρ,σ)-homogeneous term lists: every term has the same
      (ρ,σ)-valuation. Face terms are homogeneous (lemma below).
    - st/en of a face by the paper's Remark (starting vs end):
      for (ρ,σ) ∈ V_{>0}, st = Supp(ℓ_{1,−1}(ℓ_{ρ,σ}(P))) and
      en = Supp(ℓ_{−1,1}(ℓ_{ρ,σ}(P))) — i.e. st is the face term
      maximizing the secondary valuation (1,−1), en the face term
      maximizing (−1,1). This is the paper's definition, not the
      list-order endpoints of Part 15 (which agree with it on the
      §5 faces checked, but are not the definition).

    Clarification recorded here (it corrects the framing of the
    Parts 9/15 "negative result"): the shape list used in Parts 8,
    13, 15 is Part 3's `prop41_P` — the Prop. 4.1 polygon
    [(0,0),(1,1),(6,16),(6,18),(0,18)]. GGHV Thm 5.1's §5 polygon
    is a different, hypothetical polygon, constrained only by the
    stated en/st conditions (en_{3,−1} = st_{1,0} = (6,16),
    st_{−1,1} = en_{1,0} = (6,18)); its (−1,1)-face need not
    contain (0,18) at all. So the (−1,1) endpoints (0,18),(0,18)
    on prop41_P are NOT a contradiction with Thm 5.1 — they are
    endpoints on a different polygon. The negative result stands
    exactly as stated (about prop41_P), and no longer carries the
    suggestion that GGHV's theorem is inconsistent with [GGV1].

    Core Lean only, standalone. `dirVal` / `maxVertDir` / `termExps` /
    `faceTerms` / `faceTerms_mem` are restated from Parts 13–15.
    No sorry and no forbidden declarations. -/

/-- Weighted valuation (Parts 6/9/13, restated standalone). -/
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

/-- Membership characterization of the face terms (Part 14, restated). -/
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

/-- [GGV1] §1: a direction is a coprime integer pair. -/
def isDirection (ρ σ : Int) : Prop := Int.gcd ρ σ = 1

/-- [GGV1] §1: V_{>0} = directions with ρ + σ > 0. -/
def isDirectionPos (ρ σ : Int) : Prop := isDirection ρ σ ∧ 0 < ρ + σ

/-- A term list is (ρ,σ)-homogeneous when all its terms share one
    (ρ,σ)-valuation — the list-level form of P = ℓ_{ρ,σ}(P). -/
def isHomog (ρ σ : Int) (terms : List Term) : Prop :=
  ∃ c : Int, ∀ t ∈ terms, dirVal ρ σ t.1.1 t.1.2 = c

/-- Face terms are (ρ,σ)-homogeneous: they all attain the maximal
    valuation. -/
theorem faceTerms_homog {ρ σ : Int} {terms : List Term} :
    isHomog ρ σ (faceTerms ρ σ terms) := by
  cases h : maxVertDir ρ σ (termExps terms) with
  | none =>
    refine ⟨0, fun t ht => ?_⟩
    simp only [faceTerms, h] at ht
    cases ht
  | some m =>
    refine ⟨dirVal ρ σ m.1 m.2, fun t ht => ?_⟩
    obtain ⟨m', hm', -, hval⟩ := faceTerms_mem.mp ht
    have h2 : maxVertDir ρ σ (termExps terms) = some m := h
    rw [hm'] at h2
    have hmm : m' = m := Option.some.inj h2
    rw [hmm] at hval
    exact hval

/-- Face term maximizing the secondary valuation (1,−1): the
    st-candidate, by first-max recursion over the face list. -/
def stFaceAux : List Term → Option Term
  | [] => none
  | t :: ts =>
    match stFaceAux ts with
    | none => some t
    | some s => if dirVal 1 (-1) s.1.1 s.1.2 ≤ dirVal 1 (-1) t.1.1 t.1.2
                then some t else some s

/-- Face term maximizing the secondary valuation (−1,1): the
    en-candidate. -/
def enFaceAux : List Term → Option Term
  | [] => none
  | t :: ts =>
    match enFaceAux ts with
    | none => some t
    | some s => if dirVal (-1) 1 s.1.1 s.1.2 ≤ dirVal (-1) 1 t.1.1 t.1.2
                then some t else some s

theorem stFaceAux_mem {ts : List Term} {s : Term} :
    stFaceAux ts = some s → s ∈ ts := by
  induction ts with
  | nil => simp [stFaceAux]
  | cons t ts ih =>
    intro h
    simp only [stFaceAux] at h
    cases hs : stFaceAux ts with
    | none =>
      simp only [hs] at h
      have hv : t = s := Option.some.inj h
      subst hv
      exact List.mem_cons_self
    | some u =>
      simp only [hs] at h
      by_cases hle : dirVal 1 (-1) u.1.1 u.1.2 ≤ dirVal 1 (-1) t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        have hv : t = s := Option.some.inj h
        subst hv
        exact List.mem_cons_self
      · simp only [hle, ite_false] at h
        have hv : u = s := Option.some.inj h
        subst hv
        exact List.mem_cons_of_mem t (ih hs)

theorem stFaceAux_none {ts : List Term} :
    stFaceAux ts = none → ts = [] := by
  cases ts with
  | nil => intro _; rfl
  | cons t ts =>
    intro h
    simp only [stFaceAux] at h
    cases hs : stFaceAux ts with
    | none => rw [hs] at h; exact absurd h (Option.some_ne_none t)
    | some v =>
      rw [hs] at h
      dsimp only at h
      by_cases hle : dirVal 1 (-1) v.1.1 v.1.2 ≤ dirVal 1 (-1) t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        exact absurd h (Option.some_ne_none t)
      · simp only [hle, ite_false] at h
        exact absurd h (Option.some_ne_none v)

theorem stFaceAux_max {ts : List Term} {s u : Term} :
    stFaceAux ts = some s → u ∈ ts →
    dirVal 1 (-1) u.1.1 u.1.2 ≤ dirVal 1 (-1) s.1.1 s.1.2 := by
  induction ts generalizing s u with
  | nil => intro _ h; cases h
  | cons t ts ih =>
    intro h hmem
    simp only [stFaceAux] at h
    cases hs : stFaceAux ts with
    | none =>
      simp only [hs] at h
      have hv : t = s := Option.some.inj h
      have hts : ts = [] := stFaceAux_none hs
      subst hts; subst hv
      rcases List.mem_cons.mp hmem with rfl | hm
      · omega
      · cases hm
    | some v =>
      simp only [hs] at h
      by_cases hle : dirVal 1 (-1) v.1.1 v.1.2 ≤ dirVal 1 (-1) t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        have hv : t = s := Option.some.inj h
        subst hv
        rcases List.mem_cons.mp hmem with rfl | hm
        · omega
        · have h1 := ih hs hm
          omega
      · simp only [hle, ite_false] at h
        have hv : v = s := Option.some.inj h
        subst hv
        rcases List.mem_cons.mp hmem with rfl | hm
        · omega
        · exact ih hs hm

theorem enFaceAux_mem {ts : List Term} {s : Term} :
    enFaceAux ts = some s → s ∈ ts := by
  induction ts with
  | nil => simp [enFaceAux]
  | cons t ts ih =>
    intro h
    simp only [enFaceAux] at h
    cases hs : enFaceAux ts with
    | none =>
      simp only [hs] at h
      have hv : t = s := Option.some.inj h
      subst hv
      exact List.mem_cons_self
    | some u =>
      simp only [hs] at h
      by_cases hle : dirVal (-1) 1 u.1.1 u.1.2 ≤ dirVal (-1) 1 t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        have hv : t = s := Option.some.inj h
        subst hv
        exact List.mem_cons_self
      · simp only [hle, ite_false] at h
        have hv : u = s := Option.some.inj h
        subst hv
        exact List.mem_cons_of_mem t (ih hs)

theorem enFaceAux_none {ts : List Term} :
    enFaceAux ts = none → ts = [] := by
  cases ts with
  | nil => intro _; rfl
  | cons t ts =>
    intro h
    simp only [enFaceAux] at h
    cases hs : enFaceAux ts with
    | none => rw [hs] at h; exact absurd h (Option.some_ne_none t)
    | some v =>
      rw [hs] at h
      dsimp only at h
      by_cases hle : dirVal (-1) 1 v.1.1 v.1.2 ≤ dirVal (-1) 1 t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        exact absurd h (Option.some_ne_none t)
      · simp only [hle, ite_false] at h
        exact absurd h (Option.some_ne_none v)

theorem enFaceAux_max {ts : List Term} {s u : Term} :
    enFaceAux ts = some s → u ∈ ts →
    dirVal (-1) 1 u.1.1 u.1.2 ≤ dirVal (-1) 1 s.1.1 s.1.2 := by
  induction ts generalizing s u with
  | nil => intro _ h; cases h
  | cons t ts ih =>
    intro h hmem
    simp only [enFaceAux] at h
    cases hs : enFaceAux ts with
    | none =>
      simp only [hs] at h
      have hv : t = s := Option.some.inj h
      have hts : ts = [] := enFaceAux_none hs
      subst hts; subst hv
      rcases List.mem_cons.mp hmem with rfl | hm
      · omega
      · cases hm
    | some v =>
      simp only [hs] at h
      by_cases hle : dirVal (-1) 1 v.1.1 v.1.2 ≤ dirVal (-1) 1 t.1.1 t.1.2
      · simp only [hle, ite_true] at h
        have hv : t = s := Option.some.inj h
        subst hv
        rcases List.mem_cons.mp hmem with rfl | hm
        · omega
        · have h1 := ih hs hm
          omega
      · simp only [hle, ite_false] at h
        have hv : v = s := Option.some.inj h
        subst hv
        rcases List.mem_cons.mp hmem with rfl | hm
        · omega
        · exact ih hs hm

/-- [GGV1] st of a face, for (ρ,σ) ∈ V_{>0}: the face term
    maximizing (1,−1), i.e. Supp(ℓ_{1,−1}(ℓ_{ρ,σ}(P))). -/
def stFace (ρ σ : Int) (terms : List Term) : Option Term :=
  stFaceAux (faceTerms ρ σ terms)

/-- [GGV1] en of a face, for (ρ,σ) ∈ V_{>0}: the face term
    maximizing (−1,1), i.e. Supp(ℓ_{−1,1}(ℓ_{ρ,σ}(P))). -/
def enFace (ρ σ : Int) (terms : List Term) : Option Term :=
  enFaceAux (faceTerms ρ σ terms)

/-- st lies in the face and maximizes (1,−1) over it. -/
theorem stFace_mem_max {ρ σ : Int} {terms : List Term} {s u : Term}
    (h : stFace ρ σ terms = some s) (hu : u ∈ faceTerms ρ σ terms) :
    s ∈ faceTerms ρ σ terms ∧
    dirVal 1 (-1) u.1.1 u.1.2 ≤ dirVal 1 (-1) s.1.1 s.1.2 :=
  ⟨stFaceAux_mem h, stFaceAux_max h hu⟩

/-- en lies in the face and maximizes (−1,1) over it. -/
theorem enFace_mem_max {ρ σ : Int} {terms : List Term} {s u : Term}
    (h : enFace ρ σ terms = some s) (hu : u ∈ faceTerms ρ σ terms) :
    s ∈ faceTerms ρ σ terms ∧
    dirVal (-1) 1 u.1.1 u.1.2 ≤ dirVal (-1) 1 s.1.1 s.1.2 :=
  ⟨enFaceAux_mem h, enFaceAux_max h hu⟩

/-- The cross product of [GGV1]: (ρ,σ) × (b − a). -/
def cross (ρ σ : Int) (a b : Int × Int) : Int :=
  ρ * (b.2 - a.2) - σ * (b.1 - a.1)

/-- Prop. 4.1 P polygon (Part 3 `prop41_P`), unit coefficients. -/
def shapePTerms : List Term :=
  [((0, 0), 1), ((1, 1), 1), ((6, 16), 1), ((6, 18), 1), ((0, 18), 1)]

/-- (3,−1) and (1,0) are in V_{>0}; (−1,1) is not (ρ+σ = 0). -/
example : isDirectionPos 3 (-1) :=
  ⟨by show Int.gcd 3 (-1) = 1; decide, by decide⟩
example : isDirectionPos 1 0 :=
  ⟨by show Int.gcd 1 0 = 1; decide, by decide⟩
example : ¬ isDirectionPos (-1) 1 :=
  fun h => (by decide : ¬ (0 : Int) < (-1) + 1) h.2

/-- [GGV1] st/en on the Prop. 4.1 faces, matching Part 8's pairs. -/
example : stFace 3 (-1) shapePTerms = some (((1, 1), 1)) := by decide
example : enFace 3 (-1) shapePTerms = some (((6, 16), 1)) := by decide
example : stFace 1 0 shapePTerms = some (((6, 16), 1)) := by decide
example : enFace 1 0 shapePTerms = some (((6, 18), 1)) := by decide

/-- The (−1,1)-face of prop41_P is a single term, so st = en there. -/
example : stFace (-1) 1 shapePTerms = some (((0, 18), 1)) := by decide
example : enFace (-1) 1 shapePTerms = some (((0, 18), 1)) := by decide

/-- [GGV1] Remark (starting and end with cross): for the non-monomial
    (3,−1)-face, (3,−1) × (en − st) > 0. -/
example : cross 3 (-1) (1, 1) (6, 16) = 50 := by decide
