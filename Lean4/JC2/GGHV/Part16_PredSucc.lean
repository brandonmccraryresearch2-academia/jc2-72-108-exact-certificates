/- Part 16 — D4 Part A, session 3: Pred/Succ and general maximal segments.
    D4 roadmap item 1, polynomial level, third step.

    Part 14 gave coefficient-carrying face terms and Part 15 gave face
    endpoints. This file adds the neighbours of a face in traversal
    order: Pred and Succ for a general term list, plus the segment
    predecessor/successor of a face.

    Definitions, stated plainly so they cannot be misread as the
    paper's Pred/Succ: `predIn t terms` is the term immediately
    before the FIRST occurrence of `t` in list order (none when `t`
    is first or absent); `succIn t terms` is the term immediately
    after the FIRST occurrence of `t` (none when `t` is last or
    absent). For a face, the segment predecessor is `predIn` of its
    first endpoint, and the segment successor is `predIn` of its last
    endpoint in the REVERSED list — i.e. the term after the LAST
    occurrence of the last endpoint, which is the correct neighbour
    when the last endpoint value occurs more than once.

    What is proved, for arbitrary term lists (not only the §5 shapes):
    - membership and first-occurrence decompositions for Pred/Succ;
    - Pred/Succ are inverses in decomposition form;
    - the segment-predecessor theorem: if the segment predecessor
      of a face is itself a face term, it equals the first endpoint
      (so a genuine predecessor, distinct from the endpoint, lies
      outside the face);
    - the segment-successor theorem, by the same argument applied to
      the reversed list: if the segment successor is a face term, it
      equals the last endpoint.

    Scope, stated plainly: this is NOT the paper's en/st definition,
    and Pred/Succ here are list-order neighbours in the traversal
    order as given, not polygon adjacency from the [GGV*] face
    definition tied to ℓ, whose primary text ([GGV1]) is Part B work.
    The polynomial ℓ_{ρ,σ} itself, and the face definition of en/st
    from ℓ, remain open. No grade moves.

    Core Lean only, standalone. `dirVal` / `maxVertDir` / `maxVert_mem` /
    `maxVert_none` / `maxVert_max` / `termExps` / `faceTerms` /
    `faceTerms_mem` / `faceEndpoints` are restated verbatim from
    Parts 13–15, following this project's standalone-file convention.
    No sorry and no forbidden declarations. -/

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

/-- The face, as a filter, once a maximal vertex is fixed. -/
theorem faceTerms_filter {ρ σ : Int} {terms : List Term} {m : Int × Int} :
    maxVertDir ρ σ (termExps terms) = some m →
    faceTerms ρ σ terms =
      terms.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2) := by
  intro h
  simp only [faceTerms, h]

/-- The endpoints of a face: first and last face terms in list order
    (from Part 15). -/
def faceEndpoints (ρ σ : Int) (terms : List Term) : Option (Term × Term) :=
  match faceTerms ρ σ terms with
  | [] => none
  | t :: ts => some (t, List.getLast (t :: ts) (by simp))

/-- If endpoints exist, the face list starts with the first endpoint. -/
theorem faceEndpoints_head {ρ σ : Int} {terms : List Term} {a b : Term} :
    faceEndpoints ρ σ terms = some (a, b) →
    ∃ ts, faceTerms ρ σ terms = a :: ts := by
  intro h
  cases hf : faceTerms ρ σ terms with
  | nil => simp [faceEndpoints, hf] at h
  | cons t ts =>
    simp only [faceEndpoints, hf] at h
    have hpair : (t, List.getLast (t :: ts) (by simp)) = (a, b) :=
      Option.some.inj h
    obtain ⟨ha, -⟩ := Prod.mk.inj hpair
    exact ⟨ts, by rw [ha]⟩

/-- If endpoints exist, the last endpoint is the last face term. -/
theorem faceEndpoints_getLast {ρ σ : Int} {terms : List Term} {a b : Term} :
    faceEndpoints ρ σ terms = some (a, b) →
    (faceTerms ρ σ terms).getLast? = some b := by
  intro h
  cases hf : faceTerms ρ σ terms with
  | nil => simp [faceEndpoints, hf] at h
  | cons t ts =>
    simp only [faceEndpoints, hf] at h
    have hpair : (t, List.getLast (t :: ts) (by simp)) = (a, b) :=
      Option.some.inj h
    obtain ⟨-, hb⟩ := Prod.mk.inj hpair
    have hgl : (t :: ts).getLast? = some ((t :: ts).getLast (by simp)) :=
      List.getLast?_eq_some_getLast (by simp)
    rw [hgl, hb]

/-- Predecessor auxiliary: `prev` is the element before the current
    position, or `none` at the head of the list. -/
def predAux (prev : Option Term) (t : Term) : List Term → Option Term
  | [] => none
  | x :: xs => if x = t then prev else predAux (some x) t xs

/-- Predecessor of the first occurrence of `t` in list order. -/
def predIn (t : Term) (terms : List Term) : Option Term := predAux none t terms

/-- Successor of the first occurrence of `t` in list order. -/
def succIn (t : Term) : List Term → Option Term
  | [] => none
  | x :: xs => if x = t then xs.head? else succIn t xs

/-- First-occurrence decomposition for the predecessor auxiliary: either
    the predecessor sits immediately before the first occurrence of `t`
    (and `t` does not occur in the prefix before it), or `t` is the head
    and the auxiliary's incoming `prev` is the result. -/
theorem predAux_cases {prev : Option Term} {t : Term} {terms : List Term} {p : Term} :
    predAux prev t terms = some p →
    (∃ l r, terms = l ++ p :: t :: r ∧ t ∉ l) ∨
    (prev = some p ∧ ∃ r, terms = t :: r) := by
  induction terms generalizing prev with
  | nil => intro h; simp [predAux] at h
  | cons x xs ih =>
    intro h
    simp only [predAux] at h
    by_cases hx : x = t
    · right
      refine ⟨by simpa [hx] using h, xs, by rw [hx]⟩
    · have h2 : predAux (some x) t xs = some p := by simpa [hx] using h
      rcases ih h2 with ⟨l, r, hxs, hnot⟩ | ⟨hprev, r, hxs⟩
      · left
        refine ⟨x :: l, r, by simp [hxs], ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun hxt => hx hxt.symm, hnot⟩
      · left
        have hxp : x = p := Option.some.inj hprev
        refine ⟨[], r, by simp [← hxp, hxs], by simp⟩

/-- First-occurrence decomposition for the predecessor. -/
theorem predIn_cases {t : Term} {terms : List Term} {p : Term} :
    predIn t terms = some p →
    ∃ l r, terms = l ++ p :: t :: r ∧ t ∉ l := by
  intro h
  rcases predAux_cases (prev := none) h with hleft | hright
  · exact hleft
  · obtain ⟨hprev, -⟩ := hright
    simp at hprev

/-- First-occurrence decomposition for the successor. -/
theorem succIn_cases {t : Term} {terms : List Term} {s : Term} :
    succIn t terms = some s →
    ∃ l r, terms = l ++ t :: s :: r ∧ t ∉ l := by
  induction terms with
  | nil => intro h; simp [succIn] at h
  | cons x xs ih =>
    intro h
    simp only [succIn] at h
    by_cases hx : x = t
    · subst hx
      have h2 : xs.head? = some s := by simpa using h
      cases xs with
      | nil => simp at h2
      | cons y ys =>
        have hs : y = s := Option.some.inj h2
        subst hs
        exact ⟨[], ys, by simp, by simp⟩
    · have h2 : succIn t xs = some s := by simpa [hx] using h
      obtain ⟨l, r, hxs, hnot⟩ := ih h2
      refine ⟨x :: l, r, by simp [hxs], ?_⟩
      simp only [List.mem_cons, not_or]
      exact ⟨fun hxt => hx hxt.symm, hnot⟩

/-- A predecessor lies in the list. -/
theorem predIn_mem {t : Term} {terms : List Term} {p : Term} :
    predIn t terms = some p → p ∈ terms := by
  intro h
  obtain ⟨l, r, hterms, -⟩ := predIn_cases h
  rw [hterms]
  simp

/-- A successor lies in the list. -/
theorem succIn_mem {t : Term} {terms : List Term} {s : Term} :
    succIn t terms = some s → s ∈ terms := by
  intro h
  obtain ⟨l, r, hterms, -⟩ := succIn_cases h
  rw [hterms]
  simp

/-- Predecessor from a decomposition: if `p` sits immediately before
    `t`, and `t` does not occur in the prefix, then `predIn t` is `p`. -/
theorem pred_of_decomp {prev : Option Term} {l : List Term} {p t : Term} {r : List Term} :
    p ≠ t → t ∉ l → predAux prev t (l ++ p :: t :: r) = some p := by
  induction l generalizing prev with
  | nil =>
    intro hpt _
    simp [predAux, hpt]
  | cons x xs ih =>
    intro hpt hnot
    have hx : x ≠ t := by
      intro hxt
      exact hnot (by simp [hxt])
    have hnot' : t ∉ xs := by
      intro hmem
      exact hnot (by simp [hmem])
    simp only [List.cons_append] at *
    simp [predAux, hx, ih hpt hnot']

/-- Successor from a decomposition: if `t` sits immediately before `s`,
    and `t` does not occur in the prefix, then `succIn t` is `s`. -/
theorem succ_of_decomp {l : List Term} {t s : Term} {r : List Term} :
    t ∉ l → succIn t (l ++ t :: s :: r) = some s := by
  induction l with
  | nil => intro _; simp [succIn]
  | cons x xs ih =>
    intro hnot
    have hx : x ≠ t := by
      intro hxt
      exact hnot (by simp [hxt])
    have hnot' : t ∉ xs := by
      intro hmem
      exact hnot (by simp [hmem])
    simp only [List.cons_append] at *
    simp [succIn, hx, ih hnot']

/-- Pred and Succ are inverses in decomposition form: in a decomposition
    `l ++ t :: s :: r` with neither endpoint in the prefix and the
    endpoints distinct, Pred of `s` is `t` and Succ of `t` is `s`. -/
theorem pred_succ_inverse {l : List Term} {t s : Term} {r : List Term} :
    t ∉ l → s ∉ l → t ≠ s →
    predIn s (l ++ t :: s :: r) = some t ∧ succIn t (l ++ t :: s :: r) = some s := by
  intro htl hsl hts
  constructor
  · exact pred_of_decomp hts hsl
  · exact succ_of_decomp htl

/-- The segment-predecessor theorem, in head form: if the face list
    starts with `a`, the predecessor of `a` is a face term only when it
    equals `a` — so a genuine predecessor, distinct from `a`, lies
    outside the face. -/
theorem predNeighbourHead {ρ σ : Int} {terms : List Term} {a : Term} {ts : List Term}
    {p : Term} :
    faceTerms ρ σ terms = a :: ts → predIn a terms = some p →
    p ∈ faceTerms ρ σ terms → p = a := by
  intro hface hpred hpface
  obtain ⟨l, r, hterms, hnot⟩ := predIn_cases hpred
  cases hm : maxVertDir ρ σ (termExps terms) with
  | none =>
    have : faceTerms ρ σ terms = [] := by simp [faceTerms, hm]
    rw [hface] at this
    simp at this
  | some m =>
    have hfilter : faceTerms ρ σ terms =
        terms.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2) :=
      faceTerms_filter hm
    have hp : dirVal ρ σ p.1.1 p.1.2 = dirVal ρ σ m.1 m.2 := by
      rw [hfilter] at hpface
      have := (List.mem_filter.mp hpface).2
      exact of_decide_eq_true this
    have hface2 : faceTerms ρ σ terms =
        (l.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2)) ++
          p :: ((a :: r).filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2)) := by
      rw [hfilter, hterms, List.filter_append]
      simp [hp]
    rw [hface] at hface2
    cases hf : (l.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2)) with
    | nil =>
      simp only [hf, List.nil_append] at hface2
      exact (List.cons.inj hface2).1.symm
    | cons x xs =>
      have hxmem : x ∈ l.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2) := by
        simp [hf]
      have hxterms : x ∈ l := (List.mem_filter.mp hxmem).1
      have hax : a = x := by
        have hcons : a :: ts = x :: (xs ++ p :: ((a :: r).filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2))) := by
          rw [hface2, hf, List.cons_append]
        exact (List.cons.inj hcons).1
      subst hax
      exact absurd hxterms hnot

/-- Segment predecessor: the predecessor of the first endpoint. -/
def segPred (ρ σ : Int) (terms : List Term) : Option Term :=
  match faceEndpoints ρ σ terms with
  | some (a, _) => predIn a terms
  | none => none

/-- Segment successor: the predecessor of the last endpoint in the
    reversed list, i.e. the term after the last occurrence of the
    last endpoint in the original list. -/
def segSucc (ρ σ : Int) (terms : List Term) : Option Term :=
  match faceEndpoints ρ σ terms with
  | some (_, b) => predIn b terms.reverse
  | none => none

/-- The segment-predecessor theorem: a segment predecessor that is
    itself a face term equals the first endpoint. -/
theorem segPred_neighbour {ρ σ : Int} {terms : List Term} {a b p : Term} :
    faceEndpoints ρ σ terms = some (a, b) → segPred ρ σ terms = some p →
    p ∈ faceTerms ρ σ terms → p = a := by
  intro hend hseg hp
  obtain ⟨ts, hface⟩ := faceEndpoints_head hend
  have hpred : predIn a terms = some p := by simpa [segPred, hend] using hseg
  exact predNeighbourHead hface hpred hp

/-- Face terms of the reversed list are the reversed face terms. The
    maximal valuation value is the same in both orders, even though
    `maxVertDir`'s last-max tie-break may pick a different vertex. -/
theorem faceTerms_reverse {ρ σ : Int} {terms : List Term} :
    faceTerms ρ σ terms.reverse = (faceTerms ρ σ terms).reverse := by
  cases hm : maxVertDir ρ σ (termExps terms) with
  | none =>
    have hterms : termExps terms = [] := maxVert_none hm
    have hterms' : terms = [] := by
      cases terms with
      | nil => rfl
      | cons x xs => simp [termExps] at hterms
    subst hterms'
    simp [faceTerms, termExps, maxVertDir]
  | some m =>
    cases hm' : maxVertDir ρ σ (termExps terms.reverse) with
    | none =>
      have hnil : termExps terms.reverse = [] := maxVert_none hm'
      have h1 : termExps terms.reverse = (termExps terms).reverse := by
        simp [termExps, List.map_reverse]
      rw [h1] at hnil
      have h2 : termExps terms = [] := by simpa using hnil
      rw [h2] at hm
      simp [maxVertDir] at hm
    | some m' =>
      have hmaxeq : dirVal ρ σ m.1 m.2 = dirVal ρ σ m'.1 m'.2 := by
        have hm_mem : m ∈ termExps terms := maxVert_mem hm
        have hm'_mem : m' ∈ termExps terms.reverse := maxVert_mem hm'
        have hm'_in : m' ∈ termExps terms := by
          have h1 : termExps terms.reverse = (termExps terms).reverse := by
            simp [termExps, List.map_reverse]
          rw [h1] at hm'_mem
          exact List.mem_reverse.mp hm'_mem
        have hm_in_rev : m ∈ termExps terms.reverse := by
          have h1 : termExps terms.reverse = (termExps terms).reverse := by
            simp [termExps, List.map_reverse]
          rw [h1]
          exact List.mem_reverse.mpr hm_mem
        have h1 := maxVert_max hm hm'_in
        have h2 := maxVert_max hm' hm_in_rev
        exact Int.le_antisymm h2 h1
      rw [faceTerms_filter hm', faceTerms_filter hm, List.filter_reverse]
      have hfilter_eq : (terms.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m'.1 m'.2)) =
          terms.filter (fun t => dirVal ρ σ t.1.1 t.1.2 = dirVal ρ σ m.1 m.2) := by
        rw [hmaxeq]
      rw [hfilter_eq]

/-- The segment-successor theorem: a segment successor that is itself
    a face term equals the last endpoint. Proved by the predecessor
    theorem applied to the reversed list, whose first face term is the
    original last endpoint. -/
theorem segSucc_neighbour {ρ σ : Int} {terms : List Term} {a b s : Term} :
    faceEndpoints ρ σ terms = some (a, b) → segSucc ρ σ terms = some s →
    s ∈ faceTerms ρ σ terms → s = b := by
  intro hend hseg hs
  have hlast : (faceTerms ρ σ terms).getLast? = some b := faceEndpoints_getLast hend
  have hpred_rev : predIn b terms.reverse = some s := by
    simpa [segSucc, hend] using hseg
  have hs_rev : s ∈ faceTerms ρ σ terms.reverse := by
    rw [faceTerms_reverse, List.mem_reverse]
    exact hs
  have hhead : (faceTerms ρ σ terms.reverse).head? = some b := by
    rw [faceTerms_reverse, List.head?_reverse]
    exact hlast
  obtain ⟨ts', hface_rev⟩ := List.head?_eq_some_iff.mp hhead
  exact predNeighbourHead hface_rev hpred_rev hs_rev

/-- §5 P-shape with unit coefficients (placeholders, as in Part 14). -/
def shapePTerms : List Term :=
  [((0, 0), 1), ((1, 1), 1), ((6, 16), 1), ((6, 18), 1), ((0, 18), 1)]

/-- §5 Q-shape with unit coefficients (placeholders, as in Part 14). -/
def shapeQTerms : List Term :=
  [((0, 0), 1), ((1, 0), 1), ((9, 24), 1), ((9, 27), 1), ((0, 27), 1)]

/-- Pred/Succ on the §5 P-shape, computed exactly. -/
example : predIn ((1, 1), 1) shapePTerms = some ((0, 0), 1) := by decide
example : succIn ((1, 1), 1) shapePTerms = some ((6, 16), 1) := by decide
example : predIn ((0, 0), 1) shapePTerms = none := by decide
example : succIn ((0, 18), 1) shapePTerms = none := by decide

/-- Segment neighbours of the §5 (3,−1)-face: both outside the face. -/
example : faceEndpoints 3 (-1) shapePTerms =
    some ((((1, 1), 1), ((6, 16), 1))) := by decide
example : segPred 3 (-1) shapePTerms = some ((0, 0), 1) := by decide
example : segSucc 3 (-1) shapePTerms = some ((6, 18), 1) := by decide
example : ((0, 0), 1) ∉ faceTerms 3 (-1) shapePTerms := by decide
example : ((6, 18), 1) ∉ faceTerms 3 (-1) shapePTerms := by decide

/-- Segment neighbours of the §5 (1,0)-face. -/
example : faceEndpoints 1 0 shapePTerms =
    some ((((6, 16), 1), ((6, 18), 1))) := by decide
example : segPred 1 0 shapePTerms = some ((1, 1), 1) := by decide
example : segSucc 1 0 shapePTerms = some ((0, 18), 1) := by decide

/-- The (−1,1) negative case, carried through Pred/Succ: the face is a
    single vertex, its predecessor is (6,18), and it has no successor
    because it is the last term of the list. -/
example : faceEndpoints (-1) 1 shapePTerms =
    some ((((0, 18), 1), ((0, 18), 1))) := by decide
example : segPred (-1) 1 shapePTerms = some ((6, 18), 1) := by decide
example : segSucc (-1) 1 shapePTerms = none := by decide

/-- A general maximal segment beyond the §5 shapes: under (0,1) the
    face of [(0,0),(1,2),(2,2),(3,0)] is [(1,2),(2,2)], with segment
    neighbours (0,0) and (3,0), both outside the face. -/
def shapeGenTerms : List Term :=
  [((0, 0), 1), ((1, 2), 1), ((2, 2), 1), ((3, 0), 1)]

example : faceTerms 0 1 shapeGenTerms = [((1, 2), 1), ((2, 2), 1)] := by decide
example : faceEndpoints 0 1 shapeGenTerms =
    some ((((1, 2), 1), ((2, 2), 1))) := by decide
example : segPred 0 1 shapeGenTerms = some ((0, 0), 1) := by decide
example : segSucc 0 1 shapeGenTerms = some ((3, 0), 1) := by decide
example : ((0, 0), 1) ∉ faceTerms 0 1 shapeGenTerms := by decide
example : ((3, 0), 1) ∉ faceTerms 0 1 shapeGenTerms := by decide
