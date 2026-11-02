/- Part 18 — D4 Part B, session 2: [GGV1] Proposition 8.2, instance layer.
    [GGV1] = arXiv:1401.1784. Bibliographic pin, checked against the
    TeX: GGHV's "Proposition 8.2" is the arXiv TeX's Proposition
    "esquina de 83" (corner of §8.3), item (2):

      If en_{ρ₂,σ₂}(P) ≁ en_{ρ₂,σ₂}(Q), then there exists k ∈ ℕ
      with (k+1)b < a and
        {en_{ρ₂,σ₂}(P), en_{ρ₂,σ₂}(Q)} = {(-k,0), (k+1,1)}.

    (Here (a,b) = (1/m)en_{ρ₁,σ₁}(P) = (1/n)en_{ρ₁,σ₁}(Q) from the
    proposition's hypotheses, and ∼ is proportionality of exponent
    pairs, i.e. vanishing cross product.)

    What is formalized here:
    - proportionality ∼ of integer exponent pairs, with refl/symm
      and the non-proportionality of the whole k-family
      {(-k,0), (k+1,1)} for k > 0 (so the conclusion's pair is
      always in the ≁ case, as the proposition requires);
    - the k = 1 instance used by GGHV Props. 4.1/4.3
      (D4_CITED_RESULTS): {en(Q), en(P)} = {(2,1), (−1,0)};
    - the statement of item (2) as a hypothesis bundle
      (`Prop82Instance`), in this project's convention: a cited
      theorem is carried as explicit hypotheses, never as an axiom.

    What is NOT formalized here: the proof of item (2) itself
    (via [GGV1] "le basico" proportionality and the regular-corner
    machinery), the (m,n)-pair setup, Succ/Dir, and the
    "k = 2 impossible (edges not parallel)" exclusion for the
    GGHV instance — that exclusion needs the parallel-edges
    argument and is recorded OPEN below. The instance's
    inequality (k+1)b < a is carried as a hypothesis field, not
    proved: the (a,b) values for the GGHV applications are part
    of the instance data, not reconstructed here.

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- Cross product of two exponent pairs (Part 17's `cross` at the
    origin, restated standalone). -/
def crossProd (a b : Int × Int) : Int := a.1 * b.2 - a.2 * b.1

/-- Proportionality of exponent pairs: vanishing cross product. -/
def prop (a b : Int × Int) : Prop := crossProd a b = 0

theorem prop_refl (a : Int × Int) : prop a a := by
  show crossProd a a = 0
  simp only [crossProd]
  rw [Int.mul_comm a.2 a.1]
  simp

theorem prop_symm {a b : Int × Int} (h : prop a b) : prop b a := by
  show crossProd b a = 0
  simp only [crossProd] at h ⊢
  rw [Int.mul_comm b.1 a.2, Int.mul_comm b.2 a.1]
  exact Int.sub_eq_zero.mpr (Int.sub_eq_zero.mp h).symm

/-- The k-family in Prop. 8.2(2) is never proportional, for k > 0. -/
theorem kfamily_not_prop {k : Int} (hk : 0 < k) :
    ¬ prop (-k, 0) (k + 1, 1) := by
  show crossProd (-k, 0) (k + 1, 1) ≠ 0
  simp only [crossProd]
  omega

/-- The k = 1 pair, by computation. -/
example : ¬ prop (-1, 0) (2, 1) := by
  show crossProd (-1, 0) (2, 1) ≠ 0
  decide

example : crossProd (-1, 0) (2, 1) = -1 := by decide

/-- Prop. 8.2(2) as a hypothesis bundle: the instance data plus the
    conclusion, with the (m,n)-pair setup and the proof left as the
    surrounding theory (sessions 3–4 and the [GGV1] corner theory).
    `hk1` is the proposition's inequality (k+1)b < a, carried, not
    proved. -/
structure Prop82Instance where
  k : Int
  hk : 0 < k
  a : Int
  b : Int
  hb : 0 < b
  hba : b < a
  hk1 : (k + 1) * b < a
  enP : Int × Int
  enQ : Int × Int
  hpair : (enP = (-k, 0) ∧ enQ = (k + 1, 1)) ∨
          (enP = (k + 1, 1) ∧ enQ = (-k, 0))

/-- From the bundle, the two en points are never proportional. -/
theorem prop82_not_prop (I : Prop82Instance) : ¬ prop I.enP I.enQ := by
  rcases I.hpair with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · rw [hP, hQ]
    exact kfamily_not_prop I.hk
  · rw [hP, hQ]
    intro h
    exact kfamily_not_prop I.hk (prop_symm h)

/-- The k = 1 specialization is exactly the GGHV Props. 4.1/4.3
    instance: {en(Q), en(P)} = {(2,1), (−1,0)}. -/
theorem prop82_k1 (I : Prop82Instance) (hk1 : I.k = 1) :
    (I.enP = (-1, 0) ∧ I.enQ = (2, 1)) ∨
    (I.enP = (2, 1) ∧ I.enQ = (-1, 0)) := by
  rcases I.hpair with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · left
    rw [hk1] at hP hQ
    exact ⟨by simpa using hP, by simpa using hQ⟩
  · right
    rw [hk1] at hP hQ
    exact ⟨by simpa using hP, by simpa using hQ⟩

/-- OPEN (not proved here): the k = 2 exclusion for the GGHV
    instance. k = 2 would give the pair {(-2,0), (3,1)}; GGHV
    excludes it because the P- and Q-edges are not parallel.
    That parallel-edges argument belongs to the [GGV1] corner
    theory (sessions 3–4), not to this instance layer. -/
example : ¬ prop (-2, 0) (3, 1) := by
  show crossProd (-2, 0) (3, 1) ≠ 0
  decide
