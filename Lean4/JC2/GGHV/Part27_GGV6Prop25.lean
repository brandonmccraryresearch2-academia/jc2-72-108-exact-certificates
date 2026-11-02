/- Part 27 — D4 Part D, session 3: [GGV6] Prop. 2.5, instance
    layer. Part D is COMPLETE after this session.

    Instance (GGHV, Prop. 4.3 argument): in the setting where
    (ρ,σ) = Pred_P(−1,4) ∈ ](0,−1),(1,−1)], ℓ_{ρ,σ}(P) =
    λR^{qm} = λR^{4m} with v_{ρ,σ}(R) > 0, en_{ρ,σ}(R) =
    (7,2), and [R,G] = R^i for some i, Prop. 2.5 gives
    Pred_P(1,0) ∈ {(1,−2), (1,−3)}.

    Status, stated plainly: Prop. 2.5's TeX analogue was NOT
    located in arXiv:1708.09367 (its §2 propositions are
    "jacobiano se anula", "direcciones positivas", "b igual a
    2", none of which states a Pred(1,0) bound). The instance
    is therefore formalized as cited — a hypothesis bundle
    carrying the setting and the conclusion — not as a checked
    statement. The arithmetic that IS checked: qm = 4m with
    m > 0 gives q = 4; the two Pred candidates are distinct;
    and this Prop. 4.3 Pred set {(1,−2),(1,−3)} is a different
    setting from Part 23's Prop. 4.2 Pred set {(1,−2),(2,−5)}
    — the two must not be conflated (they share only (1,−2)).

    Core Lean only, standalone. No sorry and no forbidden
    declarations. -/

/-- Prop. 2.5's setting and conclusion, as a carried bundle. -/
structure Prop25Instance where
  q : Nat
  m : Nat
  hm : 0 < m
  hqm : q * m = 4 * m
  enR : Int × Int
  henR : enR = (7, 2)
  pred10 : Int × Int
  hpred : pred10 = (1, -2) ∨ pred10 = (1, -3)

/-- qm = 4m with m > 0 gives q = 4. -/
theorem prop25_q (q m : Nat) (hm : 0 < m) (h : q * m = 4 * m) :
    q = 4 :=
  Nat.eq_of_mul_eq_mul_right hm h

/-- The two Pred candidates are distinct. -/
example : (1, -2) ≠ (1, -3) := by decide

/-- The Prop. 4.3 Pred set and the Prop. 4.2 Pred set share
    exactly (1,−2) (filtering the first list by membership in
    the second). -/
example : ([(1, -2), (1, -3)] : List (Int × Int)).filter
    (fun p => (p == (1, -2)) || (p == (2, -5))) = [(1, -2)] := by decide
