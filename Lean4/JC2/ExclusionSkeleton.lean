/-
  JC2 / Exclusion — skeleton ONLY (MAP, 2026-10-29).
  Nothing in this file is proved. `INTERFACE` axioms name exactly the
  paper inputs that Phase 1 assumes and Phase 2 must discharge.
  Do not present this file, or anything built from it, as a proof.
-/

/-- A Keller pair over an algebraically closed field of char 0:
    two polynomials with nonzero constant Jacobian bracket. -/
structure KellerPair (K : Type) [Field K] where
  P : K[X] -- placeholder: two-variable polynomials, to be fixed at setup
  Q : K[X]

/-- INTERFACE (GGHV Prop. 4.3, case (8,28)): a (72,108) counterexample
    yields Laurent polynomials with bracket x^2 in Case 1 or Case 2,
    with the vertex lists of FORMALIZATION_MAP.md §3.1. -/
axiom gghv_prop_43_interface : True

/-- INTERFACE (Helali §5, Case 2): the transcribed Case 2 system
    has no solution. To be discharged by Case2.lean: data + expansion
    check of 1 = Σ TᵢRᵢ, NOT by this axiom. -/
axiom case2_no_solution_interface : True

/-- INTERFACE (Helali §5, Case 1): the transcribed Case 1 system
    has no solution. To be discharged by Case1Branching / Case1HZero /
    HardCertificate / Symmetry: s = ±c split, h = 0 unit certificates,
    hard identity h = Σ TᵢEᵢ, involution transport. -/
axiom case1_no_solution_interface : True

/-- Helali's theorem, conditional form: the two transcribed systems
    have no solutions. This is the only "theorem" this skeleton states,
    and it rests on the two INTERFACE axioms above. -/
theorem transcribed_systems_empty :
    case2_no_solution_interface ∧ case1_no_solution_interface :=
  ⟨case2_no_solution_interface, case1_no_solution_interface⟩

/-- Helali's corollary, with its condition kept in the statement:
    IF Prop. 4.3 is exhaustive AND the transcription is faithful,
    THEN (72,108) is impossible and every hypothetical plane
    counterexample has max degree ≥ 125. -/
theorem conditional_degree_bound
    (h_reduction : gghv_prop_43_interface)
    (h_transcription : True) : True :=
  trivial
