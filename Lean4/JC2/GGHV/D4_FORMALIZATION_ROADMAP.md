# D4 — Formalization roadmap (2026-10-30)

Status: **OPEN.** This is the work plan for formalizing
the cited [GGV*] results, in dependency order. Nothing
in it is claimed proved. The order matters: later items
depend on earlier ones, so starting at the end (the
[GGV5] enumeration, or Thm 7.3) without the direction
theory underneath would be building on air.

## Dependency order

1. **Direction / ℓ theory (gateway, D1).** Define
   (ρ,σ)-homogeneous parts ℓ_{ρ,σ} and the face
   definition of en/st (the Part 9 negative result shows
   valuation extremum alone does not give en/st — the
   ordering tied to ℓ is essential), Pred/Succ, and
   maximal segments for general polygons. This unlocks
   items 2–4. DONE at the support level: Part 13
   (2026-10-30) proves face lists with membership,
   subset, maximality, and nonemptiness lemmas. The
   remaining part of item 1 is the polynomial ℓ
   (coefficients), which is the next run's target.
2. **[GGV1] direction/edge theory.** Prop. 8.2 (k = 1
   gives (en(Q), en(P)) = ((2,1), (−1,0)); k = 2
   impossible), Cor. 7.4 (the (ρ₀,σ₀) instances),
   Thm 7.6(5) (q₁ = 4), Prop. 2.11(3), Cor. 7.2,
   Def. 4.3, Props. 1.13/2.1. These are the instances
   Part 3/Part 5 actually use.
3. **[GGV2] corner theory.** Prop. 3.29 (§3-120
   last-corner argument), Prop. 3.12 (Prop. 4.2
   algorithm setting), Def. 3.21, Remark 3.31. Needs
   item 1 plus Newton-polygon corner machinery; the
   Prop. 4.2 algorithm must be formalized as a
   verified computation, not transcribed.
4. **[GGV6] root theory.** Thm 7.3 (I_M ≥ I_m),
   Props. 6.4/6.6, Ex. 6.7 (π-roots, major/minor
   roots, δ-values). Needs items 1–2; this is the
   theory behind Part 2's `discard_84` hypothesis.
5. **[GGV5] enumeration.** The §2 premise (every
   counterexample below degree 125 lies in one of the
   10 table rows, [GGV5] §§5–6). Largest single item;
   last, because it is an enumeration over the whole
   classification, not a lemma of the other items.
6. **Assembly premise replacement.** Only when items
   1–5 are proved theorems (or the needed instances
   are) can Part 5's `AssemblyPremises` fields be
   replaced by proofs, one field at a time, with
   `lake build` re-run after each replacement. No
   field has been replaced to date.

## What is already done (and is not this)

The kernel-checked arithmetic in Parts 1–6/8/9
(gcd, scalings, degree bounds, direction valuations,
I_M = 4 / I_m = 5 as numbers, max-attainment for
(3,−1)/(1,0)) is arithmetic about the *inputs* to
the cited theorems. It does not discharge any item
above, and must not be cited as doing so.

## Honest scale

Items 1–4 are each a paper-section formalization;
item 5 is a programme in itself. D4 does not close
in a single run. Item 1 at the support level is done
(Part 13, 2026-10-30: face lists). The next run should
take the polynomial ℓ level, and report exactly which
definitions and lemmas it proves.
