"""GGHV §6 elimination check (independent SymPy re-derivation, I1).

Paper: arXiv:2204.14178v1, §6, align block before
`ecuacion principal para 7`. The paper says: "using a CAS
(for example Mathematica) we eliminate the variables
d_{-10}, d_{-8}, d_{-7}, d_{-6}, d_{-5}, d_{-4}, d_{-3},
d_{-2}", obtaining
    9 y^9 d_1 (d_{-1})^6 + y^{27} + 27 d_0 (d_{-1})^9 = 0.
System used here (9 equations, excluding (D~^2)_{-8},
(D~^2)_{-6} and (D~^3)_{-3}, exactly as the paper states):
  D2_1..D2_5, D2_7, Q1, Q2, Q4, with F_{-4} = (1/2) y^{-1}
  so the F term in Q4 is F_{-4} y^{10} = y^9 / 2.
Transcription note: the TeX line for (D~^2)_{-7} reads
"2 d_{-1}0 + ..." — read as 2 d_{-10}, confirmed by the
coefficient pattern: (D~^2)_{-7} pairs (3,-10),(1,-8),
(0,-7),(-1,-6),(-2,-5),(-3,-4), and the (D~^2)_{-8} line
starts with the correctly-braced 2 d_{-11} for pair (3,-11).
Method: sequential linear elimination (each eliminated
variable first occurs linearly with constant coefficient
in one equation), then elimination of d_{-2} between the
two remaining equations (Q2 and Q4) by resultant, then
factoring. This is an independent CAS check (I1), NOT a
Lean kernel proof: it verifies the paper's elimination
claim, it does not formalize it.
"""
import sympy as sp

d0, d1, m1, m2, m3, m4, m5, m6, m7, m8, m10, y = sp.symbols(
    "d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 y")

# (D~^2) equations
D2_1 = 2*d0*m1 + 2*d1*m2 + 2*m4
D2_2 = m1**2 + 2*d0*m2 + 2*d1*m3 + 2*m5
D2_3 = 2*m1*m2 + 2*d0*m3 + 2*d1*m4 + 2*m6
D2_4 = m2**2 + 2*m1*m3 + 2*d0*m4 + 2*d1*m5 + 2*m7
D2_5 = 2*m2*m3 + 2*m1*m4 + 2*d0*m5 + 2*d1*m6 + 2*m8
D2_7 = 2*m10 + 2*m3*m4 + 2*m2*m5 + 2*m1*m6 + 2*d0*m7 + 2*d1*m8
# (D~^3 + ...) equations, j = 1, 2, 4 (j = 3 excluded)
Q1 = (3*d0**2*m1 + 3*d1*m1**2 + 6*d0*d1*m2 + 3*m2**2 + 3*d1**2*m3
      + 6*m1*m3 + 6*d0*m4 + 6*d1*m5 + 3*m7)
Q2 = (3*d0*m1**2 + 3*d0**2*m2 + 6*d1*m1*m2 + 6*d0*d1*m3 + 6*m2*m3
      + 3*d1**2*m4 + 6*m1*m4 + 6*d0*m5 + 6*d1*m6 + 3*m8)
Q4 = (3*m10 + 3*m1**2*m2 + 3*d0*m2**2 + 6*d0*m1*m3 + 6*d1*m2*m3
      + 3*d0**2*m4 + 6*d1*m1*m4 + 6*m3*m4 + 6*d0*d1*m5 + 6*m2*m5
      + 3*d1**2*m6 + 6*m1*m6 + 6*d0*m7 + 6*d1*m8 + sp.Rational(1, 2)*y**9)

subs = {}
def solve_linear(eq, var, name):
    sol = sp.solve(eq.subs(subs), var, dict=True)
    assert len(sol) == 1, (name, sol)
    subs[var] = sp.expand(sol[0][var])
    print(f"{name}: {var} = {subs[var]}")

solve_linear(D2_1, m4, "D2_1 -> dm4")
solve_linear(D2_2, m5, "D2_2 -> dm5")
solve_linear(D2_3, m6, "D2_3 -> dm6")
solve_linear(D2_4, m7, "D2_4 -> dm7")
solve_linear(D2_5, m8, "D2_5 -> dm8")
# Q1 is linear in dm3 after the above substitutions
solve_linear(Q1, m3, "Q1 -> dm3")
solve_linear(D2_7, m10, "D2_7 -> dm10")

def full_subs(expr):
    for _ in range(12):
        new = expr.subs(subs)
        if new == expr:
            break
        expr = new
    return sp.expand(expr)

Q2r = full_subs(Q2)
Q4r = full_subs(Q4)
print("\nQ2 after substitutions (in dm2, dm1, d0, d1):")
print(sp.factor(Q2r))
print("\nQ4 after substitutions (in dm2, dm1, d0, d1, y):")
print(sp.factor(Q4r))

# Eliminate dm2 between Q2r and Q4r
res = sp.resultant(Q2r, Q4r, m2)
res = sp.factor(res)
print("\nResultant w.r.t. dm2, factored:")
print(res)
target = 9*y**9*d1*m1**6 + y**27 + 27*d0*m1**9
print("\nTarget principal equation:")
print(target)
print("\nResultant / target (should be a single factor, expanded):")
q, r = sp.div(sp.expand(res), sp.expand(target))
print("quotient:", sp.factor(q))
print("remainder:", r)
assert r == 0, "resultant is not divisible by the target"
print("\nCHECK PASSED: resultant is divisible by the paper's principal equation.")
print("Remaining quotient factor:", sp.factor(q))
