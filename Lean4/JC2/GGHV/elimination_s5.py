"""GGHV §5 elimination check (independent SymPy re-derivation, I1).

Paper: arXiv:2204.14178v1, §5, align block before
`ecuacion principal`. The paper says: "We consider this
as a system of 9 equations and using a CAS (for example
Mathematica) we eliminate the variables d_{-10}, d_{-8},
d_{-7}, d_{-6}, d_{-5}, d_{-4}, d_{-3}, d_{-2}",
obtaining
    18 C_3^{23} d_1 (d_{-1})^6 F_{-4}
      + 8 C_3^{69} F_{-4}^3 + 27 d_0 (d_{-1})^9 = 0.
System used here (9 equations, excluding (D~^2)_{-8},
(D~^2)_{-6} and (D~^3)_{-3}, exactly as the paper states):
  D2_1..D2_5, D2_7, Q1, Q2, Q4, where Q4's final term is
  F_{-4} C_3^{23} (in §6 the corresponding term is
  F_{-4} y^{10} = y^9/2; the rest of the system is
  identical, which is why the resultant factor below
  matches the §6 check exactly).
Transcription note: the TeX line for (D~^2)_{-7} reads
"2 d_{-1}0 + ..." — read as 2 d_{-10}, as in the §6
script (coefficient pattern + correctly-braced 2 d_{-11}
in the (D~^2)_{-8} line, which is excluded here).
Method: sequential linear elimination, then elimination
of d_{-2} between the two remaining equations (Q2 and
Q4) by resultant, then factoring. This is an
independent CAS check (I1), NOT a Lean kernel proof:
it verifies the paper's elimination claim, it does not
formalize it. Note on the check itself: SymPy's
polynomial `div` does not handle the dm1^{-3} factor in
the resultant, so divisibility is checked by expanding
resultant - factor x target and confirming it is 0,
and by simplifying resultant/target to the factor.
"""
import sympy as sp

d0, d1, m1, m2, m3, m4, m5, m6, m7, m8, m10, C3, F = sp.symbols(
    "d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 C3 F")

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
      + 3*d1**2*m6 + 6*m1*m6 + 6*d0*m7 + 6*d1*m8 + F*C3**23)

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
print("\nQ4 after substitutions (in dm2, dm1, d0, d1, C3, F):")
print(sp.factor(Q4r))

# Eliminate dm2 between Q2r and Q4r
res = sp.resultant(Q2r, Q4r, m2)
res = sp.factor(res)
print("\nResultant w.r.t. dm2, factored:")
print(res)
target = 18*C3**23*d1*m1**6*F + 8*C3**69*F**3 + 27*d0*m1**9
print("\nTarget principal equation:")
print(target)
print("\nResultant / target:")
print(sp.simplify(res / target))
assert sp.expand(res - sp.Rational(-27, 64) / m1**3 * target) == 0
print("\nCHECK PASSED: resultant = -27/(64*dm1^3) x the paper's principal equation.")
print("Remaining quotient factor: -27/(64*dm1**3)")
