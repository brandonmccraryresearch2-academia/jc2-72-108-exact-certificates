"""GGHV §5 elimination CERTIFICATE (tracked linear elimination).

Extends elimination_s6.py: instead of only checking the
resultant, this script tracks every elimination step as an
explicit combination of the 9 original equations, so the
final principal equation is obtained as an explicit
polynomial identity

    D * dm1 * target = sum_i P_i * orig_i

with P_i polynomials (in d0, d1, dm1, dm2, y) and D a
power of dm1. In Lean (over Q, with dm1 != 0) that identity
plus orig_i = 0 for all i gives target = 0 by `ring` and
nonzero cancellation — a genuine kernel certificate for
the §5 principal equation, given the 9 original equations.
The 9 originals themselves (the (D~^2)/(D~^3) coefficient
system) are still hypotheses: their derivation from C/F/D
expansions is D2, not closed here. The rescaling to
`nueva ecuacion principal` is also still open.
"""
import sympy as sp

d0, d1, m1, m2, m3, m4, m5, m6, m7, m8, m10, y, C3, F = sp.symbols(
    "d0 d1 dm1 dm2 dm3 dm4 dm5 dm6 dm7 dm8 dm10 y C3 F")

orig = {
    "D2_1": 2*d0*m1 + 2*d1*m2 + 2*m4,
    "D2_2": m1**2 + 2*d0*m2 + 2*d1*m3 + 2*m5,
    "D2_3": 2*m1*m2 + 2*d0*m3 + 2*d1*m4 + 2*m6,
    "D2_4": m2**2 + 2*m1*m3 + 2*d0*m4 + 2*d1*m5 + 2*m7,
    "D2_5": 2*m2*m3 + 2*m1*m4 + 2*d0*m5 + 2*d1*m6 + 2*m8,
    "D2_7": 2*m10 + 2*m3*m4 + 2*m2*m5 + 2*m1*m6 + 2*d0*m7 + 2*d1*m8,
    "Q1": (3*d0**2*m1 + 3*d1*m1**2 + 6*d0*d1*m2 + 3*m2**2 + 3*d1**2*m3
          + 6*m1*m3 + 6*d0*m4 + 6*d1*m5 + 3*m7),
    "Q2": (3*d0*m1**2 + 3*d0**2*m2 + 6*d1*m1*m2 + 6*d0*d1*m3 + 6*m2*m3
          + 3*d1**2*m4 + 6*m1*m4 + 6*d0*m5 + 6*d1*m6 + 3*m8),
    "Q4": (3*m10 + 3*m1**2*m2 + 3*d0*m2**2 + 6*d0*m1*m3 + 6*d1*m2*m3
          + 3*d0**2*m4 + 6*d1*m1*m4 + 6*m3*m4 + 6*d0*d1*m5 + 6*m2*m5
          + 3*d1**2*m6 + 6*m1*m6 + 6*d0*m7 + 6*d1*m8 + F*C3**23),
}

# eqs[name] = (expr, combo dict orig_name -> rational function)
eqs = {k: (sp.expand(v), {k: sp.Integer(1)}) for k, v in orig.items()}

def poly_coeff(expr, var):
    p = sp.Poly(expr, var)
    assert p.degree() <= 1, (var, p.degree())
    return sp.cancel(p.coeff_monomial(var)), sp.cancel(p.coeff_monomial(1))

def eliminate(var, src):
    expr, combo = eqs[src]
    cv, rest = poly_coeff(expr, var)
    assert cv != 0, (src, var)
    val = sp.cancel(-rest / cv)
    print(f"{src} -> {var} = {val}   (coeff {cv})")
    for name in list(eqs):
        if name == src:
            continue
        e, c = eqs[name]
        if not e.has(var):
            continue
        cf, _ = poly_coeff(e, var)
        ratio = sp.cancel(cf / cv)
        new_e = sp.expand(e.subs(var, val))
        new_c = {}
        for k in set(c) | set(combo):
            new_c[k] = sp.cancel(c.get(k, 0) - ratio * combo.get(k, 0))
        eqs[name] = (new_e, {k: v for k, v in new_c.items() if v != 0})
    # source equation is now used up; keep it out of the remaining set
    del eqs[src]

eliminate(m4, "D2_1")
eliminate(m5, "D2_2")
eliminate(m6, "D2_3")
eliminate(m7, "D2_4")
eliminate(m8, "D2_5")
eliminate(m3, "Q1")
eliminate(m10, "D2_7")
print("\nRemaining equations:", list(eqs))
Q2r, cQ2 = eqs["Q2"]
Q4r, cQ4 = eqs["Q4"]
print("Q2r =", sp.factor(Q2r))
print("Q4r =", sp.factor(Q4r))

# Cleared-denominator forms (see gcdex analysis)
q2 = d0*m1**3 + d1*m1**2*m2 + m2**3
q4 = 3*d0*d1*m1**3 + 3*d1**2*m1**2*m2 + 3*d1*m2**3 - 3*m1**3*m2 + 2*m1*F*C3**23
assert sp.expand(Q2r + sp.Rational(3, 2) / m1 * q2) == 0
assert sp.expand(Q4r - 1 / (2 * m1) * q4) == 0
print("Q2r, Q4r match cleared forms q2, q4.")

S = -3 * (9*d1**2*m1**6 + 9*d1*m1**4*m2**2 + 3*d1*m1**2*m2*(2*F*C3**23) + d1*(2*F*C3**23)**2 - 9*m1**7)
T = 9*d1*m1**6 + 9*m1**4*m2**2 + 3*m1**2*m2*(2*F*C3**23) + (2*F*C3**23)**2
target = 18*F*C3**23*d1*m1**6 + 8*F**3*C3**69 + 27*d0*m1**9
assert sp.expand(S * q2 + T * q4 - m1 * target) == 0
print("Cofactor identity S*q2 + T*q4 = dm1*target verified.")

# Final combination: m1*target = sum_i coeff_i * orig_i
coeff = {}
for k in set(cQ2) | set(cQ4):
    coeff[k] = sp.cancel(S * (-sp.Rational(2, 3) * m1) * cQ2.get(k, 0)
                         + T * (2 * m1) * cQ4.get(k, 0))
print("\nFinal coefficients (rational functions) and their denominators:")
dens = set()
for k, v in coeff.items():
    _, den = sp.fraction(sp.together(v))
    dens.add(sp.factor(den))
    print(k, "->", v)
print("Distinct denominators:", dens)

# Clear denominators: D = product of distinct denominators (they are powers of dm1)
D = sp.Integer(1)
for den in dens:
    D = sp.expand(D * den)
P = {}
for k, v in coeff.items():
    pv = sp.cancel(v * D)
    _, den = sp.fraction(sp.together(pv))
    assert den == 1, (k, pv)
    P[k] = sp.expand(pv)
print("\nClearing denominator D =", sp.factor(D))
for k in orig:
    print(f"P_{k} =", P.get(k, 0))
lhs = sp.expand(D * m1 * target - sum(P.get(k, 0) * orig[k] for k in orig))
print("\nFinal identity check D*dm1*target - sum P_i*orig_i == 0:", lhs == 0)
assert lhs == 0
print("CERTIFICATE PASSED: explicit polynomial identity for the §5 principal equation.")
print("\nLean-ready summary:")
print("  D =", sp.factor(D))
print("  target =", target)
