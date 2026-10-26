#!/usr/bin/env python3
"""Symbolic check of the two cases in the proof of the cut-cell Lemma (Lemma 4.2 of the manuscript).

Case 1 (x >= 2y-1, y >= 0):  Gamma - (1-xy)/4 = (2 - (x-y)^2 - 2y^2)/8, and (x-y)^2 + 2y^2 <= 2 on the triangle.
Case 2 (x <  2y-1):          with c = y/2 - (1+x)/4, tau = (1-y)/2, t* = (1-x)/4,
                             (c - y/4) x + 2 * int_0^{1/2} g = H(x,y) and Gamma - H = (1-y)(2x-y+3)/8.
Prints True/False for each identity; exit status 1 if any is False.
Needs sympy.   usage: py checks/lemma2_symbolic.py
"""
import sys
import sympy as sp

x, y, t = sp.symbols("x y t", real=True)
Gamma = (1 - x**2) / 8 + sp.Rational(3, 8) * (1 - y**2)
ok = True

# case 1
d1 = sp.simplify(8 * (Gamma - (1 - x * y) / 4) - (2 - (x - y) ** 2 - 2 * y**2))
print("case 1 identity:", d1 == 0); ok &= d1 == 0
for (vx, vy, val) in [(-1, 0, 1), (1, 0, 1), (1, 1, 2)]:
    v = (vx - vy) ** 2 + 2 * vy**2
    print(f"  vertex ({vx},{vy}): (x-y)^2+2y^2 = {v} (<= 2: {v <= 2})"); ok &= v == val

# case 2
c = y / 2 - (1 + x) / 4
tau = (1 - y) / 2
ts = (1 - x) / 4
I = (sp.integrate(c + t, (t, 0, tau)) + sp.integrate(c - t - y + 1, (t, tau, ts)) + sp.integrate(t - c, (t, ts, sp.Rational(1, 2))))
bound = sp.expand((c - y / 4) * x + 2 * I)
H = (1 + 4 * y - 4 * y**2 - 2 * x + 2 * x * y - x**2) / 8
print("case 2 integral == H:", sp.simplify(bound - H) == 0); ok &= sp.simplify(bound - H) == 0
print("Gamma - H == (1-y)(2x-y+3)/8:", sp.simplify(Gamma - H - (1 - y) * (2 * x - y + 3) / 8) == 0)
ok &= sp.simplify(Gamma - H - (1 - y) * (2 * x - y + 3) / 8) == 0
# the three pieces of g agree with max(t-c, c-Psi_lo) on a sample grid
import itertools
from fractions import Fraction as F
bad = 0
for xv, yv in itertools.product([F(k, 8) for k in range(-8, 9)], repeat=2):
    if not (xv < 2 * yv - 1):
        continue
    cv = yv / 2 - (1 + xv) / 4
    for tv in [F(k, 64) for k in range(0, 33)]:
        lo = max(-tv, tv + yv - 1)
        g = max(tv - cv, cv - lo)
        tauv, tsv = (1 - yv) / 2, (1 - xv) / 4
        piece = cv + tv if tv <= tauv else (cv - tv - yv + 1 if tv <= tsv else tv - cv)
        bad += g != piece
print("piecewise form of g matches max(t-c, c-Psi_lo) on a rational grid; mismatches:", bad); ok &= bad == 0
print("ALL OK" if ok else "FAILED")
sys.exit(0 if ok else 1)
