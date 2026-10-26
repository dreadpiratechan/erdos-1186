"""Erdos 1186, formalisation of the claimed proof of delta_3 = 117/2192: grid data for the shared Lean interface.

Writes `lean/Erdos/Proofs/P1186ExData.lean` (the two grids G24, G8: cell endpoints, Lemma 2 constants a_i, b_i) and
`problems/1186/exact/data/grids.json` (the same data plus the cell signs and the pair areas A4 for the certificate lanes).

Model (exact Fractions only), as in the reviewers' reports (coordinator NIGHT/results/rev1186m.md, rev1186c.md, ver1186c.md):
phi* = the PRS 12-block colouring (Lean `Erdos1186Day.c1`, blocks 28,6,28,37,59,116,116,59,37,28,6,28 of 548);
R = {(a, b) : a/2 < b <= (1 + a)/2} (a = end, b = middle); h(x) = -(phi*(x)/2) [int_{x/2}^{(1+x)/2} phi* + int_{max(0,2x-1)}^{min(1,2x)} phi*];
a_i = w_i min_{I_i} h; b_i = w_i^2 / (2 M_i), M_i = sup over levels v of the sum of 1/|slope| over the unit pieces of h on I_i
that reach v. The model code follows the independent verifier ver1186c (vmodel.py / verify.py), rewritten here.

Checks done before writing: Q(phi*) = -5/137, int h = 5/137, h >= 0 on the lattice with zeros exactly at the 11 edges, every
cell sign-constant, and for every ordered pair of cells the kernel sum A4 = sum K4(1096, p, q) equals 4 * 1096^2 * (exact polygon
area of R cap I_i x I_j).

Usage: py -I problems/1186/exact/gen_interface.py <certs_exact.json>   (the grids are read from the reviewer certificate file)
"""
import io
import json
import sys
from fractions import Fraction as Fr
from pathlib import Path

U = 1096
TH548 = [28, 34, 62, 99, 158, 274, 390, 449, 486, 514, 520, 548]
EDGES = [2 * t for t in TH548[:-1]]


def c1(x):
    """Lean `Erdos1186Day.c1` on [1, 548]."""
    for thr, val in [(28, True), (34, False), (62, True), (99, False), (158, True), (274, False), (390, True),
                     (449, False), (486, True), (514, False), (520, True)]:
        if x <= thr:
            return val
    return False


SGN = [1 if c1(k // 2 + 1) else -1 for k in range(U)]          # phi* on the unit cell [k, k+1]/1096
FU = [0]
for k in range(U):
    FU.append(FU[-1] + SGN[k])
assert FU[U] == 0


def F(x):
    x = Fr(x)
    k = int(x)
    if k >= U:
        return Fr(FU[U])
    return FU[k] + (x - k) * SGN[k]


def hval(x, s):
    x = Fr(x)
    p1 = F((U + x) / 2) - F(x / 2)
    p2 = F(min(Fr(U), 2 * x)) - F(max(Fr(0), 2 * x - U))
    return -Fr(s) * (p1 + p2) / (2 * U)


def K4(L, p, q):
    """Lean `Erdos1186Night2M2.K4` (1-indexed unit cells, p = end, q = middle)."""
    m = 2 * q - p - 1
    if 1 <= m <= L - 2:
        return 4
    if m == 0 or m == L - 1:
        return 3
    if m == -1 or m == L:
        return 1
    return 0


def area_units(A0, A1, B0, B1):
    """area (unit^2) of R cap [A0,A1] x [B0,B1] (unit coordinates), exact."""
    A0, A1, B0, B1 = Fr(A0), Fr(A1), Fr(B0), Fr(B1)
    bps = {A0, A1}
    for t in (2 * B0, 2 * B1, 2 * B0 - U, 2 * B1 - U):
        if A0 < t < A1:
            bps.add(t)
    xs = sorted(bps)

    def f(A):
        return max(Fr(0), min(B1, (U + A) / 2) - max(B0, A / 2))

    return sum(((f(p) + f(q)) * (q - p) / 2 for p, q in zip(xs, xs[1:])), Fr(0))


def anchors():
    # Q(phi*) = (1/U^2) sum_{p,q} (K4/4) s_p s_q
    tot = 0
    for p in range(1, U + 1):
        for q in range(1, U + 1):
            k = K4(U, p, q)
            if k:
                tot += k * SGN[p - 1] * SGN[q - 1]
    assert Fr(tot, 4 * U * U) == Fr(-5, 137), Fr(tot, 4 * U * U)
    hk = [hval(k, SGN[k] if k < U else SGN[U - 1]) for k in range(U + 1)]
    assert all(v >= 0 for v in hk)
    assert [k for k in range(U + 1) if hk[k] == 0] == EDGES, [k for k in range(U + 1) if hk[k] == 0]
    # int h (h linear on each unit cell): trapezoid rule is exact
    ih = sum((hval(k, SGN[k]) + hval(k + 1, SGN[k])) / 2 for k in range(U)) / U
    assert ih == Fr(5, 137), ih
    return tot


def grid_data(pts):
    n = len(pts) - 1
    assert pts[0] == 0 and pts[-1] == U and all(pts[i] < pts[i + 1] for i in range(n))
    assert all(e in pts for e in EDGES)
    w = [Fr(pts[i + 1] - pts[i], U) for i in range(n)]
    sg = []
    for i in range(n):
        assert len(set(SGN[pts[i]:pts[i + 1]])) == 1, i
        sg.append(SGN[pts[i]])
    hk = [hval(k, SGN[k] if k < U else SGN[U - 1]) for k in range(U + 1)]
    # one-sided values on each unit piece (h is continuous, checked by the anchors' zero test and here)
    for k in range(1, U):
        assert hval(k, SGN[k - 1]) == hval(k, SGN[k]), k
    a, b = [], []
    for i in range(n):
        ks = range(pts[i], pts[i + 1] + 1)
        a.append(w[i] * min(hk[k] for k in ks))
        pieces = []
        for k in range(pts[i], pts[i + 1]):
            d = hk[k + 1] - hk[k]
            assert d != 0, ("flat piece", i, k)
            pieces.append((min(hk[k], hk[k + 1]), max(hk[k], hk[k + 1]), 1 / (abs(d) * U)))
        lv = sorted(set(hk[k] for k in ks))
        M = max(sum(inv for (pl, ph, inv) in pieces if pl <= v0 and ph >= v1) for v0, v1 in zip(lv, lv[1:]))
        b.append(w[i] ** 2 / (2 * M))
    # pair areas: kernel sum vs exact polygon area
    A4 = []
    for i in range(n):
        row = []
        for j in range(n):
            s = sum(K4(U, p, q) for p in range(pts[i] + 1, pts[i + 1] + 1) for q in range(pts[j] + 1, pts[j + 1] + 1))
            assert Fr(s, 4) == area_units(pts[i], pts[i + 1], pts[j], pts[j + 1]), (i, j)
            row.append(s)
        A4.append(row)
    return {"pts": pts, "sgn": sg, "a": [str(x) for x in a], "b": [str(x) for x in b], "A4": A4}


def lean_rat(x):
    x = Fr(x)
    return f"({x.numerator} / {x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"


def main():
    certs = json.load(io.open(sys.argv[1], encoding="utf-8"))
    pts = {}
    for v in certs["slabs"].values():
        pts.setdefault(v["grid"], v["pts"])
    assert certs["inner"]["pts"] == pts["g24"]
    tot = anchors()
    print("anchors OK: sum K4 s s =", tot, "Q(phi*) = -5/137, int h = 5/137, 11 zeros")
    root = Path(__file__).resolve().parents[2]  # the repository root
    out = {}
    for name in ("g24", "g8"):
        out[name] = grid_data(pts[name])
        print(name, "cells", len(out[name]["pts"]) - 1, "A4 checks OK")
    io.open(root / "computation/theorem-c/data/grids.json", "w", encoding="utf-8").write(json.dumps(out))
    L = ["import Mathlib", "",
         "/-!", "# Erdos 1186 - grid data for the formalisation of the claimed proof (generated, do not edit)", "",
         "Generated by `py -I problems/1186/exact/gen_interface.py <certs_exact.json>`; see that file for the model and the",
         "checks run before writing. Cell endpoints are in units of 1/1096; `a`, `b` are the Lemma 2 (bathtub) constants.", "-/", "",
         "namespace Erdos1186Ex", "",
         "/-- A grid of `[0, 1]`: cell endpoints in units of `1/1096`, and the Lemma 2 constants of each cell. -/",
         "structure Grid where", "  pts : List ℕ", "  a : List ℚ", "  b : List ℚ", ""]
    for name, lname in (("g24", "G24"), ("g8", "G8")):
        g = out[name]
        L.append(f"/-- grid `{name}` ({len(g['pts']) - 1} cells). -/")
        L.append(f"def {lname} : Grid where")
        L.append("  pts := [" + ", ".join(str(p) for p in g["pts"]) + "]")
        L.append("  a := [" + ", ".join(lean_rat(x) for x in g["a"]) + "]")
        L.append("  b := [" + ", ".join(lean_rat(x) for x in g["b"]) + "]")
        L.append("")
    L += ["end Erdos1186Ex", ""]
    io.open(root / "lean/Erdos/Proofs/P1186ExData.lean", "w", encoding="utf-8", newline="\n").write("\n".join(L))
    print("wrote P1186ExData.lean and grids.json")


if __name__ == "__main__":
    main()
