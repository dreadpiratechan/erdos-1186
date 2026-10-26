"""Erdos 1186 (lane excert): exact Python mirror of the integer formulas that the Lean checker evaluates.

Formalises (as data) the finite part of the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05,
unrefereed); the mathematics is its author's.  Input: `data/cert_region{r}.json` (lane excertsdp).

Every formula here is the one written in `lean/Erdos/Proofs/P1186ExCert*.lean`; `check_region(r)` recomputes the
whole integer matrix `U * N` from the tables and compares with the JSON `N` entry by entry.
"""
import json
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import sdpmodel  # noqa: E402

Q = 1 << 40
Z0 = 360364800
DZ = Q * Z0
R = 21920            # = 20 * 1096
U = R * R
K1096 = 1096
REG = {1: ("G24", 0, 4), 2: ("G24", 4, 6), 3: ("G24", 6, 8), 4: ("G8", 8, 9), 5: ("G8", 9, 10)}   # lo, hi over 20


def load(r):
    d = json.load(open(HERE / "data" / ("cert_region%d.json" % r), encoding="utf-8"))
    return d


class Reg:
    pass


def build(r):
    """All integer tables of region r (dict of python lists), straight from the JSON."""
    d = load(r)
    gname, loN, hiN = REG[r]
    G = sdpmodel.load_grid(gname)
    n = G.N
    assert d["n"] == n
    assert Fr(loN, 20) == Fr(d["lo"]) and Fr(hiN, 20) == Fr(d["hi"])
    o = Reg()
    o.r, o.d, o.G, o.n, o.loN, o.hiN = r, d, G, n, loN, hiN
    mu_den = int(d["mu_den"])
    assert (int(d["D"]) % mu_den) == 0
    o.Zn = int(d["D"]) // mu_den
    assert int(d["D"]) == DZ
    o.len = list(G.len)
    o.lo = G.pts[:-1]
    o.hi = G.pts[1:]
    o.sgn = list(G.sgn)
    # A4 by the Lean rule (corner tests, exact A4 only for the rest)
    A4v = [[0] * n for _ in range(n)]
    kind = [[""] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            dmin = 2 * (o.lo[j] + 1) - o.hi[i] - 1
            dmax = 2 * o.hi[j] - (o.lo[i] + 1) - 1
            if dmin >= 1 and dmax <= K1096 - 2:
                A4v[i][j] = 4 * o.len[i] * o.len[j]
                kind[i][j] = "full"
            elif dmax <= -2 or dmin >= K1096 + 1:
                A4v[i][j] = 0
                kind[i][j] = "empty"
            else:
                A4v[i][j] = G.A4[i][j]
                kind[i][j] = "cut"
            assert A4v[i][j] == G.A4[i][j]
    o.A4v, o.kind = A4v, kind
    # theta table
    th = [[(0 if kind[i][j] == "full" else (Q if kind[i][j] == "empty" else None)) for j in range(n)] for i in range(n)]
    assert int(d["theta_den"]) == Q
    for i, j, t in d["cuts"]:
        assert kind[i][j] == "cut", (i, j)
        th[i][j] = int(t)
    for i in range(n):
        for j in range(n):
            assert th[i][j] is not None and 0 <= th[i][j] <= Q
    o.theta = th
    # alpha, beta
    o.alpha = []
    o.beta = []
    for i in range(n):
        a = G.a[i] * DZ
        b = G.b[i] * DZ
        assert a.denominator == 1 and b.denominator == 1
        o.alpha.append(int(a))
        o.beta.append(int(b))
    # forms
    z = lambda: [0] * n
    o.Yv, o.Ov, o.A1, o.A2, o.A3, o.A4w = z(), z(), z(), z(), z(), z()
    o.YY = [[0] * n for _ in range(n)]
    o.OO = [[0] * n for _ in range(n)]
    o.YO = [[0] * n for _ in range(n)]
    o.p = o.r_ = o.s = 0
    o.tri = []
    for f in d["forms"]:
        k = f[0]
        num = int(f[-1])
        assert num >= 0
        if k == "y":
            o.Yv[f[1]] += num
        elif k == "o":
            o.Ov[f[1]] += num
        elif k == "ml":
            o.p += num
        elif k == "hm":
            o.r_ += num
        elif k == "yy":
            assert f[1] <= f[2]
            o.YY[f[1]][f[2]] += num
        elif k == "oo":
            assert f[1] <= f[2]
            o.OO[f[1]][f[2]] += num
        elif k == "yo":
            o.YO[f[1]][f[2]] += num
        elif k == "yml":
            o.A1[f[1]] += num
        elif k == "oml":
            o.A2[f[1]] += num
        elif k == "yhm":
            o.A3[f[1]] += num
        elif k == "ohm":
            o.A4w[f[1]] += num
        elif k == "mhm":
            o.s += num
        elif k == "tri":
            o.tri.append(f[1:])
        else:
            raise ValueError(k)
    return o


def pair_coefs(o, i, j):
    s = 1 if o.sgn[i] * o.sgn[j] == 1 else -1
    th = o.theta[i][j]
    ln = o.len[i] * o.len[j]
    K = 300 * (Q - th) * ln
    if s == 1:
        c = 75 * (Q - th) * (4 * ln - o.A4v[i][j])
    else:
        c = 75 * th * o.A4v[i][j]
    return s, K, c


def semantic(o, tri_c0=0, tri_l=None, tri_q=None):
    """The integer coefficients (c0', l', q') of  U*D*L_theta - FS  (the polynomial that the matrix U*N must reproduce)."""
    n, Zn = o.n, o.Zn
    Lo, Hi = 1096 * o.loN, 1096 * o.hiN
    om = [20 * l for l in o.len]
    Yv = [Zn * x for x in o.Yv]
    Ov = [Zn * x for x in o.Ov]
    A1 = [Zn * x for x in o.A1]
    A2 = [Zn * x for x in o.A2]
    A3 = [Zn * x for x in o.A3]
    A4 = [Zn * x for x in o.A4w]
    YY = [[Zn * x for x in r] for r in o.YY]
    OO = [[Zn * x for x in r] for r in o.OO]
    YO = [[Zn * x for x in r] for r in o.YO]
    p, r_, s = Zn * o.p, Zn * o.r_, Zn * o.s
    u1 = [A1[i] - A2[i] for i in range(n)]
    u2 = [A3[i] - A4[i] for i in range(n)]
    u10 = sum(A2) + p
    u20 = sum(A4) + r_
    # pair part
    cP = 0
    lP = [U * o.alpha[i] for i in range(n)]
    qP = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s_, K, c = pair_coefs(o, i, j)
            cP -= U * c
            qP[i][j] = U * (s_ * K + (o.beta[i] if i == j else 0))
    # form part
    cF = U * (sum(Ov) + sum(sum(rw) for rw in OO)) + R * (-Lo * u10 + Hi * u20) - s * Lo * Hi
    lF = []
    for i in range(n):
        rowOO = sum(OO[i])
        colOO = sum(OO[k][i] for k in range(n))
        rowYO = sum(YO[i])
        lF.append(U * (Yv[i] - Ov[i] - rowOO - colOO + rowYO)
                  + R * (om[i] * u10 - Lo * u1[i] - om[i] * u20 + Hi * u2[i]) + s * om[i] * (Lo + Hi))
    qF = [[U * (YY[i][j] + OO[i][j] - YO[i][j]) + R * om[j] * (u1[i] - u2[i]) - s * om[i] * om[j]
           for j in range(n)] for i in range(n)]
    c0 = cP - cF
    l = [lP[i] - lF[i] for i in range(n)]
    q = [[qP[i][j] - qF[i][j] for j in range(n)] for i in range(n)]
    if tri_l is not None:
        c0 -= tri_c0
        l = [l[i] - tri_l[i] for i in range(n)]
        q = [[q[i][j] - tri_q[i][j] for j in range(n)] for i in range(n)]
    return c0, l, q


def tri_poly(o):
    """U-scaled polynomial of sum_t nu_t tri_t:  returns (c0, l, q) with q symmetric (= 2 U R), R = rowvec of the cuts."""
    n = o.n
    Rm = [[0] * n for _ in range(n)]
    snu = 0
    for t in o.tri:
        i, j, k, s1, s2, s3, num = [int(x) for x in t]
        assert i < j < k and s1 * s2 * s3 == 1 and all(x in (1, -1) for x in (s1, s2, s3)) and num >= 0
        nu = o.Zn * num
        snu += nu
        for (a, b, sg) in ((i, j, s1), (j, k, s2), (i, k, s3)):
            Rm[a][b] += nu * sg
            Rm[b][a] += nu * sg
    sumR = sum(sum(rw) for rw in Rm)
    assert sumR % 2 == 0
    c0 = U * (snu + sumR // 2)
    l = [-2 * U * sum(Rm[a]) for a in range(n)]
    q = [[2 * U * Rm[a][b] for b in range(n)] for a in range(n)]
    return c0, l, q, Rm


def padded_N(o):
    """(n+1) x (n+1) integer matrix N of the JSON; region 1 (constant row zero) is padded with a zero row/column."""
    N = [[int(x) for x in row] for row in o.d["N"]]
    n = o.n
    if o.d["const_row_zero"]:
        assert len(N) == n
        N = [[0] * (n + 1)] + [[0] + row for row in N]
    assert len(N) == n + 1 and all(len(row) == n + 1 for row in N)
    return N


def check_entries(o, tri=None):
    c0, l, q = semantic(o, *(tri or (0, None, None)))
    n = o.n
    N = padded_N(o)
    bad = 0
    if U * N[0][0] != c0:
        bad += 1
        print("const entry differs", U * N[0][0] - c0)
    for i in range(n):
        if 2 * U * N[0][i + 1] != l[i] or 2 * U * N[i + 1][0] != l[i]:
            bad += 1
            if bad < 5:
                print("linear entry", i, 2 * U * N[0][i + 1] - l[i])
    for i in range(n):
        for j in range(n):
            if 2 * U * N[i + 1][j + 1] != q[i][j] + q[j][i]:
                bad += 1
                if bad < 5:
                    print("quad entry", i, j, 2 * U * N[i + 1][j + 1] - q[i][j] - q[j][i])
    return bad


if __name__ == "__main__":
    for r in [int(a) for a in sys.argv[1:]] or [1, 2, 3, 4, 5]:
        o = build(r)
        print("region", r, "n", o.n, "forms", len(o.d["forms"]), "tri", len(o.tri), "Zn", o.Zn)
        if o.tri:
            c0t, lt, qt, Rm = tri_poly(o)
            print("  mismatches:", check_entries(o, (c0t, lt, qt)))
        else:
            print("  mismatches:", check_entries(o))
