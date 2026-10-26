"""Erdos 1186 exact lane (excertsdp): exact verifier of data/cert_region{r}.json (own code; separate from make_certs.py).

For each region it checks, in exact integer / rational arithmetic:
  A. structure: cut list = the cut pairs of the grid (0 < A4 < 4 len_i len_j) in lexicographic order, theta numerators in
     [0, theta_den], every form valid (kind, indices, triangles i<j<k with s1 s2 s3 = +1), numerators integers >= 0, no duplicates.
  B. the matrix N: rebuilt here by a SECOND implementation (atom Gram formulation  S = L_theta - A^T mu A  for the
     product forms with  A = atom coefficient matrix, plus explicit expansion of the triangle forms) and compared entrywise with
     the stored N = D * S  (B' = 0).
  C. the polynomial identity  L_theta(y) - sum_f mu_f f(y) = v'Sv  at random rational points, with L_theta, f taken from the
     DEFINITIONS (sdpmodel.lval_theta / eval_form), and  Lval(y) >= L_theta(y)  and  f(y) >= 0  at random points of the region.
  D. N is PSD: E = T2*N - C C^T (exact integers) is diagonally dominant;  and the margin  S >= 2^-k I  (dominance for N - ceil(D/2^k) I).
  E. region 1 only: the constant row of S is zero (S_00 = S_0i = 0) and the y-block is certified.
What this establishes (for the data given, conditional on nothing but the Lean definitions in sdpmodel.py being a faithful copy of
P1186Ex.lean):  for every y in [0,1]^N with lo <= m <= hi,  Lval G y >= L_theta(y) = v'Sv + sum_f mu_f f(y) >= 0.
Usage: py -I verify_certs.py [region ...]   (default 1..5)
"""
import io
import json
import os
import random
import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402

import psdcert as P  # noqa: E402
import sdpmodel as M  # noqa: E402


def fr(s):
    return Fr(s)


def load(region):
    return json.load(io.open(M.EXACT / "data" / ("cert_region%d.json" % region), encoding="utf-8"))


def triangle_expand(i, j, k, s1, s2, s3):
    """f = 1 + s1 z_i z_j + s2 z_j z_k + s3 z_i z_k, z = 1 - 2y, as (const, {idx: lin coef}, {(a,b): coef of y_a y_b, a<b})."""
    c = 1 + s1 + s2 + s3
    lin = {i: -2 * (s1 + s3), j: -2 * (s1 + s2), k: -2 * (s2 + s3)}
    quad = {(i, j): 4 * s1, (j, k): 4 * s2, (i, k): 4 * s3}
    return c, lin, quad


def rebuild_N(cert, G, R):
    """Second implementation of S (scaled by D).  Returns a numpy object matrix of Python ints, size (n+1) x (n+1)."""
    n = G.N
    D = cert["D"]
    Q = cert["theta_den"]
    mu_den = cert["mu_den"]
    Z0 = cert["Z0"]
    assert D == Q * Z0 and D % mu_den == 0
    lo, hi = R[1], R[2]
    W = M.U
    # ---- L_theta, scaled by D (every term an exact integer) -----------------------------------------------------
    N = np.zeros((n + 1, n + 1), dtype=object)
    for a in range(n + 1):
        for b in range(n + 1):
            N[a][b] = 0
    th = {(i, j): t for i, j, t in cert["cuts"]}

    def theta_num(i, j):
        kd = G.kind(i, j)
        if kd == "cut":
            return th[(i, j)]
        return 0 if kd == "full" else Q

    def put(a, b, x):             # symmetric-matrix entry: x added to N[a][b] (and N[b][a] if a != b)
        x = Fr(x)
        assert x.denominator == 1, (a, b, x)
        x = int(x)
        N[a][b] += x
        if a != b:
            N[b][a] += x

    for i in range(n):
        put(0, i + 1, Fr(D) * G.a[i] / 2)
        put(i + 1, i + 1, Fr(D) * G.b[i])
    const = Fr(0)
    for i in range(n):
        for j in range(n):
            t = theta_num(i, j)
            om = Q - t                                 # (1 - theta) * Q
            lij = G.len[i] * G.len[j]
            # D * w_i w_j (1-theta) = Z0 * om * lij / W^2
            wterm = Fr(Z0 * om * lij, W * W)
            if G.sgn[i] * G.sgn[j] == 1:
                coef = wterm
                const -= Fr(Z0 * om, 1) * Fr(4 * lij - G.A4[i][j], 4 * W * W)       # D*(1-th)*Aout, Aout=(4 lij - A4)/(4 W^2)
            else:
                coef = -wterm
                const -= Fr(Z0 * t * G.A4[i][j], 4 * W * W)                       # D*th*Ain
            if i == j:
                put(i + 1, i + 1, coef)
            else:
                put(i + 1, j + 1, coef / 2)                      # ordered pair (i,j) and (j,i) each add coef/2 to the symmetric entry
    put(0, 0, const)
    # ---- product forms via atoms:  S -= A^T mu A  (mu symmetric over atoms) --------------------------------------
    # atoms: 0:'1'  1+i:'y_i'  1+n+i:'o_i'  1+2n:'ml'  2+2n:'hm'; coefficient vectors over v=(1,y), scaled by 2*W*20 to be ints
    SC = 2 * W * 20
    na = 2 * n + 3
    A = np.zeros((na, n + 1), dtype=object)
    for a in range(na):
        for b in range(n + 1):
            A[a][b] = 0
    A[0][0] = SC
    for i in range(n):
        A[1 + i][i + 1] = SC
        A[1 + n + i][0] = SC
        A[1 + n + i][i + 1] = -SC
    lo_n = lo * 20
    hi_n = hi * 20
    assert lo_n.denominator == 1 and hi_n.denominator == 1
    A[1 + 2 * n][0] = -int(lo_n) * W * 2
    A[2 + 2 * n][0] = int(hi_n) * W * 2
    for k in range(n):
        A[1 + 2 * n][k + 1] = G.len[k] * 20 * 2
        A[2 + 2 * n][k + 1] = -G.len[k] * 20 * 2

    def atom_index(name, i=None):
        return {"one": 0, "y": 1 + (i or 0), "o": 1 + n + (i or 0), "ml": 1 + 2 * n, "hm": 2 + 2 * n}[name]

    pairs = {"y": ("y", "one"), "o": ("o", "one"), "ml": ("ml", "one"), "hm": ("hm", "one")}
    MU = np.zeros((na, na), dtype=object)
    for a in range(na):
        for b in range(na):
            MU[a][b] = 0
    tri_forms = []
    for f in cert["forms"]:
        kind, args, num = f[0], f[1:-1], f[-1]
        if kind == "tri":
            tri_forms.append((args, num))
            continue
        if kind in ("y", "o"):
            pa, pb = atom_index(kind, args[0]), 0
        elif kind in ("ml", "hm"):
            pa, pb = atom_index(kind), 0
        elif kind == "yy":
            pa, pb = atom_index("y", args[0]), atom_index("y", args[1])
        elif kind == "oo":
            pa, pb = atom_index("o", args[0]), atom_index("o", args[1])
        elif kind == "yo":
            pa, pb = atom_index("y", args[0]), atom_index("o", args[1])
        elif kind == "yml":
            pa, pb = atom_index("y", args[0]), atom_index("ml")
        elif kind == "oml":
            pa, pb = atom_index("o", args[0]), atom_index("ml")
        elif kind == "yhm":
            pa, pb = atom_index("y", args[0]), atom_index("hm")
        elif kind == "ohm":
            pa, pb = atom_index("o", args[0]), atom_index("hm")
        elif kind == "mhm":
            pa, pb = atom_index("ml"), atom_index("hm")
        else:
            raise KeyError(kind)
        # f = l_pa * l_pb  ->  symmetric matrix (l_pa l_pb^T + l_pb l_pa^T)/2 : put num/2 at (pa,pb) and (pb,pa)
        # (pa == pb: both lines add num to the same cell, i.e. 2*num, which is what the /2 in `scale` expects)
        MU[pa][pb] += num
        MU[pb][pa] += num
    # D * (mu_num / mu_den) * (1/2) * sum(A^T MU A)/SC^2  must be integral in total; compute exactly with Fractions at the end
    Tm = A.T.dot(MU).dot(A)                       # (n+1)x(n+1) object ints = SC^2 * (sum mu_num * 2 * sym(l_a l_b^T))
    scale = Fr(D, mu_den) / (2 * SC * SC)
    for a in range(n + 1):
        for b in range(a, n + 1):
            x = scale * Tm[a][b]
            assert x.denominator == 1, (a, b)
            x = int(x)
            N[a][b] -= x
            if a != b:
                N[b][a] -= x
    # ---- triangle forms: explicit expansion --------------------------------------------------------------------
    for args, num in tri_forms:
        i, j, k, s1, s2, s3 = args
        c, lin, quad = triangle_expand(i, j, k, s1, s2, s3)
        mu = Fr(num * D, mu_den)
        assert mu.denominator == 1
        mu = int(mu)
        N[0][0] -= mu * c
        for idx, cf in lin.items():
            assert (mu * cf) % 2 == 0 or True
            x = Fr(mu * cf, 2)
            assert x.denominator == 1, "odd"
            N[0][idx + 1] -= int(x)
            N[idx + 1][0] -= int(x)
        for (a, b), cf in quad.items():
            x = Fr(mu * cf, 2)
            assert x.denominator == 1
            N[a + 1][b + 1] -= int(x)
            N[b + 1][a + 1] -= int(x)
    return N


def verify(region, seed=12345, npoints=6):
    t0 = time.time()
    cert = load(region)
    assert cert["format"] == "excertsdp-v1" and cert["region"] == region
    R = M.REGIONS[region]
    assert cert["grid"] == R[0] and fr(cert["lo"]) == R[1] and fr(cert["hi"]) == R[2]
    G = M.load_grid(R[0])
    n = G.N
    assert cert["n"] == n
    Q, mu_den, D = cert["theta_den"], cert["mu_den"], cert["D"]
    assert cert["bprime"] == "0"
    # ---- A. structure -------------------------------------------------------------------------------------------
    cl = G.cuts()
    assert [(i, j) for i, j, _ in cert["cuts"]] == cl, "cut list differs from the grid's cut pairs"
    theta = {}
    for i, j, t in cert["cuts"]:
        assert isinstance(t, int) and 0 <= t <= Q
        theta[(i, j)] = Fr(t, Q)
    seen = set()
    forms_mu = []
    for f in cert["forms"]:
        form, num = f[:-1], f[-1]
        assert isinstance(num, int) and num >= 0, f
        M.check_form_valid(G, form)
        key = tuple(form)
        assert key not in seen, ("duplicate form", key)
        seen.add(key)
        forms_mu.append((form, Fr(num, mu_den)))
    kinds = {}
    for f in cert["forms"]:
        kinds[f[0]] = kinds.get(f[0], 0) + 1
    print("[region %d] A. structure OK: %d cut pairs, %d forms %s (%.1fs)" % (region, len(cl), len(forms_mu), kinds, time.time() - t0), flush=True)
    # ---- B. second implementation of N -----------------------------------------------------------------------------
    N2 = rebuild_N(cert, G, R)
    Nst = np.array(cert["N"], dtype=object)
    if cert["const_row_zero"]:
        assert all(N2[0][j] == 0 for j in range(n + 1)), "constant row of S is not zero"
        N2 = N2[1:, 1:]
    assert N2.shape == Nst.shape
    assert (N2 == Nst).all(), "stored N differs from the rebuilt N"
    print("[region %d] B. stored N == independently rebuilt N (%d x %d exact integers) (%.1fs)" % (region, *N2.shape, time.time() - t0), flush=True)
    # ---- C. identity at random points and soundness of the pieces ---------------------------------------------------
    rng = random.Random(seed + region)
    Nfull = np.array(cert["N"], dtype=object)

    def vSv(y):
        v = [Fr(1)] + list(y) if not cert["const_row_zero"] else list(y)
        tot = Fr(0)
        for a in range(len(v)):
            row = Nfull[a]
            s = sum(int(row[b]) * v[b] for b in range(len(v)))
            tot += v[a] * s
        return tot / D

    lo, hi = R[1], R[2]
    for p in range(npoints):
        # random y in [0,1]^n with denominators 1000
        y = [Fr(rng.randint(0, 1000), 1000) for _ in range(n)]
        lt = M.lval_theta(G, theta, y)
        rhs = sum(mu * M.eval_form(G, R, form, y) for form, mu in forms_mu)
        assert lt - rhs == vSv(y), "identity fails at a random point"
        lv = M.lval_exact(G, y)
        assert lv >= lt, "Lval < L_theta"
    print("[region %d] C1. identity L_theta - sum mu f = v'Sv exact at %d random points; Lval >= L_theta there (%.1fs)" % (region, npoints, time.time() - t0), flush=True)
    # points inside the region: scale a random vector so that m lands in [lo, hi]
    inside = 0
    for p in range(npoints):
        for _ in range(100):
            y = [Fr(rng.randint(0, 1000), 1000) for _ in range(n)]
            m = M.mval(G, y)
            if m == 0:
                continue
            target = rng.choice([lo, hi, (lo + hi) / 2, lo + (hi - lo) * Fr(rng.randint(0, 100), 100)])
            if target == 0:
                continue
            lam = target / m
            if lam > 1:
                continue
            y = [(yy * lam).limit_denominator(10 ** 6) for yy in y]
            m = M.mval(G, y)
            if lo <= m <= hi and all(0 <= yy <= 1 for yy in y):
                break
        else:
            continue
        inside += 1
        for form, mu in forms_mu:
            assert M.eval_form(G, R, form, y) >= 0, ("form negative on the region", form)
        lt = M.lval_theta(G, theta, y)
        assert lt >= 0 and M.lval_exact(G, y) >= lt
    print("[region %d] C2. %d random region points: every form >= 0, Lval >= L_theta >= 0 (%.1fs)" % (region, inside, time.time() - t0), flush=True)
    # ---- D. PSD certificate -------------------------------------------------------------------------------------------
    ch = cert["chol"]
    rows = ch["rows"]
    assert len(rows) == len(Nst) and all(len(rows[i]) == i + 1 for i in range(len(rows)))
    E = P.exact_E(Nst, P.full_C(rows), ch["T2"])
    ok, worst = P.check_dominance(E)
    assert ok, ("dominance fails", worst)
    print("[region %d] D1. N PSD: E = T2*N - C C^T diagonally dominant, T2=%d, min slack %d >= 0 (%.1fs)" % (region, ch["T2"], worst[1], time.time() - t0), flush=True)
    kk = cert["margin"]["eta_pow2"]
    shift = (D + (1 << kk) - 1) >> kk
    N3 = Nst.copy()
    for i in range(len(N3)):
        N3[i][i] -= shift
    c3 = P.certify(N3, D, T2_list=(1, 16, 256, 4096), shift_fracs=(0.5, 0.8))
    E3 = P.exact_E(N3, P.full_C(c3["rows"]), c3["T2"])
    ok3, w3 = P.check_dominance(E3)
    assert ok3
    print("[region %d] D2. margin: S >= 2^-%d I (= %.3e) certified by dominance on N - ceil(D/2^k) I (%.1fs)" % (region, kk, 2.0 ** -kk, time.time() - t0), flush=True)
    # ---- E. summary ---------------------------------------------------------------------------------------------------
    if cert["const_row_zero"]:
        print("[region %d] E. constant row of S is zero; y-block P certified PSD; L >= y'Py + sum mu f >= 0" % region)
    else:
        print("[region %d] E. B' = 0; S_00 = %.4e > 0 (the reviewers' slack B sits in S_00); L >= v'Sv + sum mu f >= 0" % (region, Nst[0][0] / D))
    return True


if __name__ == "__main__":
    regs = [int(a) for a in sys.argv[1:]] or [1, 2, 3, 4, 5]
    for r in regs:
        verify(r)
    print("ALL OK for regions", regs)
