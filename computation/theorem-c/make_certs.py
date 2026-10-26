"""Erdos 1186 exact lane (excertsdp): build the five region certificates (B' = 0, S PSD with a margin) -> data/cert_region{r}.json.

Starting data: reviewer rev1186c's exact certificates (`data/certs_rev1186c.json`, theta / mu / B, built by that reviewer
from the claim's text with its own code).  What this script adds (own code):
  * slabs 2-5: B' = 0 (the reviewers' constant B > 0 moves into S_00), and MARGIN by raising the multipliers of the box
    forms y_i (1 - y_i) by eps_i >= 0:  S_new = S_rev + sum_i eps_i (e_i - e_0/2)(e_i - e_0/2)^T + (B - sum_i eps_i / 4) e_0 e_0^T,
    which is PSD with margin as soon as S_rev is PSD and sum eps_i < 4 B.  (S_rev's own smallest eigenvalue is ~1e-12.)
  * all multipliers and thetas rounded to dyadic rationals (multiples of 2^-K, mu rounded DOWN, theta to nearest, in [0, 1]).
  * region 1 (inner, m <= 1/5): theta in {0, 1}, mu from Lam / Nu / N rounded down, the linear multipliers c_i are DERIVED
    exactly so that the constant row of S is zero; S = P on the y-block.
  * integer N = D * S (exact), an integer approximate Cholesky + dominance certificate, and a certified margin.
Everything produced here is re-checked by verify_certs.py (a separate script).
Usage: py -I make_certs.py [region ...]     (default: 2 3 4 5 1)
"""
import io
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json
import math
import sys
import time
from fractions import Fraction as Fr

import numpy as np

import import_rev as IR
import psdcert as P
import sdpmodel as M

K = 40
Q = 1 << K
Z0 = 360364800                    # = 2^8 * 3 * 5^2 * 137^2 : common denominator of all fixed data (a_i, b_i, w, A4, lo, hi)
D = Q * Z0


def fr_str(x):
    x = Fr(x)
    return "%d/%d" % (x.numerator, x.denominator) if x.denominator != 1 else str(x.numerator)


def S_to_int(S, D):
    """Sym -> integer numpy object matrix N = D*S (asserting integrality)."""
    n1 = S.n + 1
    N = np.zeros((n1, n1), dtype=object)
    for i in range(n1):
        for j in range(n1):
            N[i][j] = 0
    for (a, b), v in S.d.items():
        x = Fr(v) * D
        assert x.denominator == 1, ("not integral", a, b, v)
        N[a][b] += int(x)
        if a != b:
            N[b][a] += int(x)
    return N


def frac_theta(theta_num):
    return {k: Fr(v, Q) for k, v in theta_num.items()}


def assemble(G, R, theta_num, mu_num, mu_den):
    """-> Sym for  L_theta - sum_f mu_f f  (B' = 0)."""
    theta = frac_theta(theta_num)
    forms_mu = [(list(k), Fr(v, mu_den)) for k, v in mu_num.items() if v != 0]
    return M.build_S(G, R, theta, forms_mu, Bp=Fr(0))


def float_S(S):
    return np.array(S.full_matrix(1), dtype=float)


def slab_certificate(region, eps_scale=0.5):
    gname, B, theta_rev, forms_rev = IR.load_rev(region)
    R = M.REGIONS[region]
    G = M.load_grid(R[0])
    n = G.N
    theta_num = {}
    for k, th in theta_rev.items():
        v = int(round(th * Q))
        theta_num[k] = min(max(v, 0), Q)
    mu_num = {}
    for f, mu in forms_rev:
        M.check_form_valid(G, f)
        key = tuple(f)
        assert key not in mu_num, key
        assert mu >= 0
        v = (mu * Q).__floor__()
        if v:
            mu_num[key] = v
    # margin: box forms yo(i,i)
    base = assemble(G, R, theta_num, mu_num, Q)
    Sb = float_S(base)
    eps_total = eps_scale * 4 * float(B)
    eps = int(eps_total / n * Q)
    for i in range(n):
        key = ("yo", i, i)
        mu_num[key] = mu_num.get(key, 0) + eps
    S = assemble(G, R, theta_num, mu_num, Q)
    return G, R, theta_num, mu_num, Q, S, {"B_rev": fr_str(B), "eps_each_num": eps, "eps_scale": eps_scale}


def inner_certificate():
    c = json.load(io.open(M.EXACT / "data" / "certs_rev1186c.json", encoding="utf-8"))["inner"]
    R = M.REGIONS[1]
    G = M.load_grid(R[0])
    n = G.N
    assert c["pts"] == G.pts
    theta_num = {}
    for (i, j) in G.cuts():
        theta_num[(i, j)] = Q if G.sgn[i] * G.sgn[j] == 1 else 0
    mu_num = {}
    Lam = [[Fr(x) for x in row] for row in c["Lam"]]
    for i in range(n):
        for j in range(n):
            if Lam[i][j] != 0:
                v = (Lam[i][j] * Q).__floor__()
                if v:
                    mu_num[("yo", i, j)] = v
    for j, x in enumerate(c["Nu"]):
        v = (Fr(x) * Q).__floor__()
        if v:
            mu_num[("yhm", j)] = v
    for (a, b), x in c["N"]:
        v = (Fr(x) * Q).__floor__()
        if v:
            mu_num[("yy", a, b)] = v
    # derived exact c_i: build S without c, read the constant row, c_i = 2 S_0i
    S0 = assemble(G, R, theta_num, mu_num, Q)
    assert S0.d.get((0, 0), 0) == 0
    cvals = []
    for i in range(n):
        s0i = S0.d.get((0, i + 1), Fr(0))
        ci = 2 * s0i
        assert ci >= 0, ("negative c_i", i, ci)
        cvals.append(ci)
    # c_i over the common denominator D (exact): store numerators over `mu_den`
    mu_den = D
    mu_over_D = {k: v * Z0 for k, v in mu_num.items()}
    for i, ci in enumerate(cvals):
        if ci != 0:
            x = ci * D
            assert x.denominator == 1
            mu_over_D[("y", i)] = int(x)
    S = assemble(G, R, theta_num, mu_over_D, mu_den)
    return G, R, theta_num, mu_over_D, mu_den, S, {}


def build_region(region, **kw):
    t = time.time()
    if region == 1:
        G, R, theta_num, mu_num, mu_den, S, extra = inner_certificate()
        n = G.N
        Nfull = S_to_int(S, D)
        assert all(Nfull[0][j] == 0 for j in range(n + 1))
        Ny = Nfull[1:, 1:].copy()
        Nuse = Ny
        const_row_zero = True
    else:
        G, R, theta_num, mu_num, mu_den, S, extra = slab_certificate(region, **kw)
        Nfull = S_to_int(S, D)
        Nuse = Nfull
        const_row_zero = False
    Sf = P.float_matrix(Nuse, D)
    ev = np.linalg.eigvalsh(Sf)
    print("region", region, "float eig min %.4e max %.4e" % (ev[0], ev[-1]), "(%.1fs)" % (time.time() - t), flush=True)
    assert ev[0] > 0
    cert = P.certify(Nuse, D)
    print("  chol cert T2=%d min slack %d (%.1fs)" % (cert["T2"], cert["min_slack"], time.time() - t), flush=True)
    mar = P.margin_lower_bound(Nuse, D)
    (shift, den), kk, mcert = mar
    print("  exact margin: S >= 2^-%d I  (%.3e) (%.1fs)" % (kk, 2.0 ** -kk, time.time() - t), flush=True)
    out = {
        "format": "excertsdp-v1",
        "header": "Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the "
                  "mathematics is its author's.  Data lane excertsdp (agent/n3d); starting multipliers from reviewer rev1186c.",
        "region": region, "grid": R[0], "lo": fr_str(R[1]), "hi": fr_str(R[2]), "n": G.N,
        "K": K, "theta_den": Q, "mu_den": mu_den, "bprime": "0",
        "cuts": [[i, j, theta_num[(i, j)]] for (i, j) in G.cuts()],
        "forms": [list(k) + [v] for k, v in sorted(mu_num.items())],
        "D": D, "Z0": Z0,
        "const_row_zero": const_row_zero,
        "N": [[int(x) for x in row] for row in Nuse],
        "chol": {"T2": cert["T2"], "rows": cert["rows"], "min_slack": cert["min_slack"]},
        "margin": {"lambda_min_float": float(ev[0]), "lambda_max_float": float(ev[-1]), "eta_pow2": kk,
                   "eta_note": "S >= 2^-eta_pow2 * I, certified by dominance on N - ceil(D/2^k) I", "extra": extra},
    }
    return out, G, R


if __name__ == "__main__":
    regs = [int(a) for a in sys.argv[1:]] or [2, 3, 4, 5, 1]
    for r in regs:
        out, G, R = build_region(r)
        p = M.EXACT / "data" / ("cert_region%d.json" % r)
        io.open(p, "w", encoding="utf-8").write(json.dumps(out, separators=(",", ":")))
        print("  wrote", p, "%.0f KB" % (p.stat().st_size / 1024), flush=True)
