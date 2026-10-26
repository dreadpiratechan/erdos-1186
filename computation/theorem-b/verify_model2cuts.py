"""Erdos #1186 night2 (sdp1186m): independent exact check of a MODEL-2 Shor + triangle-cut certificate data/sdp_model2cuts_L{L}.json.
usage: py verify_model2cuts.py L [--brute] [--skip-pd]        (shares no code with n2/sdp1186m/{tri2,cert_cuts2,kern}.py)
Model 2 (MODEL2.md): for even L, w and n = L w every 2-colouring of [n] has
      4 monoCount >= floor((n-1)^2/4) + w^2 F(x) - 2 L w - 3n/2 ,   F(x) = x^T C x - L ,   C = S + I + J/4 ,   S = (K + K^T)/2,
K = exact cell-area kernel of R_n (m = 2q-p-1: 1 for 1<=m<=L-2, 3/4 for m in {0,L-1}, 1/4 for m in {-1,L}, else 0); 8C = K4 + K4^T + 8 I + 2 J (integers, K4 = 4K).
Certificate: dn_p >= 0 (d = dn/Q) and triangle cuts (i<j<k 1-indexed, pattern p, mn >= 1) with
      N = 2Q (8C) + 16 diag(dn) - 8 sum_t mn_t sigma_t(at the six symmetric off-diagonal entries)   positive definite (Bareiss, all leading minors > 0).
Then x^T C x >= -(sum d + sum mu) =: -S on [-1,1]^L, F >= -(L+S) and  delta_3 >= 1/16 - (L + S)/(4 L^2)."""
import sys, json, os, itertools, time
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
PAT = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]

def kernel4(L):
    p = np.arange(1, L + 1)[:, None]; q = np.arange(1, L + 1)[None, :]
    m = 2 * q - p - 1
    K4 = np.zeros((L, L), np.int64)
    K4[(m >= 1) & (m <= L - 2)] = 4
    K4[(m == 0) | (m == L - 1)] = 3
    K4[(m == -1) | (m == L)] = 1
    return K4

def brute_cells(L, w):
    n = L * w
    a = np.arange(1, n + 1)[:, None]; b = np.arange(1, n + 1)[None, :]
    R = ((2 * b - a >= 1) & (2 * b - a <= n))
    return R.reshape(L, w, L, w).sum((1, 3))

def main(L, brute, skip_pd):
    d = json.load(open(os.path.join(HERE, "data", "sdp_model2cuts_L%d.json" % L)))
    assert d["L"] == L and L % 2 == 0 and L >= 4
    Q, dn, cuts = d["Q"], d["dn"], d["cuts"]
    assert len(dn) == L and all(v >= 0 for v in dn)
    K4 = kernel4(L)
    for w in ([2, 4, 6] if brute else [2, 4]):
        assert np.array_equal(4 * brute_cells(L, w), K4 * w * w), "kernel formula != brute-force cell counts at w=%d" % w
    print("(0) closed-form kernel == brute-force cell counts of R_n (w = 2,4%s)" % (",6" if brute else ""))
    seen = set()
    for (i, j, k, p, m) in cuts:
        assert 1 <= i < j < k <= L and 0 <= p < 4 and m >= 1 and (i, j, k, p) not in seen
        seen.add((i, j, k, p))
    for s in PAT:
        assert s[0] * s[1] * s[2] == 1
        for xs in itertools.product((-1, 1), repeat=3):          # multilinear in x: validity at the 8 vertices => on the whole cube
            assert s[0] * xs[0] * xs[1] + s[1] * xs[0] * xs[2] + s[2] * xs[1] * xs[2] + 1 >= 0
    print("(1)(2) ok: %d cuts, distinct, multipliers >= 1/Q, d >= 0, each pattern product +1 and valid at all 8 cube vertices" % len(cuts))
    N = 2 * Q * (K4 + K4.T + 8 * np.eye(L, dtype=np.int64) + 2 * np.ones((L, L), np.int64))
    N[np.arange(L), np.arange(L)] += 16 * np.array(dn, dtype=np.int64)
    N = N.astype(object)
    for (i, j, k, p, m) in cuts:
        s = PAT[p]
        for (a, b, sg) in ((i, j, s[0]), (i, k, s[1]), (j, k, s[2])):
            N[a - 1, b - 1] -= 8 * m * sg; N[b - 1, a - 1] -= 8 * m * sg
    assert all(N[a, b] == N[b, a] for a in range(L) for b in range(a))
    S = Fraction(sum(dn) + sum(c[4] for c in cuts), Q)
    bound = Fraction(1, 16) - (L + S) / (4 * L * L)
    print("(4) S = %s = %.4f ; delta_3 >= %s = %.7f   (file says %s)" % (S, float(S), bound, float(bound), d["bound"]))
    assert str(bound) == d["bound"] and str(S) == d["S"]
    if not skip_pd:
        t0 = time.time(); prev = 1; M = N.copy()
        for k in range(L):
            piv = M[k, k]
            if piv <= 0: raise SystemExit("NOT PD: pivot %d = %s" % (k, piv))
            if k < L - 1:
                col = M[k + 1:, k].copy(); row = M[k, k + 1:].copy()
                M[k + 1:, k + 1:] = (M[k + 1:, k + 1:] * piv - np.outer(col, row)) // prev
            prev = piv
        print("(3) Bareiss: all %d leading principal minors > 0 -> N positive definite (%.1fs)" % (L, time.time() - t0))
    # float sanity (NOT part of the proof): F(x) + L + S >= 0 at random cube points after greedy descent
    C = (K4 + K4.T) / 8.0 + np.eye(L) + 0.25 * np.ones((L, L))
    rng = np.random.default_rng(1); worst = 1e18
    for t in range(60):
        x = rng.choice([-1.0, 1.0], L) if t % 2 else rng.uniform(-1, 1, L)
        for _ in range(40):
            for p in range(L):
                g = C[p] @ x - C[p, p] * x[p]
                x[p] = max(-1.0, min(1.0, -g / C[p, p]))
        worst = min(worst, x @ C @ x + float(S))
    print("float sanity: min over 60 greedy-descent cube points of x^T C x + S = %.4f (must be >= 0)" % worst)
    assert worst >= -1e-6

if __name__ == "__main__":
    main(int(sys.argv[1]), "--brute" in sys.argv, "--skip-pd" in sys.argv)
