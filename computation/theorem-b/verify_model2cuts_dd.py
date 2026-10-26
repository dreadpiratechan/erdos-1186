"""Erdos #1186 night2 (sdp1186m): memory-light exact positive-definiteness proof (diagonal dominance after an integer congruence) for the MODEL-2 cut certificates
data/sdp_model2cuts_L*.json, for L where Bareiss on object arrays is too heavy (L >= 512).
COPIED from problems/1186/n2/sdp1186c/verify_dd.py (branch agent/n2s1, agent sdp1186c) with only build_M() and the bound formula changed to the MODEL-2 matrix
   N = 2Q (K4 + K4^T + 8 I + 2 J) + 16 diag(dn) - 8 sum_t mn_t sigma_t   (see verify_model2cuts.py),   bound = 1/16 - (L + S)/(4 L^2).
Method (exact integers; floats only guess T): T upper triangular integer with nonzero diagonal; N' = T^T N T computed exactly; if N' is strictly diagonally dominant
with positive diagonal then N' is PD (Gershgorin) and so is N (congruence by an invertible T).   usage: py verify_model2cuts_dd.py L"""
import sys, json, time, os
from fractions import Fraction
import numpy as np
import scipy.linalg as sla

PAT = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
B = 18

def build_M(d):
    L, Q, dn, cuts = d["L"], d["Q"], np.array(d["dn"], dtype=np.int64), d["cuts"]
    p = np.arange(1, L + 1)[:, None]; q = np.arange(1, L + 1)[None, :]
    m = 2 * q - p - 1
    K4 = np.zeros((L, L), np.int64)
    K4[(m >= 1) & (m <= L - 2)] = 4
    K4[(m == 0) | (m == L - 1)] = 3
    K4[(m == -1) | (m == L)] = 1
    M = 2 * Q * (K4 + K4.T + 8 * np.eye(L, dtype=np.int64) + 2 * np.ones((L, L), np.int64))
    M[np.arange(L), np.arange(L)] += 16 * dn
    C = np.array(cuts, dtype=np.int64).reshape(-1, 5)
    sg = np.array(PAT, dtype=np.int64)[C[:, 3]]
    for (ca, cb, col) in ((0, 1, 0), (0, 2, 1), (1, 2, 2)):
        a = C[:, ca] - 1; b = C[:, cb] - 1
        np.add.at(M, (a, b), -8 * C[:, 4] * sg[:, col]); np.add.at(M, (b, a), -8 * C[:, 4] * sg[:, col])
    assert (M == M.T).all()
    return M

def limbs(X, k):
    """Split an integer array (int64 or object) into k signed limbs base 2^B:  X = sum limb_a * 2^(B a),  |limb| < 2^B, sign of X."""
    if X.dtype == object:
        sgn = np.sign(X).astype(np.int64)
        ab = np.abs(X)
        out = []
        mask = (1 << B) - 1
        for a in range(k):
            out.append(((ab & mask).astype(np.int64) * sgn).astype(np.float64)); ab = ab >> B
        assert not (ab != 0).any(), "limb overflow"
        return out
    sgn = np.sign(X); ab = np.abs(X); out = []
    mask = (1 << B) - 1
    for a in range(k):
        out.append(((ab & mask) * sgn).astype(np.float64)); ab = ab >> B
    assert not (ab != 0).any()
    return out

def nlimbs(X):
    m = int(np.max(np.abs(X))) if X.dtype != object else max(abs(int(v)) for v in X.ravel())
    return max(1, -(-m.bit_length() // B))

def exact_matmul(X, Y):
    """Exact integer product X @ Y (X, Y int64 or object arrays); returns an object array."""
    kx, ky = nlimbs(X), nlimbs(Y)
    n = X.shape[1]
    assert n * 2 ** (2 * B) < 2 ** 53 / (kx + ky + 1), "limb partial sums could exceed 2^53"
    Lx = limbs(X, kx); Ly = limbs(Y, ky)
    groups = {}
    for a in range(kx):
        for b in range(ky):
            P = Lx[a] @ Ly[b]
            Pi = np.rint(P).astype(np.int64)
            assert np.abs(P - Pi).max() == 0.0 and np.abs(Pi).max() < 2 ** 53
            groups[a + b] = groups.get(a + b, 0) + Pi
    out = np.zeros(X.shape[:1] + Y.shape[1:], dtype=object)
    for s, G in groups.items():
        out = out + (G.astype(object) << (B * s)) if s else out + G.astype(object)
    return out

def try_T(M, Tf, p):
    """Round Tf (float, upper triangular) * 2^p to integers; return exact N = T^T M T and diagonal dominance margin info."""
    Ti = np.rint(Tf * 2.0 ** p)
    assert np.abs(Ti).max() < 2 ** 62
    Ti = np.triu(Ti.astype(np.int64))
    assert (np.diag(Ti) != 0).all(), "T singular"
    MT = exact_matmul(M, Ti)
    N = exact_matmul(Ti.T.copy(), MT)
    return Ti, N

def dd_ok(N):
    L = N.shape[0]
    diag = np.array([N[i, i] for i in range(L)], dtype=object)
    absN = np.abs(N)
    off = absN.sum(axis=1) - np.abs(diag)
    marg = diag - off
    return bool((diag > 0).all() and (marg > 0).all()), marg, diag

def main(L0):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "sdp_model2cuts_L%d.json" % L0)
    d = json.load(open(path)); L, Q = d["L"], d["Q"]
    assert L == L0 and L % 2 == 0
    t0 = time.time()
    M = build_M(d)
    S = Fraction(sum(d["dn"]) + sum(c[4] for c in d["cuts"]), Q)
    b = Fraction(1, 16) - (L + S) / (4 * L * L)
    assert all(v >= 0 for v in d["dn"]) and all(c[4] >= 1 for c in d["cuts"])
    print("L=%d  cuts=%d  S=%s (%.6f)  bound %s = %.8f   (json: %s)" % (L, len(d["cuts"]), S, float(S), b, float(b), d["bound"]), flush=True)
    assert str(b) == d["bound"] and str(S) == d["S"]
    Mf = M.astype(np.float64)
    R = sla.cholesky(Mf, lower=False)             # M ~ R^T R
    T = sla.solve_triangular(R, np.eye(L), lower=False)   # R^{-1}
    p = 30
    Tcur = T.copy()
    for rnd in range(5):
        # column scaling so that N_ii ~ 1 (power of two scaling keeps it simple)
        Ti, N = try_T(M, Tcur, p)
        ok, marg, diag = dd_ok(N)
        nd = np.array([float(x) for x in diag])
        offmax = max(float(abs(x)) for x in (np.abs(N).sum(axis=1) - np.abs(np.array(diag, dtype=object))))
        print("  round %d: N exact computed (%.1fs); min diag = %.3e; max offdiag-row-sum / diag = %.3e ; strictly diagonally dominant: %s" % (
            rnd, time.time() - t0, nd.min(), offmax / nd.min() if nd.min() > 0 else float('nan'), ok), flush=True)
        if ok:
            assert (N == N.T).all()
            print("PASS: the MODEL-2 integer matrix N is positive definite (T upper triangular, invertible; T^T M T strictly diagonally dominant, exact integers). L=%d, bound %.8f" % (L, float(b)))
            return True
        # refine: Cholesky of N (float, normalised) gives a correction
        Nf = np.array([[float(N[i, j]) for j in range(L)] for i in range(L)])
        sc = 1.0 / np.sqrt(np.abs(np.diag(Nf)))
        Nn = Nf * sc[:, None] * sc[None, :]
        try:
            R2 = sla.cholesky(Nn, lower=False)
        except Exception as e:
            print("  float Cholesky of N failed:", e); return False
        T2 = sla.solve_triangular(R2, np.eye(L), lower=False)
        Tcur = (Ti.astype(np.float64) / 2.0 ** p) @ (np.diag(sc) @ T2)
        Tcur = np.triu(Tcur)
    print("FAIL: no exact diagonal-dominance certificate found within 5 rounds (this does NOT mean M is not PD)")
    return False

if __name__ == "__main__":
    sys.exit(0 if main(int(sys.argv[1])) else 1)
