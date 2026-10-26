"""Erdos #1186 night2 sdp1186c: SECOND independent exact positive-definiteness proof for a Shor + triangle certificate, scalable to L >= 1024.

Method (all comparisons in exact integer arithmetic, floats only to GUESS a matrix T):
  M = 2Q*(A + diag(d) - sum mu_t C_t) is an integer symmetric matrix (same construction as verify_tri.py, re-implemented here).
  Pick an upper-triangular integer matrix T with every diagonal entry nonzero (so T is invertible, exactly).
  Compute N = T^T M T EXACTLY (blocked 18-bit-limb products in float64 BLAS, every partial sum < 2^53, recombined with Python ints).
  If N is strictly diagonally dominant with positive diagonal (N_ii > sum_{j != i} |N_ij|), Gershgorin gives lambda_min(N) > 0,
  and x^T M x = y^T N y with y = T^{-1} x, so M is positive definite.
T is a guess: the float inverse of the Cholesky factor of M, column-scaled so that N is close to a diagonal matrix; up to 4 refinement rounds.
usage: py verify_dd.py CERT.json
Reuses nothing from tri.py / certify.py / verify_tri.py (only the cut sign table, restated below).  Prints PASS only if the exact check passes."""
import sys, json, time
from fractions import Fraction
import numpy as np
import scipy.linalg as sla

PAT = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
B = 18

def build_M(d):
    L, Q, dn, cuts = d["L"], d["Q"], np.array(d["dn"], dtype=np.int64), d["cuts"]
    i = np.arange(1, L + 1)[:, None]; j = np.arange(1, L + 1)[None, :]
    Bm = ((j + 1 <= 2 * i) & (2 * i <= j + L)).astype(np.int64)
    M = 2 * Q * (Bm + Bm.T)
    M[np.arange(L), np.arange(L)] += 2 * dn
    C = np.array(cuts, dtype=np.int64).reshape(-1, 5)
    sg = np.array(PAT, dtype=np.int64)[C[:, 3]]
    for (ca, cb, col) in ((0, 1, 0), (0, 2, 1), (1, 2, 2)):
        a = C[:, ca] - 1; b = C[:, cb] - 1
        np.add.at(M, (a, b), -C[:, 4] * sg[:, col]); np.add.at(M, (b, a), -C[:, 4] * sg[:, col])
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

def main(path):
    d = json.load(open(path)); L, Q = d["L"], d["Q"]
    t0 = time.time()
    M = build_M(d)
    S = Fraction(sum(d["dn"]) + sum(c[4] for c in d["cuts"]), Q)
    b = Fraction(1, 2) * (Fraction(3, 8) - Fraction(1, 4 * L) - Fraction(1, 4) - S / (4 * L * L))
    assert all(v >= 0 for v in d["dn"]) and all(c[4] >= 1 for c in d["cuts"])
    print("L=%d  cuts=%d  S=%s (%.6f)  bound %s = %.8f   (json: %s)" % (L, len(d["cuts"]), S, float(S), b, float(b), d["bound"]), flush=True)
    assert str(b) == d["bound"]
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
            print("PASS: 2Q*M is positive definite (T upper triangular, invertible; T^T M T strictly diagonally dominant, exact integers). L=%d, bound %.8f" % (L, float(b)))
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
    sys.exit(0 if main(sys.argv[1]) else 1)
