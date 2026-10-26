"""Erdos #1186 night2 (sdp1186m): independent re-check of the MODEL2 diagonal certificates data/sdp_model2_L{L}.json.   usage: py verify_model2.py L [--exact] [--brute]
Model 2 (problems/1186/MODEL2.md, Theorem 1):  for L, w even and n = L w, every 2-colouring of [n] satisfies
      4 monoCount >= floor((n-1)^2/4) + w^2 F(x) - 2 L w - 3n/2 ,   F(x) = x^T S x - sum_p (1 - x_p^2) + (1/4)(sum_p x_p)^2 ,
x_p = mean of the +-1 colour over the p-th block of w integers, S = (K + K^T)/2, K = exact cell-area kernel of R_n = {(a,b) in [n]^2 : 1 <= 2b-a <= n}:
      m = 2q - p - 1 :  K_pq = 1 (1 <= m <= L-2) ; 3/4 (m in {0, L-1}) ; 1/4 (m in {-1, L}) ; 0 otherwise.
Certificate: integers en_p >= 0 with  Q*(K4 + K4^T + 8 I + 2 J) + diag(en)  positive definite (exact Bareiss), K4 = 4K.  Then F(x) >= -(L + sum e), e = en/(8Q),
and delta_3 >= 1/16 - (L + sum e)/(4 L^2).
Checks: (1) the closed-form kernel against brute-force cell counts of R_n for w = 2, 4 (--brute also w = 6); (2) en >= 0; (3) Bareiss (--exact; otherwise float eigenvalues);
(4) the exact bound as a Fraction."""
import json, os, sys
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))

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

def bareiss_pd(M):
    M = M.copy(); n = M.shape[0]; prev = 1
    for k in range(n):
        piv = M[k, k]
        if piv <= 0: return False, k
        if k < n - 1:
            col = M[k + 1:, k].copy(); row = M[k, k + 1:].copy()
            M[k + 1:, k + 1:] = (M[k + 1:, k + 1:] * piv - np.outer(col, row)) // prev
        prev = piv
    return True, n

def main(L, exact, brute):
    d = json.load(open(os.path.join(HERE, "data", "sdp_model2_L%d.json" % L)))
    assert d["L"] == L and L % 2 == 0
    Q = d["Q"]; en = np.array(d["en"], dtype=np.int64); assert len(en) == L and en.min() >= 0
    K4 = kernel4(L)
    for w in ([2, 4, 6] if brute else [2, 4]):
        assert np.array_equal(4 * brute_cells(L, w), K4 * w * w), "kernel formula disagrees with brute-force cell counts at w=%d" % w
    print("L=%d: closed-form kernel == brute-force cell counts of R_n for w in %s; en >= 0 (min %d)" % (L, [2, 4, 6] if brute else [2, 4], en.min()))
    A = K4 + K4.T + 8 * np.eye(L, dtype=np.int64) + 2 * np.ones((L, L), dtype=np.int64)
    lam = np.linalg.eigvalsh(A / 8.0 + np.diag(en / (8.0 * Q)))[0]
    print("float64 min eigenvalue of C + diag(e) = %.3e" % lam)
    if exact:
        ok, _ = bareiss_pd((A * Q + np.diag(en)).astype(object))
        print("exact Bareiss: Q*(8C) + diag(en) positive definite =", ok)
        assert ok
    Se = Fraction(int(en.sum()), 8 * Q)
    bound = Fraction(1, 16) - (L + Se) / (4 * L * L)
    print("sum e = %s (%.4f);  delta_3 >= %s = %.7f   (file says %s)" % (Se, float(Se), bound, float(bound), d["bound"]))
    assert "%d/%d" % (bound.numerator, bound.denominator) == d["bound"]
    print("(PRS08 published 1675/32768 = %.7f; repo PRS-method certificate L=512: 0.0518729)" % (1675 / 32768))

if __name__ == "__main__":
    main(int(sys.argv[1]), "--exact" in sys.argv, "--brute" in sys.argv)
