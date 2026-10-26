"""Erdos #1186 (side result): re-check the saved PRS08-method certificates data/sdp_dn_L{L}.json.
Checks (1) all d_i > 0 (needed in PRS08 Lemma 3: x^T A x >= -sum d_i x_i^2 >= -sum d_i for |x_i| <= 1);
(2) A_L + diag(d) positive definite - float64 eigenvalue margin (independent of the exact route) and, with --exact, exact
fraction-free Bareiss elimination over the integers (all leading principal minors > 0; L=256 ~ 1.5 min, L=512 ~ 12 min);
(3) prints the exact lower bound V(n) >= (1/2)(3/8 - c) n^2 (1+o(1)), c = 1/(4L) + 1/4 + sum(d)/(4 L^2).
A_ij = B_ij + B_ji, B_ij = 1 iff j+1 <= 2i <= j+L  (PRS08 Section 3.2, any even L).   usage: py verify_sdp.py L [--exact]"""
import json, os, sys
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)

def amat(L):
    B = np.zeros((L, L), np.int64)
    for i in range(1, L + 1):
        for j in range(1, L + 1):
            if j + 1 <= 2 * i <= j + L:
                B[i - 1, j - 1] = 1
    return B + B.T

def main(L, exact):
    d = json.load(open(os.path.join(HERE, "data", "sdp_dn_L%d.json" % L)))
    assert d["L"] == L
    Q = d["Q"]; dn = np.array(d["dn"], dtype=np.int64); assert len(dn) == L and dn.min() > 0
    A = amat(L)
    lam = np.linalg.eigvalsh(A.astype(float) + np.diag(dn / Q)).min()
    print("L=%d: all d_i > 0 (min %.4f); float64 min eigenvalue of A+D = %.3e (float error ~ %.1e) -> %s" % (
        L, dn.min() / Q, lam, L * 2.2e-16 * 4 * L, "PD with margin" if lam > 1e-6 else "NOT CLEARLY PD"))
    if exact:
        from shorcert import bareiss_pd
        ok, _ = bareiss_pd((A * Q + np.diag(dn)).astype(object))
        print("exact Bareiss: A+D positive definite =", ok)
        assert ok
    S = Fraction(int(dn.sum()), Q)
    c = Fraction(1, 4 * L) + Fraction(1, 4) + S / (4 * L * L)
    b = Fraction(1, 2) * (Fraction(3, 8) - c)
    print("sum d = %s;  c = %s;  V(n) >= %s n^2 = %.7f n^2  (PRS08 L=128: 1675/32768 = %.7f)" % (S, c, b, float(b), 1675 / 32768))

if __name__ == "__main__":
    main(int(sys.argv[1]), "--exact" in sys.argv)
