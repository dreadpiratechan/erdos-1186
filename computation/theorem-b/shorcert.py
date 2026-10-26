"""Erdos #1186 (side exploration): EXACT certificate for the PRS08 Sec. 3.2 semidefinite lower bound at larger L.
Takes the numerical dual diagonal d from shorlb.solve(L), rounds it UP to multiples of 1/Q (Q = 2^10), and proves in exact
integer arithmetic (fraction-free Bareiss elimination: A + D positive definite  <=>  all leading principal minors > 0)
that  A_L + diag(d) is positive definite.  Then, by PRS08 Lemma 3 + Lemma 1 (their argument is for every even L),
    V(n) >= (1/2)(3/8 - c) n^2 (1+o(1)),  c = 1/(4L) + 1/4 + (sum d)/(4 L^2).
Reproduction check: the same code at L = 128 must give a bound within 1e-5 of PRS08's 1675/32768 = 0.0511170...
usage: py shorcert.py L"""
import os, sys, time
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import shorlb

Q = 1 << 10

def bareiss_pd(Mint):
    """Mint: square symmetric integer matrix (object array). Returns (True, minors_min) iff all leading minors > 0."""
    M = Mint.copy()
    n = M.shape[0]
    prev = 1
    minmin = None
    for k in range(n):
        piv = M[k, k]
        if piv <= 0:
            return False, k
        if k < n - 1:
            col = M[k + 1:, k].copy(); row = M[k, k + 1:].copy()
            sub = M[k + 1:, k + 1:] * piv - np.outer(col, row)
            # exact division by the previous pivot
            M[k + 1:, k + 1:] = sub // prev
        prev = piv
    return True, n

def certify(L):
    t0 = time.time()
    A, S, d, lam = shorlb.solve(L)
    dn = np.ceil((d + 1e-6) * Q).astype(np.int64)          # d_i = dn_i / Q  (rounded up)
    Mint = (A.astype(np.int64) * Q + np.diag(dn)).astype(object)
    ok, info = bareiss_pd(Mint)
    sumd = Fraction(int(dn.sum()), Q)
    c = Fraction(1, 4 * L) + Fraction(1, 4) + sumd / (4 * L * L)
    bound = Fraction(1, 2) * (Fraction(3, 8) - c)
    print("L=%d: numeric SDP sum d = %.3f ; rounded-up exact sum d = %s (= %.3f); A+D positive definite (exact): %s ; bound V(n) >= %s n^2 = %.7f n^2   [%.0fs]"
          % (L, -S, sumd, float(sumd), ok, bound, float(bound), time.time() - t0), flush=True)
    return ok, bound, dn

if __name__ == "__main__":
    for L in map(int, sys.argv[1:]):
        ok, bound, dn = certify(L)
        if ok:
            np.save(os.path.join(HERE, "out", "dn_L%d.npy" % L), dn)
