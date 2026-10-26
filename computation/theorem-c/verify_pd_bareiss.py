"""Second, independent exact positive-definiteness check of the stored integer matrices N (lane excertsdp).

`verify_certs.py` certifies PSD via the Cholesky-dominance certificate (the check the Lean generator will mirror).  This script
does not use the Cholesky data at all: it runs fraction-free (Bareiss) elimination on N - ceil(D/2^k) I for the margin 2^-k stored in
the JSON and checks that ALL leading principal minors are > 0 (Sylvester's criterion), so N >= (D/2^k) I in the exact sense.
Pure Python integers, one process.   Usage: py -I verify_pd_bareiss.py [region ...]
"""
import io
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))


def leading_minors_positive(A):
    """Bareiss: returns (ok, k) where k = number of leading minors checked (all > 0 iff ok)."""
    n = len(A)
    M = [row[:] for row in A]
    prev = 1
    for k in range(n - 1):
        piv = M[k][k]
        if piv <= 0:
            return False, k
        for i in range(k + 1, n):
            Mi = M[i]
            Mk = M[k]
            f = Mi[k]
            for j in range(k + 1, n):
                Mi[j] = (Mi[j] * piv - f * Mk[j]) // prev
        prev = piv
    return M[n - 1][n - 1] > 0, n


def main(regs):
    for r in regs:
        t = time.time()
        d = json.load(io.open(os.path.join(HERE, "data", "cert_region%d.json" % r), encoding="utf-8"))
        N = d["N"]
        n = len(N)
        D = d["D"]
        k = d["margin"]["eta_pow2"]
        shift = -(-D // (1 << k))              # ceil(D / 2^k)
        A = [row[:] for row in N]
        for i in range(n):
            A[i][i] -= shift
        assert all(A[i][j] == A[j][i] for i in range(n) for j in range(n))
        ok, cnt = leading_minors_positive(A)
        print("[region %d] Bareiss: N - ceil(D/2^%d) I (%d x %d) all leading principal minors > 0: %s  (%.1fs)"
              % (r, k, n, n, ok, time.time() - t), flush=True)
        if not ok:
            print("  FAILED at step", cnt)
            sys.exit(1)
    print("BAREISS OK for regions", regs)


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]] or [1, 2, 3, 4, 5])
