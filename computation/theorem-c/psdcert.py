"""Erdos 1186 exact lane (excertsdp): integer approximate-Cholesky + diagonal-dominance certificates of `N >= 0`.

For a symmetric integer matrix N (here N = D * S), a certificate is an integer scale T2 >= 1 and an integer lower
triangular C with E := T2 * N - C C^T (exact integers) DIAGONALLY DOMINANT: E_ii >= sum_{j != i} |E_ij|.  Then
E is PSD (Gershgorin / dominance), so T2 * N = C C^T + E is PSD, so N is PSD.  The float Cholesky used to propose C
is irrelevant to soundness: `check_dominance` re-verifies in exact integer arithmetic.  Own code.
"""
import numpy as np


def to_obj(M):
    return np.array([[int(x) for x in row] for row in M], dtype=object)


def exact_E(N, C, T2):
    """E = T2*N - C C^T with Python ints (numpy object arrays)."""
    n = len(N)
    Co = np.array(C, dtype=object)
    G = Co.dot(Co.T)
    return T2 * N - G


def check_dominance(E):
    """-> (ok, worst slack index, min slack)  where slack_i = E_ii - sum_{j != i} |E_ij|."""
    n = len(E)
    worst = None
    ok = True
    for i in range(n):
        s = E[i][i] - sum(abs(E[i][j]) for j in range(n) if j != i)
        if worst is None or s < worst[1]:
            worst = (i, s)
        if s < 0:
            ok = False
    return ok, worst


def float_matrix(N, D):
    n = len(N)
    return np.array([[N[i][j] / D for j in range(n)] for i in range(n)], dtype=float)


def propose_chol(N, D, shift_frac=0.5, T2=1, shift_abs=None):
    """Float Cholesky of (N/D - shift I), scaled by tau = sqrt(T2*D), rounded to integers (lower triangular)."""
    Sf = float_matrix(N, D)
    lam = np.linalg.eigvalsh(Sf)[0]
    shift = shift_abs if shift_abs is not None else shift_frac * lam
    L = np.linalg.cholesky(Sf - shift * np.eye(len(Sf)))
    tau = float(np.sqrt(float(T2) * float(D)))
    C = np.rint(L * tau)
    n = len(Sf)
    rows = [[int(C[i][j]) for j in range(i + 1)] for i in range(n)]
    return rows, lam


def full_C(rows):
    n = len(rows)
    return [[rows[i][j] if j <= i else 0 for j in range(n)] for i in range(n)]


def certify(N, D, T2_list=(1, 4, 16, 64, 256, 4096, 65536), shift_fracs=(0.5, 0.7, 0.3, 0.9)):
    """Try to find (T2, rows) with E diagonally dominant.  N: numpy object array of Python ints."""
    best = None
    for T2 in T2_list:
        for sf in shift_fracs:
            rows, lam = propose_chol(N, D, sf, T2)
            E = exact_E(N, full_C(rows), T2)
            ok, worst = check_dominance(E)
            if best is None or worst[1] > best[0]:
                best = (worst[1], T2, sf)
            if ok:
                return {"T2": T2, "rows": rows, "shift_frac": sf, "lam_min_float": float(lam),
                        "min_slack": int(worst[1])}
    raise RuntimeError("no dominance certificate found; best (min slack, T2, shift) = %r" % (best,))


def margin_lower_bound(N, D, etas=None):
    """Largest eta in a geometric ladder with a dominance certificate for N - round(eta*D) I  (so S >= eta I exactly,
    up to the ceil).  Returns (eta_rational_as_(num, den), certificate)."""
    n = len(N)
    best = None
    # ladder of eta = 2^-k
    for k in range(10, 40):
        shift = (D + (1 << k) - 1) >> k          # ceil(D / 2^k): N - shift*I with shift/D >= 2^-k
        N2 = N.copy()
        for i in range(n):
            N2[i][i] = N2[i][i] - shift
        try:
            cert = certify(N2, D, T2_list=(1, 16, 256, 4096), shift_fracs=(0.5, 0.8))
        except Exception:
            continue
        return (shift, D), k, cert
    return None
