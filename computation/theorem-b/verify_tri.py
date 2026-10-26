"""Erdos #1186 night2 sdp1186c: INDEPENDENT exact check of a Shor + triangle-cut certificate (data/sdp_tri_L*.json).

Shares no code with tri.py / certify.py.  Pure Python integers / Fractions for everything that matters:
 (1) every d_i = dn_i/Q >= 0 and every multiplier mn_t >= 1 (cuts are listed with i<j<k, 1-indexed, pattern p);
 (2) the 4 patterns have sign products +1 and each cut  s1 x_i x_j + s2 x_i x_k + s3 x_j x_k + 1 >= 0  holds at all 8 vertices of {-1,1}^3
     (it is multilinear in x, so it then holds on the whole cube [-1,1]^3: its minimum over a cube is at a vertex);
 (3) the integer matrix N = 2Q*(A + diag(dn/Q) - sum_t (mn_t/Q) C_t) is positive definite: Bareiss, all leading principal minors > 0;
 (4) S = sum d + sum mu and the PRS08 constant  b = (1/2)(3/8 - 1/(4L) - 1/4 - S/(4L^2)).
Then  x^T A x >= -S  on [-1,1]^L, hence V(n) >= b n^2 (1+o(1)) by PRS08 Lemmas 1-3 (see CUTS.md).
Float sanity (not part of the proof): q(x) + S >= 0 on random vertices/cube points and 1-flip local minima.
usage: py verify_tri.py data/sdp_tri_L128.json [--skip-pd]"""
import sys, json, itertools, random, time
from fractions import Fraction

PAT = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]

def Aij(L, i, j):
    b = lambda a, c: 1 if (c + 1 <= 2 * a <= c + L) else 0
    return b(i, j) + b(j, i)

def main(path, skip_pd=False):
    d = json.load(open(path))
    L, Q, dn, cuts = d["L"], d["Q"], d["dn"], d["cuts"]
    assert len(dn) == L and all(v >= 0 for v in dn)
    seen = set()
    for (i, j, k, p, m) in cuts:
        assert 1 <= i < j < k <= L and 0 <= p < 4 and m >= 1 and (i, j, k, p) not in seen
        seen.add((i, j, k, p))
    for s in PAT:
        assert s[0] * s[1] * s[2] == 1
        for xs in itertools.product((-1, 1), repeat=3):
            assert s[0] * xs[0] * xs[1] + s[1] * xs[0] * xs[2] + s[2] * xs[1] * xs[2] + 1 >= 0
    print("(1)(2) ok: %d cuts, all multipliers positive, d >= 0, cut validity at all vertices" % len(cuts))
    # integer matrix N = 2Q*A + 2 diag(dn) - sum mn * sigma at (a,b),(b,a)
    N = [[2 * Q * Aij(L, i, j) for j in range(1, L + 1)] for i in range(1, L + 1)]
    for i in range(L): N[i][i] += 2 * dn[i]
    for (i, j, k, p, m) in cuts:
        s = PAT[p]
        for (a, b, sg) in ((i, j, s[0]), (i, k, s[1]), (j, k, s[2])):
            N[a - 1][b - 1] -= m * sg; N[b - 1][a - 1] -= m * sg
    assert all(N[a][b] == N[b][a] for a in range(L) for b in range(L))
    S = Fraction(sum(dn) + sum(c[4] for c in cuts), Q)
    c = Fraction(1, 4 * L) + Fraction(1, 4) + S / (4 * L * L)
    b = Fraction(1, 2) * (Fraction(3, 8) - c)
    print("(4) S = %s = %.6f ; bound V(n) >= %s n^2 = %.8f n^2   (json says %s)" % (S, float(S), b, float(b), d["bound"]))
    assert str(b) == d["bound"] and str(S) == d["S"]
    if not skip_pd:
        t0 = time.time()
        prev = 1
        for k in range(L):
            piv = N[k][k]
            if piv <= 0: raise SystemExit("NOT PD: pivot %d = %s" % (k, piv))
            rk = N[k]
            for r in range(k + 1, L):
                f = N[r][k]; rr = N[r]
                if f == 0 and prev == 1:
                    for c2 in range(k + 1, L): rr[c2] = rr[c2] * piv // prev
                else:
                    for c2 in range(k + 1, L): rr[c2] = (rr[c2] * piv - f * rk[c2]) // prev
            prev = piv
        print("(3) Bareiss: all %d leading principal minors > 0 -> 2Q*M positive definite (%.1fs)" % (L, time.time() - t0))
    # float sanity of the final inequality on cube points
    rnd = random.Random(1)
    A = [[Aij(L, i, j) for j in range(1, L + 1)] for i in range(1, L + 1)]
    Sf = float(S)
    worst = 1e18
    for t in range(300):
        x = [rnd.choice((-1.0, 1.0)) if t % 3 else rnd.uniform(-1, 1) for _ in range(L)]
        for _ in range(60 if t % 2 else 0):     # a few greedy coordinate descent sweeps (cube min per coordinate)
            for i in range(L):
                s_i = sum(A[i][j] * x[j] for j in range(L) if j != i)
                x[i] = max(-1.0, min(1.0, -s_i / (2.0 * A[i][i])))
        q = sum(A[i][j] * x[i] * x[j] for i in range(L) for j in range(L))
        worst = min(worst, q + Sf)
    print("float sanity: min over tested cube points of q(x) + S = %.4f (must be >= 0)" % worst)
    assert worst >= -1e-6

if __name__ == "__main__":
    main(sys.argv[1], "--skip-pd" in sys.argv)
