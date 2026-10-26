"""Erdos 1186 exstar lane: numerical sanity checks for lean/Erdos/Proofs/P1186ExStar.lean (evidence, not proof).

1. T = sum_{p,q in [1,548]} K4(548,p,q) sg(c1 p) sg(c1 q) = -43840, by the direct double sum and by the 274-term form
   (column sums of K4 via prefix sums: Lean `KS_lo`, `KS_hi`, `starT`).
2. Wm(sstar w)(1096 w) = -43840 w^2 for w = 1..W (Wm s n = sum_y s_y (pre(y + D) - pre(y - D - 1)), D = min(y - 1, n - y)),
   against the Lean bound  -43840 w^2 - 1096 w - 2192 <= Wm.
c1 is the PRS 12-block colouring of [1, 548] (blocks 28,6,28,37,59,116,116,59,37,28,6,28), `sstar w x = sg c1 (ceil(x / 2w))`.

Usage: py -I problems/1186/exact/check_star.py [W]     (default W = 4)
"""
import sys

import numpy as np

THR = [(28, True), (34, False), (62, True), (99, False), (158, True), (274, False), (390, True), (449, False),
       (486, True), (514, False), (520, True)]


def c1(x):
    for thr, val in THR:
        if x <= thr:
            return val
    return False


def sg(x):
    return 1 if c1(x) else -1


def K4(L, p, q):
    m = 2 * q - p - 1
    if 1 <= m <= L - 2:
        return 4
    if m == 0 or m == L - 1:
        return 3
    if m == -1 or m == L:
        return 1
    return 0


def T_direct(L=548):
    return sum(K4(L, p, q) * sg(p) * sg(q) for p in range(1, L + 1) for q in range(1, L + 1))


def T_starT(L=548):
    h = L // 2
    P = [0] * (L + 1)
    for k in range(1, L + 1):
        P[k] = P[k - 1] + sg(k)
    t = 0
    for q in range(1, h + 1):
        t += sg(q) * (4 * P[2 * q - 2] + 3 * sg(2 * q - 1) + sg(2 * q))
        t += sg(h + q) * (4 * (P[2 * h] - P[2 * q]) + 3 * sg(2 * q) + sg(2 * q - 1))
    return t


def Wm_sstar(w):
    n = 1096 * w
    k = 2 * w
    s = np.zeros(n + 2, dtype=np.int64)
    for x in range(1, n + 1):
        s[x] = sg((x + k - 1) // k)
    pre = np.cumsum(s)
    tot = 0
    for y in range(1, n + 1):
        d = min(y - 1, n - y)
        tot += int(s[y]) * int(pre[y + d] - pre[y - d - 1])
    return tot


if __name__ == "__main__":
    W = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    a, b = T_direct(), T_starT()
    print("T direct =", a, " T (274-term form) =", b)
    assert a == b == -43840
    for w in range(1, W + 1):
        v = Wm_sstar(w)
        print("w =", w, "n =", 1096 * w, "Wm =", v, "= -43840 w^2:", v == -43840 * w * w,
              " Lean bound holds:", v >= -43840 * w * w - 1096 * w - 2192)
        assert v >= -43840 * w * w - 1096 * w - 2192
    print("OK")
