"""Numerical sanity test of the Lean interface `P1186Ex.lean` (evidence, not proof): exact integer arithmetic.

For n = 1096 w (w = 1, 2, 3, 5): Wm = Qd; the expansion Wm(s) = Wm(s*) + 2 sum H2 sigma + 4 Qd(s* sigma);
StarOK slack (Wm(s*) + 5/137 n^2) / w; BathOK slack over the worst sigma per cell and size (the k lowest H2 points);
PairOK slack on random and block sigma. Bounded slack / w as w grows is what the interface needs.

Usage: py -I problems/1186/exact/test_interface.py
"""
import io
import json
import random
import sys
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gen_interface import c1, K4  # noqa: E402

G = json.load(io.open(Path(__file__).resolve().parent / "data" / "grids.json", encoding="utf-8"))


def sstar(w):
    n = 1096 * w
    k = 2 * w
    return np.array([0] + [1 if c1((x + k - 1) // k) else -1 for x in range(1, n + 1)], dtype=np.int64)


def pre(u):
    return np.cumsum(u)          # pre[t] = sum_{x <= t} u_x (u[0] = 0)


def Wm(s, n):
    P = pre(s)
    tot = 0
    for y in range(1, n + 1):
        D = min(y - 1, n - y)
        tot += int(s[y]) * int(P[y + D] - P[y - D - 1])
    return tot


def Qd(u, n):
    P = pre(u)
    tot = 0
    for y in range(1, n + 1):
        lo, hi = max(1, 2 * y - n), min(n, 2 * y - 1)
        if lo <= hi:
            tot += int(u[y]) * int(P[hi] - P[lo - 1])
    return tot


def H2(s, n):
    P = pre(s)
    out = np.zeros(n + 1, dtype=np.int64)
    for x in range(1, n + 1):
        ylo, yhi = (x + 2) // 2, (x + n) // 2          # 1 <= 2y - x <= n
        row = int(P[yhi] - P[ylo - 1]) if ylo <= yhi else 0
        elo, ehi = max(1, 2 * x - n), min(n, 2 * x - 1)
        col = int(P[ehi] - P[elo - 1]) if elo <= ehi else 0
        out[x] = -int(s[x]) * (row + col)
    return out


def pterm(g, i, j, yi, yj):
    U = 1096
    wi, wj = Fr(g["pts"][i + 1] - g["pts"][i], U), Fr(g["pts"][j + 1] - g["pts"][j], U)
    P = wi * wj * yi * yj
    Ain = Fr(g["A4"][i][j], 4 * U * U)
    Aout = wi * wj - Ain
    if g["sgn"][i] * g["sgn"][j] == 1:
        return max(Fr(0), P - Aout)
    return max(-Ain, -P)


def main():
    rng = random.Random(1186)
    for w in (1, 2, 3, 5):
        n = 1096 * w
        s0 = sstar(w)
        h2 = H2(s0, n)
        ws = Wm(s0, n)
        # 1-2: Wm = Qd, expansion identity
        sig = np.array([0] + [rng.randint(0, 1) for _ in range(n)], dtype=np.int64)
        s = s0 * (1 - 2 * sig)
        s[0] = 0
        assert Wm(s, n) == Qd(s, n)
        lhs = Wm(s, n)
        rhs = ws + 2 * int(np.dot(h2[1:], sig[1:])) + 4 * Qd(s0 * sig, n)
        assert lhs == rhs, (lhs, rhs)
        star = Fr(ws) + Fr(5, 137) * n * n
        print(f"w={w}: Wm=Qd OK, expansion OK; StarOK slack/w = {float(star / w):.3f}")
        # 4: BathOK worst case per cell
        worst = None
        for name in ("g24", "g8"):
            g = G[name]
            for i in range(len(g["pts"]) - 1):
                a, b = Fr(g["a"][i]), Fr(g["b"][i])
                xs = list(range(g["pts"][i] * w + 1, g["pts"][i + 1] * w + 1))
                vals = sorted(int(h2[x]) for x in xs)
                acc = 0
                for k in range(len(xs) + 1):
                    if k:
                        acc += vals[k - 1]
                    y = Fr(k, len(xs))
                    sl = (acc - 2 * n * n * (a * y + b * y * y)) / w
                    if worst is None or sl < worst[0]:
                        worst = (sl, name, i, k)
        print(f"   BathOK worst slack/w = {float(worst[0]):.3f} at {worst[1:]}")
        # 5: PairOK on random and block sigma
        for name in ("g24", "g8"):
            g = G[name]
            N = len(g["pts"]) - 1
            mins = []
            for trial in range(6 if w < 5 else 2):
                if trial % 2 == 0:
                    p = rng.random()
                    sig = np.array([0] + [1 if rng.random() < p else 0 for _ in range(n)], dtype=np.int64)
                else:
                    sig = np.zeros(n + 1, dtype=np.int64)
                    for i in range(N):
                        if rng.random() < 0.5:
                            lo, hi = g["pts"][i] * w + 1, g["pts"][i + 1] * w
                            cut = rng.randint(lo, hi)
                            sig[lo:cut + 1] = 1
                ys = []
                for i in range(N):
                    lo, hi = g["pts"][i] * w + 1, g["pts"][i + 1] * w
                    ys.append(Fr(int(sig[lo:hi + 1].sum()), hi - lo + 1))
                tot = sum(pterm(g, i, j, ys[i], ys[j]) for i in range(N) for j in range(N))
                q = Qd(s0 * sig, n)
                mins.append(float((q - n * n * tot) / w))
            print(f"   PairOK {name} slack/w min over trials = {min(mins):.3f}")


if __name__ == "__main__":
    main()
