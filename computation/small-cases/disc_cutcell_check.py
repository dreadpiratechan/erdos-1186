#!/usr/bin/env python3
"""Exhaustive check of the discrete cut-cell inequality (Lemma 5.4 of the manuscript).

    py -I disc_cutcell_check.py [wmax]

For w = 2, 4, ..., wmax (default 10) and all sign vectors s, t in {-1,+1}^w it computes the largest value of
    8*D - 2*X*Y - [(w^2 - X^2) + 3*(w^2 - Y^2)],   D = sum_i s_i T(floor(i/2)),  T(k) = t_1 + ... + t_k,
which the lemma bounds by 4w.  For fixed w the expression is convex in s and in t separately, so its maximum over the
cube [-1,1]^w x [-1,1]^w is attained at vertices and the check covers the real-valued statement for these w.
"""
import itertools
import sys

import numpy as np


def worst(w: int) -> int:
    vecs = np.array(list(itertools.product([-1, 1], repeat=w)), dtype=np.int64)
    X = vecs.sum(1)
    cs = np.concatenate([np.zeros((len(vecs), 1), dtype=np.int64), np.cumsum(vecs, 1)], 1)  # cs[:, k] = T(k)
    idx = np.array([i // 2 for i in range(1, w + 1)])
    D = vecs @ cs[:, idx].T  # D[s, t] = sum_i s_i T_t(floor(i/2))
    Xs, Y = X[:, None], X[None, :]
    return int((8 * D - 2 * Xs * Y - ((w * w - Xs ** 2) + 3 * (w * w - Y ** 2))).max())


def main() -> int:
    wmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    ok = True
    for w in range(2, wmax + 1, 2):
        m = worst(w)
        good = m <= 4 * w
        ok &= good
        print(f"w={w}: largest excess {m}  (lemma allows 4w = {4 * w})  {'OK' if good else 'FAIL'}")
    print("RESULT:", "ALL OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
