#!/usr/bin/env python3
"""Sanity check of the definition: exhaustive minMonoCount 3 n for n <= N0 against OEIS A121385.

`monoCount 3 n c` counts pairs (a, d), d >= 1, a + 2d <= n, with c(a) = c(a+d) = c(a+2d) (formal-conjectures c83a94d).  For
n <= N0 every colouring is enumerated (2^n of them, vectorised); the minimum is compared with the first terms of A121385
(OEIS, read 2026-10-26: 0,0,0,0,0,0,0,0,1,1,2,2,3,4,5,6,7,8,10,12,14,16,18,20,22,24,...; offset 1; S. Butler 2006).

    py -I oeis_small.py [N0]        (default N0 = 24; about a minute)
"""
import sys
import numpy as np

OEIS = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 31, 34]


def min_mono(n: int) -> int:
    best = None
    chunk = 1 << 20
    total = 1 << n
    for lo in range(0, total, chunk):
        c = np.arange(lo, min(lo + chunk, total), dtype=np.uint64)
        cnt = np.zeros(c.shape, dtype=np.int32)
        for d in range(1, (n - 1) // 2 + 1):
            for a in range(1, n - 2 * d + 1):
                b0 = (c >> np.uint64(a - 1)) & np.uint64(1)
                b1 = (c >> np.uint64(a - 1 + d)) & np.uint64(1)
                b2 = (c >> np.uint64(a - 1 + 2 * d)) & np.uint64(1)
                cnt += ((b0 == b1) & (b1 == b2)).astype(np.int32)
        m = int(cnt.min())
        best = m if best is None else min(best, m)
    return best


def main() -> int:
    n0 = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    ok = True
    for n in range(1, n0 + 1):
        v = min_mono(n)
        good = v == OEIS[n - 1]
        ok &= good
        print(f"n={n:2d}  min monoCount 3 n = {v:3d}  A121385 = {OEIS[n-1]:3d}  {'OK' if good else 'MISMATCH'}", flush=True)
    print("RESULT:", "ALL OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
