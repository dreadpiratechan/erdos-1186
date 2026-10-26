"""Exact-arithmetic checks of the constants and decimals quoted in README.md and docs/CHECKING-GUIDE.md.

Usage (from the repository root):  py verification/number_checks.py

Each decimal quoted for a constant must be a TRUNCATION of its exact expansion (a prefix of the digits, followed by
"..."), never a rounding. The other checks are the small identities that connect the constants of the three theorems.
The Lean statements themselves are compared with the upstream file by verification/fidelity_check.py and
verification/make_upstream_pin.py; this script only checks the arithmetic around them.
Exit status 0 iff every check passes.
"""
import sys
from decimal import Decimal, getcontext
from fractions import Fraction as F

getcontext().prec = 60
checks = []


def check(label, cond):
    checks.append((label, bool(cond)))
    print(f"{'OK  ' if cond else 'FAIL'} {label}")


def digits(x: F) -> str:
    return str(Decimal(x.numerator) / Decimal(x.denominator))


def truncation(x: F, shown: str) -> bool:
    """`shown` (e.g. '0.0533615') is a prefix of the exact decimal expansion of x."""
    return digits(x).startswith(shown)


PRS_LO, PRS_HI = F(1675, 32768), F(117, 2192)
B256, B128, B64 = F(14324135, 268435456), F(1788837, 33554432), F(1782409, 33554432)
STRIP256 = F(6928985, 134217728)

# The constants of the theorems
check("12-block colouring: block lengths 28,6,28,37,59,116,116,59,37,28,6,28 sum to 548 and are palindromic",
      sum(b := [28, 6, 28, 37, 59, 116, 116, 59, 37, 28, 6, 28]) == 548 and b == b[::-1])
check("upper bound of Theorem A: 16029 / 548^2 = 117/2192", F(16029, 548 ** 2) == PRS_HI)
check("Theorem C: 1/16 - 5/548 = 117/2192 (5/548 = (5/137)/4)", F(1, 16) - F(5, 548) == PRS_HI)
check("Theorem C star value: (5/137) * 1096^2 = 43840", F(5, 137) * 1096 ** 2 == 43840)
check("ordering 1675/32768 < 6928985/134217728 < 1782409/33554432 < 1788837/33554432 < 14324135/268435456 < 117/2192",
      PRS_LO < STRIP256 < B64 < B128 < B256 < PRS_HI)
gap = PRS_HI - B256
check(f"gap of Theorem B: 117/2192 - 14324135/268435456 = 527777/36775657472 = {digits(gap)[:12]}...",
      gap == F(527777, 36775657472))
check("gap of Theorem B is 1.435...e-5 (truncated)", digits(gap * 10 ** 5).startswith("1.435"))
check("relative width of [14324135/268435456, 117/2192] is 2.68...e-4 (truncated)", digits(gap / PRS_HI * 10 ** 4).startswith("2.68"))
# Decimals quoted in the documentation: truncations, never roundings
for x, shown in ((PRS_LO, "0.0511169"), (PRS_HI, "0.0533759"), (B256, "0.0533615"), (B128, "0.0533114"),
                 (B64, "0.0531199"), (STRIP256, "0.0516249")):
    check(f"{x.numerator}/{x.denominator} = {shown}... is a truncation of {digits(x)[:14]}", truncation(x, shown))

bad = sum(1 for _, ok in checks if not ok)
print(f"ALL {len(checks)} CHECKS PASSED" if not bad else f"FAILED: {bad} of {len(checks)} checks")
sys.exit(1 if bad else 0)
