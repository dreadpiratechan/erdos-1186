"""Compare sdpmodel.py (this lane's Python model) with the Lean definitions, evaluated in Lean over Q by `fidelity.lean`
(definitions copied from P1186Ex.lean / P1186M2.lean / P1186Tab.lean / P1186Low.lean, with R -> Q).
Usage:  (from <worktree>/lean, through the gate)  lake env lean ../problems/1186/out/fidelity.lean > ../problems/1186/exact/data/fidelity_lean_out.txt
        py -I fidelity_check.py
Exits non-zero on any mismatch."""
import io
import os
import re
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr

import sdpmodel as M

txt = io.open(M.EXACT / "data" / "fidelity_lean_out.txt", encoding="utf-8").read()


def rat(s):
    m = re.fullmatch(r"mkRat \(?(-?\d+)\)? (\d+)", s.strip())
    if m:
        return Fr(int(m.group(1)), int(m.group(2)))
    return Fr(int(s))


lines = [" ".join(x.split()) for x in re.split(r"(?<=\))\s*\n(?=\()", txt.strip())]
assert len(lines) == 5, lines


def tup(l):
    inner = l.strip()[1:-1]
    return [rat(x) for x in re.split(r",\s*(?![^()]*\))", inner)]


def lists(l):
    """'([a, b, ...], [c, d, ...])' -> two lists of Fractions"""
    m = re.fullmatch(r"\(\[(.*)\], \[(.*)\]\)", l.strip())
    return [[rat(x) for x in g.split(", ")] for g in m.groups()]


G24, G8 = M.load_grid("G24"), M.load_grid("G8")
ok = True


def cmp(name, a, b):
    global ok
    good = a == b
    ok &= good
    print("%-34s %s" % (name, "OK" if good else "MISMATCH lean=%s py=%s" % (a, b)))


l1 = tup(lines[0])
cmp("N (G24, G8)", l1, [G24.N, G8.N])
l2 = tup(lines[1])
cmp("A4 samples", l2, [G24.A4[5][7], G24.A4[0][0], G24.A4[60][70], G8.A4[10][20], G8.A4[100][3], G8.A4[145][145]])
l3 = tup(lines[2])
cmp("sgn samples", l3, [G24.sgn[0], G24.sgn[60], G24.sgn[129], G8.sgn[3], G8.sgn[100]])
YT = [lambda i: Fr((i * 7 + 3) % 13, 13), lambda i: Fr((i * 5 + 1) % 17, 16), lambda i: Fr(1 if i % 2 == 0 else 0),
      lambda i: Fr(1), lambda i: Fr((i * 11 + 4) % 7, 6), lambda i: Fr(0)]
Y24 = [[f(i) for i in range(G24.N)] for f in YT]
Y8 = [[f(i) for i in range(G8.N)] for f in YT]
m24, m8 = lists(lines[3])
cmp("mval G24 (6 points)", m24, [M.mval(G24, y) for y in Y24])
cmp("mval G8 (6 points)", m8, [M.mval(G8, y) for y in Y8])
L24, L8 = lists(lines[4])
cmp("Lval G24 (6 points)", L24, [M.lval_exact(G24, y) for y in Y24])
cmp("Lval G8 (6 points)", L8, [M.lval_exact(G8, y) for y in Y8])
print("FIDELITY", "OK" if ok else "FAILED")
sys.exit(0 if ok else 1)
