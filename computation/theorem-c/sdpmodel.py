"""Erdos 1186 exact lane (excertsdp): the finite model of the five `RegionLB` statements, exact arithmetic, own code.

Formalises (as data) the finite part of the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05,
unrefereed); the mathematics is its author's.  This module is written from the Lean interface
`lean/Erdos/Proofs/P1186Ex.lean` (+ `P1186ExData.lean`), not from the reviewers' code.

Objects (all exact, `fractions.Fraction` / Python ints):
  * `Grid`: cell endpoints `pts` (units 1/1096), the Lemma 2 constants `a_i`, `b_i`, the cell signs, the pair counts
    `A4[i][j] = sum_{p in cell i, q in cell j} K4 1096 p q`, taken from `data/grids.json` and CROSS-CHECKED here against
    `P1186ExData.lean` (pts, a, b) and a fresh kernel-count recomputation (A4, signs).
  * `Region`: `lo <= m <= hi`, `m = sum_i w_i y_i`.
  * `lval_exact`: `Lval G y` by the Lean definition (true `max`).
  * `Cert`: `theta` for the cut pairs, `mu` for a list of "forms" `f` (each `>= 0` on the region), `K` (dyadic scale).
  * `lval_theta`: the convex-combination lower bound `L_theta <= Lval`.
  * `build_S`: the exact symmetric matrix `S` with `v'Sv = L_theta(y) - sum mu_f f(y)`, `v = (1, y)`.
"""
import io
import json
import re
from fractions import Fraction as Fr
from math import gcd
from pathlib import Path

EXACT = Path(__file__).resolve().parent  # this folder (computation/theorem-c; problems/1186/exact in the research repository)
ROOT = EXACT.parents[1]  # the repository root, which contains lean/
U = 1096

# ---------------------------------------------------------------------------------------------------------------
# the PRS colouring and K4, from the Lean definitions (P1186Tab.lean c1; P1186M2.lean K4)
_C1_THR = [(28, True), (34, False), (62, True), (99, False), (158, True), (274, False), (390, True), (449, False),
           (486, True), (514, False), (520, True)]


def c1(x):
    for thr, val in _C1_THR:
        if x <= thr:
            return val
    return False


def sg_c1(x):
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


# ---------------------------------------------------------------------------------------------------------------
class Grid:
    def __init__(self, name, pts, a, b, A4, sgn):
        self.name = name
        self.pts = list(pts)
        self.N = len(pts) - 1
        self.a = [Fr(x) for x in a]
        self.b = [Fr(x) for x in b]
        self.A4 = A4
        self.sgn = list(sgn)
        self.len = [pts[i + 1] - pts[i] for i in range(self.N)]
        self.w = [Fr(l, U) for l in self.len]
        assert sum(self.w) == 1
        assert len(self.a) == self.N and len(self.b) == self.N and len(self.sgn) == self.N

    # classification of ordered pairs by the kernel count
    def kind(self, i, j):
        """'full' (A_out = 0), 'empty' (A_in = 0) or 'cut'."""
        A = self.A4[i][j]
        full = 4 * self.len[i] * self.len[j]
        if A == 0:
            return "empty"
        if A == full:
            return "full"
        assert 0 < A < full
        return "cut"

    def ain(self, i, j):
        return Fr(self.A4[i][j], 4 * U * U)

    def aout(self, i, j):
        return self.w[i] * self.w[j] - self.ain(i, j)

    def cuts(self):
        return [(i, j) for i in range(self.N) for j in range(self.N) if self.kind(i, j) == "cut"]


def _parse_lean_data():
    """Parse P1186ExData.lean: {G24: (pts, a, b), G8: ...}."""
    txt = io.open(ROOT / "lean" / "Erdos" / "Proofs" / "P1186ExData.lean", encoding="utf-8").read()
    out = {}
    for m in re.finditer(r"def (G24|G8) : Grid where\s+pts := \[([^\]]*)\]\s+a := \[(.*?)\]\s+b := \[(.*?)\]\s*\n", txt, re.S):
        name, pts, a, b = m.groups()
        pts = [int(x) for x in pts.split(",")]

        def rats(s):
            res = []
            for t in re.finditer(r"\(\s*(-?\d+)\s*(?:/\s*(\d+))?\s*:\s*ℚ\)", s):
                res.append(Fr(int(t.group(1)), int(t.group(2) or 1)))
            return res
        out[name] = (pts, rats(a), rats(b))
    return out


def _recount_A4(pts):
    """A4[i][j] from the Lean definition, with an independent numpy recount (prefix sums of the K4 table)."""
    import numpy as np
    K = np.zeros((U + 1, U + 1), dtype=np.int64)       # K[p][q], 1-indexed
    for p in range(1, U + 1):
        for q in range(1, U + 1):
            K[p][q] = K4(U, p, q)
    S = np.zeros((U + 1, U + 1), dtype=np.int64)
    S[1:, 1:] = K[1:, 1:].cumsum(0).cumsum(1)
    n = len(pts) - 1
    A = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            p0, p1, q0, q1 = pts[i], pts[i + 1], pts[j], pts[j + 1]     # (p0, p1] x (q0, q1]
            A[i][j] = int(S[p1][q1] - S[p0][q1] - S[p1][q0] + S[p0][q0])
    return A


_GRID_CACHE = {}


def load_grid(name, recheck=True):
    """name in {'G24', 'G8'}; data/grids.json cross-checked against the Lean data file and a recount of A4."""
    if name in _GRID_CACHE:
        return _GRID_CACHE[name]
    gj = json.load(io.open(EXACT / "data" / "grids.json", encoding="utf-8"))[name.lower()]
    G = Grid(name, gj["pts"], gj["a"], gj["b"], gj["A4"], gj["sgn"])
    if recheck:
        lean = _parse_lean_data()[name]
        assert lean[0] == G.pts, "pts differ from P1186ExData.lean"
        assert lean[1] == G.a and lean[2] == G.b, "a/b differ from P1186ExData.lean"
        for i in range(G.N):
            assert len(set(sg_c1(k // 2 + 1) for k in range(G.pts[i], G.pts[i + 1]))) == 1
            assert G.sgn[i] == sg_c1(G.pts[i] // 2 + 1), i
        assert G.A4 == _recount_A4(G.pts), "A4 differs from the recount"
    _GRID_CACHE[name] = G
    return G


REGIONS = {
    1: ("G24", Fr(0), Fr(1, 5)),
    2: ("G24", Fr(1, 5), Fr(3, 10)),
    3: ("G24", Fr(3, 10), Fr(2, 5)),
    4: ("G8", Fr(2, 5), Fr(9, 20)),
    5: ("G8", Fr(9, 20), Fr(1, 2)),
}


# ---------------------------------------------------------------------------------------------------------------
# exact evaluation by the Lean definitions
def mval(G, y):
    return sum(G.w[i] * y[i] for i in range(G.N))


def pterm(G, i, j, yi, yj):
    P = G.w[i] * G.w[j] * yi * yj
    Ain = G.ain(i, j)
    Aout = G.w[i] * G.w[j] - Ain
    if G.sgn[i] * G.sgn[j] == 1:
        return max(Fr(0), P - Aout)
    return max(-Ain, -P)


def lval_exact(G, y):
    s = sum(G.a[i] * y[i] + G.b[i] * y[i] ** 2 for i in range(G.N))
    for i in range(G.N):
        for j in range(G.N):
            s += pterm(G, i, j, y[i], y[j])
    return s


def theta_default(G, i, j):
    k = G.kind(i, j)
    return Fr(0) if k == "full" else Fr(1)


def theta_of(G, theta, i, j):
    """theta: dict {(i, j): Fraction} for the cut pairs; full -> 0, empty -> 1."""
    k = G.kind(i, j)
    if k == "cut":
        return theta[(i, j)]
    return Fr(0) if k == "full" else Fr(1)


def pterm_theta(G, i, j, yi, yj, th):
    """(1-th) * first + th * second, `first`/`second` the two arguments of the `max` in `pterm` (<= pterm for th in [0,1])."""
    P = G.w[i] * G.w[j] * yi * yj
    Ain = G.ain(i, j)
    Aout = G.w[i] * G.w[j] - Ain
    if G.sgn[i] * G.sgn[j] == 1:
        return (1 - th) * (P - Aout)          # second arg is 0
    return th * (-Ain) + (1 - th) * (-P)


def lval_theta(G, theta, y):
    s = sum(G.a[i] * y[i] + G.b[i] * y[i] ** 2 for i in range(G.N))
    for i in range(G.N):
        for j in range(G.N):
            s += pterm_theta(G, i, j, y[i], y[j], theta_of(G, theta, i, j))
    return s


# ---------------------------------------------------------------------------------------------------------------
# forms: lists  [kind, args...]   (see FORMAT.md)
def _atom(G, R, name, i, y):
    lo, hi = R[1], R[2]
    if name == "y":
        return y[i]
    if name == "o":
        return 1 - y[i]
    if name == "ml":
        return mval(G, y) - lo
    if name == "hm":
        return hi - mval(G, y)
    raise KeyError(name)


FORM_ARITY = {"y": 1, "o": 1, "ml": 0, "hm": 0, "yy": 2, "oo": 2, "yo": 2, "yml": 1, "oml": 1, "yhm": 1, "ohm": 1,
              "mhm": 0, "tri": 6}


def eval_form(G, R, form, y):
    k = form[0]
    a = form[1:]
    A = lambda nm, i=None: _atom(G, R, nm, i, y)    # noqa: E731
    if k == "y":
        return A("y", a[0])
    if k == "o":
        return A("o", a[0])
    if k == "ml":
        return A("ml")
    if k == "hm":
        return A("hm")
    if k == "yy":
        return A("y", a[0]) * A("y", a[1])
    if k == "oo":
        return A("o", a[0]) * A("o", a[1])
    if k == "yo":
        return A("y", a[0]) * A("o", a[1])
    if k == "yml":
        return A("y", a[0]) * A("ml")
    if k == "oml":
        return A("o", a[0]) * A("ml")
    if k == "yhm":
        return A("y", a[0]) * A("hm")
    if k == "ohm":
        return A("o", a[0]) * A("hm")
    if k == "mhm":
        return A("ml") * A("hm")
    if k == "tri":
        i, j, kk, s1, s2, s3 = a
        z = lambda t: 1 - 2 * y[t]    # noqa: E731
        return 1 + s1 * z(i) * z(j) + s2 * z(j) * z(kk) + s3 * z(i) * z(kk)
    raise KeyError(k)


def check_form_valid(G, form):
    k = form[0]
    a = form[1:]
    assert k in FORM_ARITY and len(a) == FORM_ARITY[k], form
    N = G.N
    idx = {"y": [0], "o": [0], "yy": [0, 1], "oo": [0, 1], "yo": [0, 1], "yml": [0], "oml": [0], "yhm": [0], "ohm": [0]}
    for t in idx.get(k, []):
        assert 0 <= a[t] < N, form
    if k in ("yy", "oo"):
        assert a[0] <= a[1], form
    if k == "tri":
        i, j, kk, s1, s2, s3 = a
        assert 0 <= i < j < kk < N, form
        assert all(s in (1, -1) for s in (s1, s2, s3)) and s1 * s2 * s3 == 1, form


# ---------------------------------------------------------------------------------------------------------------
# polynomials as symmetric matrices over v = (1, y_0 .. y_{N-1}):  v'Sv = S_00 + 2 sum S_0k y_k + sum S_kl y_k y_l
class Sym:
    def __init__(self, n):
        self.n = n                      # matrix is (n+1) x (n+1); index 0 = constant
        self.d = {}                     # (a, b), a <= b -> entry S_ab (the symmetric-matrix entry)

    def add(self, a, b, v):
        if v == 0:
            return
        if a > b:
            a, b = b, a
        self.d[(a, b)] = self.d.get((a, b), 0) + v

    def add_lin_prod(self, l1, l2, scale):
        """add scale * l1 * l2, l = (c, {k: coef}) with k an index into y (0-based)."""
        c1_, a1 = l1
        c2_, a2 = l2
        self.add(0, 0, scale * c1_ * c2_)
        for k, v in a2.items():
            self.add(0, k + 1, scale * c1_ * v / 2)
        for k, v in a1.items():
            self.add(0, k + 1, scale * c2_ * v / 2)
        for k, u in a1.items():
            for l, v in a2.items():
                if k == l:
                    self.add(k + 1, l + 1, scale * u * v)
                else:
                    self.add(k + 1, l + 1, scale * u * v / 2)      # the symmetric matrix gets half on each of (k,l), (l,k)

    def add_lin(self, l, scale):
        c, a = l
        self.add(0, 0, scale * c)
        for k, v in a.items():
            self.add(0, k + 1, scale * v / 2)

    def full_matrix(self, scale=1):
        """list of lists of Fractions (symmetric)."""
        n1 = self.n + 1
        M = [[Fr(0)] * n1 for _ in range(n1)]
        for (a, b), v in self.d.items():
            M[a][b] += v * scale
            if a != b:
                M[b][a] += v * scale
        return M


def _lin_atom(G, R, name, i=None):
    lo, hi = R[1], R[2]
    if name == "y":
        return (Fr(0), {i: Fr(1)})
    if name == "o":
        return (Fr(1), {i: Fr(-1)})
    if name == "ml":
        return (-lo, {k: G.w[k] for k in range(G.N)})
    if name == "hm":
        return (hi, {k: -G.w[k] for k in range(G.N)})
    raise KeyError(name)


def add_form(G, R, S, form, scale):
    """S += scale * f  (as a symmetric matrix)."""
    k = form[0]
    a = form[1:]
    L = lambda nm, i=None: _lin_atom(G, R, nm, i)    # noqa: E731
    one = Fr(1)
    if k in ("y", "o", "ml", "hm"):
        S.add_lin(L(k, a[0] if a else None), scale)
    elif k == "yy":
        S.add_lin_prod(L("y", a[0]), L("y", a[1]), scale)
    elif k == "oo":
        S.add_lin_prod(L("o", a[0]), L("o", a[1]), scale)
    elif k == "yo":
        S.add_lin_prod(L("y", a[0]), L("o", a[1]), scale)
    elif k == "yml":
        S.add_lin_prod(L("y", a[0]), L("ml"), scale)
    elif k == "oml":
        S.add_lin_prod(L("o", a[0]), L("ml"), scale)
    elif k == "yhm":
        S.add_lin_prod(L("y", a[0]), L("hm"), scale)
    elif k == "ohm":
        S.add_lin_prod(L("o", a[0]), L("hm"), scale)
    elif k == "mhm":
        S.add_lin_prod(L("ml"), L("hm"), scale)
    elif k == "tri":
        i, j, kk, s1, s2, s3 = a
        z = lambda t: (one, {t: Fr(-2)})    # noqa: E731
        S.add(0, 0, scale)
        S.add_lin_prod(z(i), z(j), scale * s1)
        S.add_lin_prod(z(j), z(kk), scale * s2)
        S.add_lin_prod(z(i), z(kk), scale * s3)
    else:
        raise KeyError(k)


def add_ltheta(G, S, theta):
    """S += L_theta (the polynomial of `lval_theta`)."""
    for i in range(G.N):
        S.add(0, i + 1, G.a[i] / 2)
        S.add(i + 1, i + 1, G.b[i])
    for i in range(G.N):
        for j in range(G.N):
            th = theta_of(G, theta, i, j)
            wij = G.w[i] * G.w[j]
            Ain = G.ain(i, j)
            if G.sgn[i] * G.sgn[j] == 1:
                S.add(0, 0, -(1 - th) * (wij - Ain))
                S.add(i + 1, j + 1, (1 - th) * wij / 2 if i != j else (1 - th) * wij)
            else:
                S.add(0, 0, -th * Ain)
                S.add(i + 1, j + 1, -(1 - th) * wij / 2 if i != j else -(1 - th) * wij)


def build_S(G, R, theta, forms_mu, Bp=Fr(0)):
    """Exact S with  v'Sv = L_theta(y) - Bp - sum_f mu_f f(y).  forms_mu: iterable of (form, mu)."""
    S = Sym(G.N)
    add_ltheta(G, S, theta)
    S.add(0, 0, -Bp)
    for form, mu in forms_mu:
        add_form(G, R, S, form, -mu)
    return S


def quad_value(Sm, y):
    """v'Sv from a Sym at point y (exact)."""
    v = [Fr(1)] + list(y)
    tot = Fr(0)
    for (a, b), s in Sm.d.items():
        tot += s * v[a] * v[b] * (1 if a == b else 2)
    return tot


def lcm(a, b):
    return a * b // gcd(a, b)
