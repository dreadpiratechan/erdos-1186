"""Erdos #1186 (side exploration, NOT the main search): numerical size of the PRS-style semidefinite (Shor) lower bound as L grows.
PRS08 Sec. 3.2: with L horizontal strips, A_ij = B_ij + B_ji, B_ij = [j+1 <= 2i <= j+L], |N+| <= n^2/(4L) + n^2/4 - n^2/(4 L^2) q(x),
q(x) = x^T A x >= -sum d_i whenever A + diag(d) is PSD; V(n) >= (1/2)(3/8 - c) n^2 with c = 1/(4L) + 1/4 + (sum d)/(4 L^2).
Here: S(L) = min <A,X> over X PSD, diag X = 1 (the SDP optimum = min sum -d), via Burer-Monteiro (rank r, unit rows) + L-BFGS.
This gives the NUMERICAL value of the best bound this method can give at that L (not a certificate).   usage: py shorlb.py L [rank]"""
import os, sys, time
os.environ.setdefault("OMP_NUM_THREADS", "1"); os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np
from scipy.optimize import minimize

def Amat(L):
    i = np.arange(1, L + 1)[:, None]; j = np.arange(1, L + 1)[None, :]
    B = ((j + 1 <= 2 * i) & (2 * i <= j + L)).astype(np.float64)
    return B + B.T

def solve(L, r=None, seed=0, tries=3):
    A = Amat(L)
    r = r or int(np.ceil(np.sqrt(2 * L))) + 1
    best = None
    for t in range(tries):
        rng = np.random.default_rng(seed + t)
        U0 = rng.standard_normal((L, r))
        def f(u):
            U = u.reshape(L, r)
            nr = np.linalg.norm(U, axis=1, keepdims=True)
            V = U / nr
            AV = A @ V
            val = np.sum(AV * V)
            G = 2 * AV  # d val / dV
            # chain through normalisation: dV/dU = (I - v v^T)/nr
            GU = (G - np.sum(G * V, axis=1, keepdims=True) * V) / nr
            return val, GU.ravel()
        res = minimize(f, U0.ravel(), jac=True, method="L-BFGS-B", options={"maxiter": 20000, "maxcor": 30, "ftol": 1e-15, "gtol": 1e-9})
        if best is None or res.fun < best[0]:
            best = (res.fun, res.x.reshape(L, r))
    val, U = best
    V = U / np.linalg.norm(U, axis=1, keepdims=True)
    AV = A @ V
    d = -np.sum(AV * V, axis=1)          # KKT dual diagonal: (A + D) V = 0 with D = diag(d)
    lam = np.linalg.eigvalsh(A + np.diag(d))[0]
    return A, val, d, lam

if __name__ == "__main__":
    for L in map(int, sys.argv[1:]):
        t0 = time.time()
        A, S, d, lam = solve(L)
        sd = d.sum()
        # dual-feasible shift: d' = d - lam (makes A + D' PSD); bound uses sum d'
        sdp = sd - lam * L
        for name, sumd in (("SDP value", -S), ("certifiable (shifted by -lambda_min)", sdp)):
            c = 1 / (4 * L) + 0.25 + sumd / (4 * L * L)
            print("L=%d  %s: sum d = %.3f  ->  V(n) >= %.6f n^2   (PRS L=128 paper value 0.051117; PRS upper 0.053376)" % (L, name, sumd, 0.5 * (0.375 - c)))
        print("   lambda_min(A + D_kkt) = %.2e  (%.1fs)" % (lam, time.time() - t0), flush=True)
