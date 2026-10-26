"""Erdos #1186 (night 2, lean1186b): generate Lean modules that make the KERNEL check a PRS08 diagonal certificate.

Input: a certificate json {"L", "Q", "dn"} (problems/1186/data/sdp_dn_L{L}.json): d_i = dn_i / Q, A_L + diag(d) PSD.
The Lean side (lean/Erdos/Proofs/P1186Cert128Lib.lean, namespace Erdos1186Night2, written by hand, no numbers) proves

    CertData.diagCert : 0 < Q -> 0 < S -> dn >= 0 -> (row lengths <= L) -> (every row of E is diagonally dominant)
                        -> DiagCert L (dn / Q)

where  M = Q*A + diag(dn)  (integer matrix),  S*M = C C^T + E,  C = integer lower-triangular rows (approximate Cholesky of M),
E = S*M - C C^T  (integer, symmetric).  Diagonal dominance of E:  sum_j |E_ij| <= 2 E_ii  (so E is PSD) is the only thing the
kernel evaluates (`decide +kernel`, in row chunks over several modules).  Rounding in this script is irrelevant to soundness.

This script (a) builds M from the PRS08 cell rule A_ij = B_ij + B_ji, B_ij = [j+1 <= 2i <= j+L] (the same as Aprs in P1186Prs.lean),
(b) finds C by float64 Cholesky of M - eps*I, scaled by t and rounded to integers (S = t^2), (c) re-checks EVERYTHING in exact Python
integers (the same criterion as the Lean `rowOK`), (d) writes modules  <Mod>Tab, <Mod>Chk1.., <Mod>  (or one --single file).

usage: py lean_cert.py data/sdp_dn_L128.json --module P1186Cert128 --out-dir ../../lean/Erdos/Proofs --rows-per-chunk 16
       py lean_cert.py data/sdp_dn_L128.json --single out/cert128_single.lean          (scratch; imports only the Lib)
       py lean_cert.py --selftest-L 16 --single out/cert016_single.lean               (own certificate for a small L, scratch)
"""
import argparse, json, math, os, sys
from fractions import Fraction
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
NS = "Erdos1186Night2"


def amat_int(L):
    """A = B + B^T, B_ij = [j+1 <= 2i <= j+L]; 1-indexed in the formula, 0-indexed array."""
    A = [[0] * L for _ in range(L)]
    for i in range(1, L + 1):
        for j in range(1, L + 1):
            b1 = 1 if (j + 1 <= 2 * i <= j + L) else 0
            b2 = 1 if (i + 1 <= 2 * j <= i + L) else 0
            A[i - 1][j - 1] = b1 + b2
    return A


def build_M(L, Q, dn):
    A = amat_int(L)
    M = [[Q * A[i][j] + (dn[i] if i == j else 0) for j in range(L)] for i in range(L)]
    return A, M


def exact_residual(M, C, S):
    """E = S*M - C C^T with exact Python ints; C lower triangular rows (list of lists, row i has i+1 entries)."""
    L = len(M)
    E = [[0] * L for _ in range(L)]
    for i in range(L):
        for j in range(L):
            g = sum(a * b for a, b in zip(C[i], C[j]))
            E[i][j] = S * M[i][j] - g
    return E


def dominant(E):
    """Mirror of Lean rowOK: sum_j |E_ij| <= 2 E_ii for all i.  Returns (ok, min margin) with margin = 2E_ii - sum|E_ij|."""
    worst = None
    for i, row in enumerate(E):
        m = 2 * row[i] - sum(abs(v) for v in row)
        worst = m if worst is None or m < worst else worst
    return worst >= 0, worst


def find_rounded_cholesky(M, tmin=1 << 6, tmax=1 << 40):
    L = len(M)
    Mf = np.array(M, dtype=np.float64)
    lam = float(np.linalg.eigvalsh(Mf)[0])
    if lam <= 0:
        raise SystemExit("float64 eigenvalue of M is %.3e <= 0: not positive definite" % lam)
    eps = 0.5 * lam
    Lc = np.linalg.cholesky(Mf - eps * np.eye(L))
    t = tmin
    while t <= tmax:
        C = np.rint(t * Lc).astype(object)
        Cl = [[int(C[i][k]) for k in range(i + 1)] for i in range(L)]
        S = t * t
        E = exact_residual(M, Cl, S)
        ok, margin = dominant(E)
        if ok:
            return Cl, S, t, E, margin, lam
        t *= 2
    raise SystemExit("no scale t <= 2^40 gave a diagonally dominant residual")


def selftest_certificate(L):
    """Own diagonal certificate for a small L (so scratch sizes need no stored json): shorlb dual, rounded up to 1/1024."""
    sys.path.insert(0, HERE)
    import shorlb
    A, S, d, lam = shorlb.solve(L)
    Q = 1024
    dn = [max(1, int(v)) for v in np.ceil((d + 1e-6) * Q)]
    return {"L": L, "Q": Q, "dn": dn}


def lean_list_int(xs):
    return "[" + ", ".join(str(int(v)) for v in xs) + "]"


def header(modname, doc):
    return "import Mathlib\nimport Erdos.Proofs.P1186Cert128Lib\n" + "{imports}" + "\n/-!\n" + doc + "\n-/\n\nnamespace " + NS + "\n\nopen Finset\n\n"


def emit(cert, args):
    L, Q, dn = cert["L"], cert["Q"], cert["dn"]
    assert len(dn) == L and all(isinstance(v, int) and v > 0 for v in dn), "dn must be positive ints"
    A, M = build_M(L, Q, dn)
    Cl, S, t, E, margin, lam = find_rounded_cholesky(M)
    okdom, worst = dominant(E)
    assert okdom
    # extra exact sanity: E symmetric
    assert all(E[i][j] == E[j][i] for i in range(L) for j in range(L))
    sumdn = sum(dn)
    sumd = Fraction(sumdn, Q)
    c = Fraction(1, 4 * L) + Fraction(1, 4) + sumd / (4 * L * L)
    bound = Fraction(1, 2) * (Fraction(3, 8) - c)
    info = ("L=%d Q=%d  sum dn=%d  sum d=%s  prsBound=%s=%.9f ; lambda_min(M)=%.4f ; t=%d S=t^2=%d ; max|C|=%d ; "
            "min row margin 2E_ii - sum|E_ij| = %d (exact)" % (L, Q, sumdn, sumd, bound, float(bound), lam, t, S,
                                                              max(abs(v) for r in Cl for v in r), worst))
    print(info)
    lines = {}
    nm = "%03d" % L if L < 1000 else str(L)
    if args.suffix:
        nm = args.suffix
    Tn = "T" + nm
    dnn = "dn" + nm
    rn = "rows" + nm
    rpc = args.rows_per_chunk
    if args.chunk_cost:
        # cost of row i = sum_j min(i, j) (length of the dot products it needs); greedy balanced chunks
        chunks, a0, acc = [], 1, 0
        for i in range(1, L + 1):
            acc += sum(min(i, j) for j in range(1, L + 1))
            if acc >= args.chunk_cost or i == L:
                chunks.append((a0, i - a0 + 1))
                a0, acc = i + 1, 0
    else:
        chunks = [(a, min(rpc, L - a + 1)) for a in range(1, L + 1, rpc)]  # (start row, count)

    doc_common = ("Generated by `problems/1186/lean_cert.py` from `%s` (no hand-typed numbers).  %s\n"
                  "Statement fidelity: `DiagCert L d` is the definition in `P1186Prs.lean` (night 2 shared interface): `d >= 0` on `1..L` and\n"
                  "`-(sum d_i x_i^2) <= x^T A x` for all real `x`, `A_ij = B_ij + B_ji`, `B_ij = [j+1 <= 2i <= j+L]`." % (
                      os.path.basename(args.json) if args.json else "own shorlb certificate (self-test)", info))

    tab = []
    tab.append("/-- The certificate numerators: `d_i = dn_i / %d`. -/\ndef %s : List ℤ := %s\n" % (Q, dnn, lean_list_int(dn)))
    for i, r in enumerate(Cl, 1):
        tab.append("def r%s_%d : List ℤ := %s\n" % (nm, i, lean_list_int(r)))
    tab.append("/-- Rows of the integer lower-triangular factor `C` (row `i` has `i` entries), scale `S = %d^2`. -/\n"
               "def %s : List (List ℤ) := [%s]\n" % (t, rn, ", ".join("r%s_%d" % (nm, i) for i in range(1, L + 1))))
    tab.append("/-- The certificate data. -/\ndef %s : CertData := { L := %d, Q := %d, S := %d, dn := %s, rows := %s }\n" % (Tn, L, Q, S, dnn, rn))
    tab.append("theorem %s_rows_len : %s.rows.length = %d := by decide +kernel\n" % (Tn, Tn, L))
    tab.append("theorem %s_hlen : ∀ i ∈ Icc 1 %d, (%s.row i).length ≤ %d := by decide +kernel\n" % (Tn, L, Tn, L))
    tab.append("theorem %s_hdn : ∀ i ∈ Icc 1 %d, 0 ≤ %s.dnAt i := by decide +kernel\n" % (Tn, L, Tn))
    tab.append("theorem %s_dn_sum : ∑ i ∈ Icc 1 %d, %s.dnAt i = %d := by decide +kernel\n" % (Tn, L, Tn, sumdn))
    tabsrc = "".join(tab)

    chk = []
    for k, (a, n) in enumerate(chunks):
        chk.append("/-- rows `%d..%d` of `%s` are diagonally dominant (kernel evaluation). -/\n"
                   "theorem %s_chk_%d : (List.range' %d %d).all %s.rowOK = true := by decide +kernel\n" % (a, a + n - 1, Tn, Tn, a, a, n, Tn))

    # final assembly
    fin = []
    cases = " ∨ ".join("(%d ≤ i ∧ i < %d)" % (a, a + n) for (a, n) in chunks)
    fin.append("theorem %s_rowOK_all : ∀ i, 1 ≤ i → i ≤ %d → %s.rowOK i = true := by\n  intro i h1 h2\n  rcases (show %s by omega) with %s\n" % (
        Tn, L, Tn, cases, " | ".join("h" for _ in chunks)))
    for k, (a, n) in enumerate(chunks):
        fin.append("  · exact List.all_eq_true.mp %s_chk_%d i (List.mem_range'_1.mpr h)\n" % (Tn, a))
    fin.append("\n")
    fin.append("/-- `d_i = dn_i / %d` from the generated table. -/\ndef d%s (i : ℕ) : ℚ := ((%s.dnAt i : ℤ) : ℚ) / %d\n\n" % (Q, nm, Tn, Q))
    fin.append(
        "theorem cert%s : DiagCert %d d%s := by\n"
        "  have h := %s.diagCert (by norm_num [%s]) (by norm_num [%s]) %s_hdn %s_hlen\n"
        "    (fun i hi => CertData.rowOK_sound %s %s_rows_len i (%s_rowOK_all i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2))\n"
        "  have e : d%s = fun i => ((%s.dnAt i : ℤ) : ℚ) / ((%s.Q : ℤ) : ℚ) := by\n"
        "    funext i; simp [d%s, %s]\n"
        "  rw [e]; exact h\n\n" % (nm, L, nm, Tn, Tn, Tn, Tn, Tn, Tn, Tn, Tn, nm, Tn, Tn, nm, Tn))
    fin.append(
        "theorem sum_d%s : ∑ i ∈ Icc 1 %d, d%s i = %d / %d := by\n"
        "  have h : ∑ i ∈ Icc 1 %d, d%s i = ((∑ i ∈ Icc 1 %d, %s.dnAt i : ℤ) : ℚ) / %d := by\n"
        "    simp only [d%s]; rw [← Finset.sum_div]; push_cast; rfl\n"
        "  rw [h, %s_dn_sum]; norm_num\n\n" % (nm, L, nm, sumd.numerator, sumd.denominator, L, nm, L, Tn, Q, nm, Tn))
    fin.append(
        "theorem prsBound_d%s : prsBound %d d%s = %d / %d := by\n"
        "  rw [prsBound_of_sum %d d%s (%d / %d) sum_d%s]\n"
        "  norm_num\n" % (nm, L, nm, bound.numerator, bound.denominator, L, nm, sumd.numerator, sumd.denominator, nm))
    if args.pin_lower:
        pn, pd = args.pin_lower.split("/")
        assert Fraction(int(pn), int(pd)) <= bound, "pinned constant exceeds the certified bound"
        fin.append("\n/-- The published PRS08 constant `%s/%s` is below the certified bound. -/\n"
                   "theorem prsBound_d%s_ge : ((%s : ℝ) / %s) ≤ prsBound %d d%s := by\n"
                   "  rw [prsBound_d%s]; norm_num\n" % (pn, pd, nm, pn, pd, L, nm, nm))
    finsrc = "".join(fin)

    return dict(tab=tabsrc, chk=chk, fin=finsrc, doc=doc_common, chunks=chunks, nm=nm, info=info, bound=bound, sumd=sumd, Tn=Tn)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json", nargs="?")
    ap.add_argument("--selftest-L", type=int, default=0)
    ap.add_argument("--module", default="P1186Cert128")
    ap.add_argument("--out-dir", default=None)
    ap.add_argument("--rows-per-chunk", type=int, default=16)
    ap.add_argument("--chunk-cost", type=int, default=0, help="balanced chunks of about this many multiply-adds (overrides --rows-per-chunk)")
    ap.add_argument("--pin-lower", default=None, help="P/Q: also emit a theorem  P/Q <= prsBound L d  (published constant)")
    ap.add_argument("--single", default=None, help="write ONE scratch file (Lib import only) instead of modules")
    ap.add_argument("--suffix", default=None, help="name suffix for defs (default: L zero-padded to 3)")
    a = ap.parse_args()
    if a.selftest_L:
        cert = selftest_certificate(a.selftest_L)
        a.json = None
    else:
        cert = json.load(open(a.json))
    r = emit(cert, a)
    nl = "\n"
    if a.single:
        body = ("import Mathlib\nimport Erdos.Proofs.P1186Cert128Lib\n\n/-!\nSCRATCH (single file)\n" + r["doc"] + "\n-/\n\nnamespace " + NS +
                "\n\nopen Finset\n\n" + r["tab"] + "\n" + "\n".join(r["chk"]) + "\n" + r["fin"] + "\nend " + NS + "\n")
        os.makedirs(os.path.dirname(os.path.abspath(a.single)), exist_ok=True)
        open(a.single, "w", encoding="utf-8", newline="\n").write(body)
        print("wrote", a.single, len(body), "bytes")
        return
    out = a.out_dir
    mod = a.module
    os.makedirs(out, exist_ok=True)
    # Tab module
    def wr(name, imports, doc, body):
        txt = ("import Mathlib\nimport Erdos.Proofs.P1186Cert128Lib\n" + "".join("import Erdos.Proofs.%s\n" % m for m in imports) +
               "\n/-!\n" + doc + "\n-/\n\nnamespace " + NS + "\n\nopen Finset\n\n" + body + "\nend " + NS + "\n")
        p = os.path.join(out, name + ".lean")
        open(p, "w", encoding="utf-8", newline="\n").write(txt)
        print("wrote", p, len(txt), "bytes")
    wr(mod + "Tab", [], "# Erdos 1186 - L = %d diagonal certificate: table (night 2, lean1186b)\n\n" % cert["L"] + r["doc"], r["tab"])
    chunk_mods = []
    for (a0, n), src in zip(r["chunks"], r["chk"]):
        cm = "%sChk%d" % (mod, a0)
        chunk_mods.append(cm)
        wr(cm, [mod + "Tab"], "# Erdos 1186 - L = %d certificate: kernel check of rows %d..%d (night 2, lean1186b)\n\n" % (cert["L"], a0, a0 + n - 1) + r["doc"], src)
    wr(mod, [mod + "Tab"] + chunk_mods,
       "# Erdos 1186 - the L = %d PRS08 diagonal certificate, checked by the kernel (night 2, lean1186b)\n\n" % cert["L"] +
       "`cert%s : DiagCert %d d%s`, `sum_d%s`, `prsBound_d%s`.\n\n" % (r["nm"], cert["L"], r["nm"], r["nm"], r["nm"]) + r["doc"], r["fin"])
    print("modules:", [mod + "Tab"] + chunk_mods + [mod])
    print("imports to add to lean/Erdos.lean (CRLF):")
    for m in [mod + "Tab"] + chunk_mods + [mod]:
        print("import Erdos.Proofs." + m)


if __name__ == "__main__":
    main()
