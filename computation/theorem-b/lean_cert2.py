"""Erdos #1186 (night 2, lean1186d): generate Lean modules that make the KERNEL check a MODEL2 Shor + triangle-cut certificate.

Input: problems/1186/data/sdp_model2cuts_L{L}.json  {"L","Q","dn","cuts":[[i,j,k,p,mn],...],"S":"num/den", ...}
(pattern p -> signs PAT[p] on the pairs (i,j), (i,k), (j,k); see MODEL2.md / verify_model2cuts.py on agent/n2s2).

The Lean side (lean/Erdos/Proofs/P1186M2CertLib.lean, namespace Erdos1186Night2M2, hand-written, NO numbers) proves

    cubeLB_of_cert : <Cert data satisfying the executable checks>  ->  CubeLB L ((sum dn + sum mn) / Q)

for the integer matrix  N = 2Q*C8 + 16 diag(dn) - 8 * sum_t mn_t sigma_t  (sigma_t = signs on the six symmetric off-diagonal
entries of the triple of cut t) built HERE only as a table.  The kernel checks (decide +kernel; none of it is trusted from Python):
  * cuts well formed (indices in 1..L, signs +-1 with product +1, mn >= 0), dn >= 0, list lengths, 48*sum mn < 2^30;
  * ACC:  accumulate L cuts = acc            (packed rows of the cut part, base 2^32 digits, one scatter pass over the cuts);
  * LINK, per row a:  sum_b (N_ab - base_ab) 2^(32 b) + 8 acc_a = 0  and every |N_ab - base_ab| < 2^30, so that
         N_ab = 2Q C8_ab + 16 dn_a [a=b] - 8 (cut part)_ab    for ALL b   (injectivity of the base-2^32 expansion);
  * DOMINANCE: integer lower-triangular rows C (approximate Cholesky factor of N at scale S = t^2), E = S N - C C^T, every row
         of E diagonally dominant (sum_j |E_ij| <= 2 E_ii).  Then S x^T N x = sum_k (C^T x)_k^2 + x^T E x >= 0.
The rounding in this script is irrelevant to soundness: everything is re-checked by the kernel and, here, by exact Python ints
that mirror the Lean functions (`Cert.rowOK`, `Cert.linkOK`, `accumulate`).

usage:
  py lean_cert2.py data/sdp_model2cuts_L128.json --out-dir ../../lean/Erdos/Proofs        (modules P1186M2Cert128*.lean)
  py lean_cert2.py data/sdp_model2cuts_L32.json --single out/cert32_single.lean            (scratch; imports only the libs)
"""
import argparse, json, os, sys
from fractions import Fraction
import numpy as np

PAT = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
NS = "Erdos1186Night2M2"


def K4(L, p, q):
    m = 2 * q - p - 1
    if 1 <= m <= L - 2:
        return 4
    if m == 0 or m == L - 1:
        return 3
    if m == -1 or m == L:
        return 1
    return 0


def C8(L, p, q):
    return K4(L, p, q) + K4(L, q, p) + (8 if p == q else 0) + 2


def Bp(b):
    return 1 << (32 * b)


def build(cert):
    L, Q, dn, cuts = cert["L"], cert["Q"], cert["dn"], cert["cuts"]
    assert len(dn) == L and all(isinstance(v, int) and v >= 0 for v in dn)
    base = [[2 * Q * C8(L, a, b) + (16 * dn[a - 1] if a == b else 0) for b in range(1, L + 1)] for a in range(1, L + 1)]
    R = [[0] * L for _ in range(L)]  # rowvec (sum of cut contributions), 0-indexed
    acc = [0] * L
    cl = []
    summn = 0
    for (i, j, k, p, mn) in cuts:
        s1, s2, s3 = PAT[p]
        assert 1 <= i <= L and 1 <= j <= L and 1 <= k <= L and mn >= 0 and s1 * s2 * s3 == 1
        cl.append((i, j, k, s1, s2, s3, mn))
        summn += mn
        for (x, y, s) in ((i, j, s1), (i, k, s2), (j, k, s3)):
            R[x - 1][y - 1] += mn * s
            R[y - 1][x - 1] += mn * s
        # mirror of Lean cutAcc
        acc[i - 1] += mn * (s1 * Bp(j) + s2 * Bp(k))
        acc[j - 1] += mn * (s1 * Bp(i) + s3 * Bp(k))
        acc[k - 1] += mn * (s2 * Bp(i) + s3 * Bp(j))
    N = [[base[a][b] - 8 * R[a][b] for b in range(L)] for a in range(L)]
    assert all(N[a][b] == N[b][a] for a in range(L) for b in range(a))
    return base, R, N, acc, cl, summn


def acc_snapshots(L, cl, ck):
    """Accumulator after each chunk of ck cuts (mirror of foldl cutAcc); the last one is the full `acc`."""
    a = [0] * L
    snaps = []
    for idx, (i, j, k, s1, s2, s3, mn) in enumerate(cl, 1):
        a[i - 1] += mn * (s1 * Bp(j) + s2 * Bp(k))
        a[j - 1] += mn * (s1 * Bp(i) + s3 * Bp(k))
        a[k - 1] += mn * (s2 * Bp(i) + s3 * Bp(j))
        if idx % ck == 0 or idx == len(cl):
            snaps.append(list(a))
    return snaps


def check_link(L, base, N, acc):
    """Mirror of Cert.linkOK for every row."""
    for a in range(L):
        s = sum((N[a][b] - base[a][b]) * Bp(b + 1) for b in range(L)) + 8 * acc[a]
        assert s == 0, "link packed sum nonzero in row %d" % (a + 1)
        assert all(abs(N[a][b] - base[a][b]) < 2 ** 30 for b in range(L)), "link bound violated"


def exact_E(N, Cl, S):
    L = len(N)
    C = np.zeros((L, L), dtype=object)
    for i in range(L):
        for k in range(i + 1):
            C[i, k] = int(Cl[i][k])
    G = C.dot(C.T)
    Nn = np.array(N, dtype=object)
    return S * Nn - G


def dominant(E):
    """Mirror of Cert.rowOK: sum_j |E_ij| <= 2 E_ii for all i; returns (ok, min margin)."""
    L = E.shape[0]
    worst = None
    for i in range(L):
        m = 2 * E[i, i] - sum(abs(v) for v in E[i])
        worst = m if worst is None or m < worst else worst
    return worst >= 0, worst


def find_rounded_cholesky(N, tmin=1 << 6, tmax=1 << 44, eps_frac=0.9):
    L = len(N)
    Nf = np.array([[float(v) for v in row] for row in N], dtype=np.float64)
    lam = float(np.linalg.eigvalsh(Nf)[0])
    if lam <= 0:
        raise SystemExit("float64 lambda_min(N) = %.3e <= 0: not positive definite" % lam)
    Lc = np.linalg.cholesky(Nf - eps_frac * lam * np.eye(L))
    t = tmin
    while t <= tmax:
        Cl = [[int(round(float(t) * Lc[i][k])) for k in range(i + 1)] for i in range(L)]
        S = t * t
        E = exact_E(N, Cl, S)
        ok, margin = dominant(E)
        if ok:
            return Cl, S, t, E, margin, lam
        t *= 2
    raise SystemExit("no scale t <= 2^44 gave a diagonally dominant residual")


def lean_list_int(xs):
    return "[" + ", ".join(str(int(v)) for v in xs) + "]"


def lean_cut(c):
    return "⟨%d, %d, %d, %d, %d, %d, %d⟩" % c


def balanced_row_chunks(L, cost_fn, target):
    chunks, a0, acc = [], 1, 0
    for i in range(1, L + 1):
        acc += cost_fn(i)
        if acc >= target or i == L:
            chunks.append((a0, i - a0 + 1))
            a0, acc = i + 1, 0
    return chunks


def emit(cert, args):
    L, Q = cert["L"], cert["Q"]
    dn = cert["dn"]
    base, R, N, acc, cl, summn = build(cert)
    sumdn = sum(dn)
    sigma = Fraction(sumdn + summn, Q)
    if "S" in cert:
        assert sigma == Fraction(cert["S"]), "sigma %s != json S %s" % (sigma, cert["S"])
    check_link(L, base, N, acc)
    SM = 48 * summn
    assert SM < 2 ** 30
    Cl, S, t, E, margin, lam = find_rounded_cholesky(N, eps_frac=args.eps_frac)
    okdom, worst = dominant(E)
    assert okdom
    assert all(E[i, j] == E[j, i] for i in range(L) for j in range(L))
    info = ("L=%d Q=%d  #cuts=%d  sum dn=%d  sum mn=%d  sigma=(sum dn+sum mn)/Q=%s=%.6f ; lambda_min(N)=%.4f ; t=%d S=t^2=%d ; "
            "max|C|=%d ; min row margin 2E_ii - sum|E_ij| = %d (exact)" % (
                L, Q, len(cl), sumdn, summn, sigma, float(sigma), lam, t, S, max(abs(v) for r in Cl for v in r), worst))
    print(info)
    nm = str(L)
    Tn = "T" + nm
    pref = "P1186M2Cert" + nm
    doc = ("Generated by `problems/1186/lean_cert2.py` from `sdp_model2cuts_L%d.json` (no hand-typed numbers).  %s\n"
           "Statement fidelity: the final theorem is `CubeLB %d (%d / %d)` for the shared `CubeLB`/`C8`/`K4` definitions of `P1186M2.lean`; "
           "the link between the integer table and (C8, dn, cuts) is checked by the kernel (`Cert.linkOK`, `accumulate`), not assumed."
           % (L, info, L, sigma.numerator, sigma.denominator))

    # ---- sources of the individual modules (bodies, without header) ----
    cutsrc = ["/-- The diagonal numerators: `d_i = dn_i / %d`. -/\ndef dn%s : List ℤ := %s\n" % (Q, nm, lean_list_int(dn))]
    ck = args.cuts_per_def
    names = []
    for k in range(0, len(cl), ck):
        nmk = "cuts%s_%d" % (nm, k // ck + 1)
        names.append(nmk)
        cutsrc.append("def %s : List Cut := [%s]\n" % (nmk, ", ".join(lean_cut(c) for c in cl[k:k + ck])))
    cutsrc.append("/-- The triangle cuts `(i, j, k, s1, s2, s3, mn)`. -/\ndef cuts%s : List Cut := %s\n" % (nm, " ++ ".join(names) if names else "[]"))
    cutsrc = "".join(cutsrc)

    nrsrc = []
    for a in range(L):
        nrsrc.append("def n%s_%d : List ℤ := %s\n" % (nm, a + 1, lean_list_int(N[a])))
    nrsrc.append("/-- The integer table `N` (row `a` = entries `N_a1 .. N_aL`). -/\ndef nrows%s : List (List ℤ) := [%s]\n" % (
        nm, ", ".join("n%s_%d" % (nm, a) for a in range(1, L + 1))))
    nrsrc = "".join(nrsrc)

    rsrc = []
    for i, r in enumerate(Cl, 1):
        rsrc.append("def r%s_%d : List ℤ := %s\n" % (nm, i, lean_list_int(r)))
    rsrc.append("/-- Rows of the integer lower-triangular factor `C` (row `i` has `i` entries), scale `S = %d^2`. -/\n"
                "def rows%s : List (List ℤ) := [%s]\n" % (t, nm, ", ".join("r%s_%d" % (nm, i) for i in range(1, L + 1))))
    rsrc = "".join(rsrc)

    tab = []
    tab.append("/-- The certificate data. -/\ndef %s : Cert :=\n  { L := %d, Q := %d, S := %d, dn := dn%s, cuts := cuts%s, nrows := nrows%s, rows := rows%s, acc := acc%s }\n" % (
        Tn, L, Q, S, nm, nm, nm, nm, nm))
    tab.append("theorem %s_rows_len : %s.rows.length = %d := by decide +kernel\n" % (Tn, Tn, L))
    tab.append("theorem %s_nrow_len : ∀ i ∈ Icc 1 %d, (%s.nrow i).length = %d := by decide +kernel\n" % (Tn, L, Tn, L))
    tab.append("theorem %s_hlen : ∀ i ∈ Icc 1 %d, (%s.row i).length ≤ %d := by decide +kernel\n" % (Tn, L, Tn, L))
    tab.append("theorem %s_hdn : ∀ i ∈ Icc 1 %d, 0 ≤ %s.dnAt i := by decide +kernel\n" % (Tn, L, Tn))
    if len(cl) <= args.cheap_chunk_above:
        tab.append("theorem %s_cuts_ok : ∀ t ∈ %s.cuts, Cut.ok %d t = true := by decide +kernel\n" % (Tn, Tn, L))
        tab.append("theorem %s_SM : 48 * (%s.cuts.map Cut.mn).sum < 2 ^ 30 := by decide +kernel\n" % (Tn, Tn))
        tab.append("theorem %s_sum : (∑ i ∈ Icc 1 %s.L, %s.dnAt i) + (%s.cuts.map Cut.mn).sum = %d := by decide +kernel\n" % (
            Tn, Tn, Tn, Tn, sumdn + summn))
    else:
        # one `decide` over a list of > ~4000 cuts hits the kernel's recursion depth (as the ACC fold does): check per chunk,
        # then combine with `List.forall_mem_append` / `List.sum_append` (the chunk sums below are re-checked by the kernel)
        ksums = [sum(c[6] for c in cl[k:k + ck]) for k in range(0, len(cl), ck)]
        assert sum(ksums) == summn
        kn = len(ksums)
        for ki in range(1, kn + 1):
            tab.append("theorem %s_ok_%d : ∀ t ∈ cuts%s_%d, Cut.ok %d t = true := by decide +kernel\n" % (Tn, ki, nm, ki, L))
            tab.append("theorem %s_ms_%d : (cuts%s_%d.map Cut.mn).sum = %d := by decide +kernel\n" % (Tn, ki, nm, ki, ksums[ki - 1]))
        app = " ++ ".join("cuts%s_%d" % (nm, ki) for ki in range(1, kn + 1))
        tab.append("theorem %s_cuts_ok : ∀ t ∈ %s.cuts, Cut.ok %d t = true := by\n"
                   "  show ∀ t ∈ %s, Cut.ok %d t = true\n"
                   "  simp only [List.forall_mem_append, and_assoc]\n"
                   "  exact ⟨%s⟩\n" % (Tn, Tn, L, app, L, ", ".join("%s_ok_%d" % (Tn, ki) for ki in range(1, kn + 1))))
        tab.append("theorem %s_msum : (%s.cuts.map Cut.mn).sum = %d := by\n"
                   "  show ((%s).map Cut.mn).sum = %d\n"
                   "  simp only [List.map_append, List.sum_append, %s]\n"
                   "  all_goals norm_num\n" % (Tn, Tn, summn, app, summn, ", ".join("%s_ms_%d" % (Tn, ki) for ki in range(1, kn + 1))))
        tab.append("theorem %s_SM : 48 * (%s.cuts.map Cut.mn).sum < 2 ^ 30 := by\n  rw [%s_msum]; norm_num\n" % (Tn, Tn, Tn))
        tab.append("theorem %s_sum : (∑ i ∈ Icc 1 %s.L, %s.dnAt i) + (%s.cuts.map Cut.mn).sum = %d := by\n"
                   "  rw [%s_msum]; decide +kernel\n" % (Tn, Tn, Tn, Tn, sumdn + summn, Tn))
    tabsrc = "".join(tab)

    snaps = acc_snapshots(L, cl, ck)
    assert snaps[-1] == acc, "chunked accumulator mismatch"
    nch = len(snaps)
    zero = "List.replicate %d 0" % L

    def accname(k):  # k = 0 .. nch
        return zero if k == 0 else ("acc%s" % nm if k == nch else "accs%s_%d" % (nm, k))

    acctab = ["/-- Accumulator after the first `k` chunks of cuts (chunks of %d cuts; the kernel's recursion depth limits one fold). -/\n" % ck]
    for k in range(1, nch):
        acctab.append("def accs%s_%d : List ℤ := %s\n" % (nm, k, lean_list_int(snaps[k - 1])))
    acctab.append("/-- The packed cut rows: `acc_a = sum_b (cut part)_ab 2^(32 b)`. -/\ndef acc%s : List ℤ := %s\n" % (nm, lean_list_int(acc)))
    acctabsrc = "".join(acctab)
    accthms = []
    for k in range(1, nch + 1):
        accthms.append("theorem %s_acc_%d : List.foldl cutAcc (%s) cuts%s_%d = %s := by decide +kernel\n" % (
            Tn, k, accname(k - 1), nm, k, accname(k)))
    accfinal = ("theorem %s_acc : accumulate %d %s.cuts = %s.acc := by\n"
                "  show accumulate %d (%s) = acc%s\n"
                "  simp only [accumulate, List.foldl_append]\n"
                "  rw [%s]\n" % (Tn, L, Tn, Tn, L, " ++ ".join("cuts%s_%d" % (nm, k) for k in range(1, nch + 1)), nm,
                                  ", ".join("%s_acc_%d" % (Tn, k) for k in range(1, nch + 1))))
    apm = args.acc_per_module
    achunks = [(k, min(apm, nch - k + 1)) for k in range(1, nch + 1, apm)]
    accsrcs = ["".join(accthms[k - 1:k - 1 + n]) for (k, n) in achunks]

    lchunks = [(a, min(args.link_rows, L - a + 1)) for a in range(1, L + 1, args.link_rows)]
    lsrc = []
    for (a, n) in lchunks:
        lsrc.append("/-- rows `%d..%d` of `%s` pass the LINK check (kernel evaluation). -/\n"
                    "theorem %s_link_%d : (List.range' %d %d).all %s.linkOK = true := by decide +kernel\n" % (
                        a, a + n - 1, Tn, Tn, a, a, n, Tn))

    dchunks = balanced_row_chunks(L, lambda i: sum(min(i, j) for j in range(1, L + 1)), args.chunk_cost)
    dsrc = []
    for (a, n) in dchunks:
        dsrc.append("/-- rows `%d..%d` of `%s` are diagonally dominant (kernel evaluation). -/\n"
                    "theorem %s_chk_%d : (List.range' %d %d).all %s.rowOK = true := by decide +kernel\n" % (
                        a, a + n - 1, Tn, Tn, a, a, n, Tn))

    def assemble(chunks, tag, hyp, pred):
        cases = " ∨ ".join("(%d ≤ i ∧ i < %d)" % (a, a + n) for (a, n) in chunks)
        s = ["theorem %s_%s_all : ∀ i, 1 ≤ i → i ≤ %d → %s.%s i = true := by\n  intro i h1 h2\n  rcases (show %s by omega) with %s\n" % (
            Tn, tag, L, Tn, pred, cases, " | ".join("h" for _ in chunks))]
        for (a, n) in chunks:
            s.append("  · exact List.all_eq_true.mp %s_%s_%d i (List.mem_range'_1.mpr h)\n" % (Tn, hyp, a))
        return "".join(s)

    fin = [accfinal, "\n", assemble(lchunks, "link", "link", "linkOK"), "\n", assemble(dchunks, "rowOK", "chk", "rowOK"), "\n"]
    fin.append(
        "/-- **Kernel-checked MODEL2 certificate for `L = %d`**: `xᵀ C x ≥ -%d/%d` on `[-1,1]^%d` (shared `CubeLB`). -/\n"
        "theorem cubeLB%s : CubeLB %d (%d / %d) := by\n"
        "  have h := cubeLB_of_cert %s (by show (0 : ℤ) < %d; norm_num) (by show (0 : ℤ) < %d; norm_num)\n"
        "    %s_rows_len %s_nrow_len %s_hlen %s_hdn\n"
        "    %s_cuts_ok %s_acc %s_SM\n"
        "    (fun i hi => %s_link_all i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)\n"
        "    (fun i hi => %s_rowOK_all i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)\n"
        "  have e : ((((∑ i ∈ Icc 1 %s.L, %s.dnAt i) + (%s.cuts.map Cut.mn).sum : ℤ) : ℚ) / (%s.Q : ℚ)) = %d / %d := by\n"
        "    rw [%s_sum]\n"
        "    show ((%d : ℤ) : ℚ) / ((%d : ℤ) : ℚ) = %d / %d\n"
        "    norm_num\n"
        "  rw [e] at h\n"
        "  exact h\n" % (L, sigma.numerator, sigma.denominator, L, nm, L, sigma.numerator, sigma.denominator,
                         Tn, Q, S, Tn, Tn, Tn, Tn, Tn, Tn, Tn, Tn, Tn, Tn, Tn, Tn, Tn, sigma.numerator, sigma.denominator, Tn,
                         sumdn + summn, Q, sigma.numerator, sigma.denominator))
    finsrc = "".join(fin)
    return dict(doc=doc, info=info, cut=cutsrc, nr=nrsrc, r=rsrc, tab=tabsrc, acctab=acctabsrc, accs=accsrcs, achunks=achunks,
                link=lsrc, lchunks=lchunks,
                dom=dsrc, dchunks=dchunks, fin=finsrc, nm=nm, Tn=Tn, pref=pref, sigma=sigma)


IMPORTS = "import Mathlib\nimport Erdos.Proofs.P1186M2\nimport Erdos.Proofs.P1186Cert128Lib\nimport Erdos.Proofs.P1186M2CertLib\n"


def header(extra, title, doc):
    return IMPORTS + "".join("import Erdos.Proofs.%s\n" % m for m in extra) + \
        "\n/-!\n" + title + "\n\n" + doc + "\n-/\n\nnamespace " + NS + "\n\nopen Finset Erdos1186Night2\n\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json")
    ap.add_argument("--out-dir", default=None)
    ap.add_argument("--single", default=None, help="write ONE scratch file instead of modules")
    ap.add_argument("--chunk-cost", type=int, default=90000, help="dominance chunks of about this many multiply-adds")
    ap.add_argument("--link-rows", type=int, default=32, help="rows per LINK module")
    ap.add_argument("--cuts-per-def", type=int, default=400,
                    help="cuts per list def = cuts per ACC fold (one kernel fold is limited to about 1000 cuts at L = 128 by recursion depth)")
    ap.add_argument("--acc-per-module", type=int, default=3, help="ACC chunk theorems per module")
    ap.add_argument("--cheap-chunk-above", type=int, default=5000,
                    help="above this many cuts the cuts_ok / sum checks are done per chunk (recursion depth); L = 64, 128 are below")
    ap.add_argument("--eps-frac", type=float, default=0.9)
    a = ap.parse_args()
    cert = json.load(open(a.json))
    r = emit(cert, a)
    if a.single:
        body = (IMPORTS + "\n/-!\nSCRATCH (single file)\n" + r["doc"] + "\n-/\n\nnamespace " + NS + "\n\nopen Finset Erdos1186Night2\n\n" +
                r["cut"] + "\n" + r["acctab"] + "\n" + r["nr"] + "\n" + r["r"] + "\n" + r["tab"] + "\n" + "\n".join(r["accs"]) + "\n" +
                "\n".join(r["link"]) + "\n" +
                "\n".join(r["dom"]) + "\n" + r["fin"] + "\nend " + NS + "\n")
        os.makedirs(os.path.dirname(os.path.abspath(a.single)), exist_ok=True)
        open(a.single, "w", encoding="utf-8", newline="\n").write(body)
        print("wrote", a.single, len(body), "bytes")
        return
    out = a.out_dir
    pref = r["pref"]
    os.makedirs(out, exist_ok=True)
    written = []

    def wr(name, extra, title, body):
        txt = header(extra, title, r["doc"]) + body + "\nend " + NS + "\n"
        p = os.path.join(out, name + ".lean")
        open(p, "w", encoding="utf-8", newline="\n").write(txt)
        written.append(name)
        print("wrote", p, len(txt), "bytes")

    L = cert["L"]
    wr(pref + "Cuts", [], "# Erdos 1186 - MODEL2 certificate L = %d: dn and triangle cuts (night 2, lean1186d)" % L, r["cut"])
    wr(pref + "Nrows", [], "# Erdos 1186 - MODEL2 certificate L = %d: the integer table N (night 2, lean1186d)" % L, r["nr"])
    wr(pref + "Rows", [], "# Erdos 1186 - MODEL2 certificate L = %d: integer Cholesky rows (night 2, lean1186d)" % L, r["r"])
    wr(pref + "AccTab", [], "# Erdos 1186 - MODEL2 certificate L = %d: packed cut rows and intermediate accumulators (night 2, lean1186d)" % L, r["acctab"])
    wr(pref + "Tab", [pref + "Cuts", pref + "Nrows", pref + "Rows", pref + "AccTab"],
       "# Erdos 1186 - MODEL2 certificate L = %d: assembled data and cheap kernel checks (night 2, lean1186d)" % L, r["tab"])
    amods, lmods, dmods = [], [], []
    for (k0, n), src in zip(r["achunks"], r["accs"]):
        m = "%sAcc%d" % (pref, k0)
        amods.append(m)
        wr(m, [pref + "Cuts", pref + "AccTab"],
           "# Erdos 1186 - MODEL2 certificate L = %d: ACC check, cut chunks %d..%d (night 2, lean1186d)" % (L, k0, k0 + n - 1), src)
    for (a0, n), src in zip(r["lchunks"], r["link"]):
        m = "%sLink%d" % (pref, a0)
        lmods.append(m)
        wr(m, [pref + "Tab"], "# Erdos 1186 - MODEL2 certificate L = %d: LINK check, rows %d..%d (night 2, lean1186d)" % (L, a0, a0 + n - 1), src)
    for (a0, n), src in zip(r["dchunks"], r["dom"]):
        m = "%sChk%d" % (pref, a0)
        dmods.append(m)
        wr(m, [pref + "Tab"], "# Erdos 1186 - MODEL2 certificate L = %d: dominance check, rows %d..%d (night 2, lean1186d)" % (L, a0, a0 + n - 1), src)
    wr(pref, [pref + "Tab"] + amods + lmods + dmods,
       "# Erdos 1186 - the L = %d MODEL2 Shor + triangle-cut certificate, checked by the kernel (night 2, lean1186d)\n\n`cubeLB%d : CubeLB %d (%d / %d)`." % (
           L, L, L, r["sigma"].numerator, r["sigma"].denominator), r["fin"])
    print("modules:", written)
    print("imports to add to lean/Erdos.lean (CRLF):")
    for m in [pref + "Cuts", pref + "Nrows", pref + "Rows", pref + "AccTab", pref + "Tab"] + amods + lmods + dmods + [pref]:
        print("import Erdos.Proofs." + m)


if __name__ == "__main__":
    main()
