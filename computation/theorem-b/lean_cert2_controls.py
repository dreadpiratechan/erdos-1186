"""Erdos #1186 (night 2, lean1186d): negative controls for the generated MODEL2 certificate modules.

Takes a SINGLE-FILE chunked certificate for a small L (default L = 32), made with

    py lean_cert2.py data/sdp_model2cuts_L32.json --single out/cert32_chunked.lean --cuts-per-def 40

and writes seven corrupted copies  out/ctrl32_<name>.lean .  Every one of them must be REJECTED by the kernel, at the theorem
named below (run each through the gate: `py $G --timeout 600 -- lake env lean ../problems/1186/out/ctrl32_<name>.lean`):

  row         one Cholesky entry of row 20 changed                 -> T32_rowOK_all  : decide proves `... = true` is false
  nrow        one entry of the integer matrix N (row 5) +1         -> T32_link_1     : false  (the N <-> (C8, dn, cuts) link)
  cut         one cut's mn +1, accumulators and N untouched        -> T32_sum, T32_acc_1 : false
  accmid      the intermediate accumulator accs32_2 changed        -> T32_acc_2, T32_acc_3 : false
  dn          every dn scaled by 0.99 (floor), N untouched         -> T32_sum, T32_link_*  : false
  sign        one cut's first sign flipped (product becomes -1)    -> T32_cuts_ok, T32_acc_1 : false
  consistent  one cut's mn +1 AND every accumulator recomputed     -> T32_sum and T32_link_* : false (N is not the matrix of the
              modified cut list; this is the control that shows the LINK is what ties N to the cuts)
"""
import json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lean_cert2 as G


def sub1(t, pat, repl):
    out, n = re.subn(pat, repl, t, count=1, flags=re.S)
    assert n == 1, pat
    return out


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "out", "cert32_chunked.lean")
    outdir = os.path.dirname(os.path.abspath(src))
    data = os.path.join(outdir, "sdp_model2cuts_L32.json")  # the scratch L = 32 instance (not committed)
    if not os.path.exists(data):
        data = os.path.join(HERE, "data", "sdp_model2cuts_L32.json")
    s = open(src, encoding="utf-8").read()

    def write(name, t):
        assert t != s, name
        p = os.path.join(outdir, "ctrl32_%s.lean" % name)
        open(p, "w", encoding="utf-8", newline="\n").write(t)
        print("wrote", p)

    # row: first entry of the Cholesky row 20
    write("row", sub1(s, r"(def r32_20 : List ℤ := \[)(\d+)", lambda m: m.group(1) + str(int(m.group(2)) + 50000)))
    # nrow: first entry of the integer matrix row 5
    write("nrow", sub1(s, r"(def n32_5 : List ℤ := \[)(\d+)", lambda m: m.group(1) + str(int(m.group(2)) + 1)))
    # cut: mn of the first cut +1
    cutpat = r"(def cuts32_1 : List Cut := \[⟨[^⟩]*?, )(\d+)(⟩)"
    write("cut", sub1(s, cutpat, lambda m: m.group(1) + str(int(m.group(2)) + 1) + m.group(3)))
    # accmid: first digit of the intermediate accumulator accs32_2
    write("accmid", sub1(s, r"(def accs32_2 : List ℤ := \[)(\d+)", lambda m: m.group(1) + str(int(m.group(2)) + 1)))
    # dn: scale by 0.99 (floor)
    def dn_repl(m):
        vals = [int(v) for v in m.group(2).split(",")]
        return m.group(1) + ", ".join(str(int(v * 0.99)) for v in vals) + "]"
    write("dn", sub1(s, r"(def dn32 : List ℤ := \[)([^\]]*)\]", dn_repl))
    # sign: flip the first sign of the first cut
    signpat = r"(def cuts32_1 : List Cut := \[⟨\d+, \d+, \d+, )(-?1)"
    write("sign", sub1(s, signpat, lambda m: m.group(1) + str(-int(m.group(2)))))
    # consistent: mn+1 on the first cut, all accumulators recomputed
    cert = json.load(open(data))
    cert["cuts"][0][4] += 1
    base, R, N, acc, cl, summn = G.build(cert)
    snaps = G.acc_snapshots(32, cl, 40)
    t = sub1(s, cutpat, lambda m: m.group(1) + str(int(m.group(2)) + 1) + m.group(3))
    for k in range(1, len(snaps)):
        t = sub1(t, r"(def accs32_%d : List ℤ := )\[[^\]]*\]" % k, lambda m, k=k: m.group(1) + G.lean_list_int(snaps[k - 1]))
    t = sub1(t, r"(def acc32 : List ℤ := )\[[^\]]*\]", lambda m: m.group(1) + G.lean_list_int(snaps[-1]))
    write("consistent", t)


if __name__ == "__main__":
    main()
