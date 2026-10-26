"""Regenerate every generated Lean module from the JSON data with the repository's generators, and compare.

Usage (from the repository root):  py verification/regen_check.py

The generators write into a temporary directory (nothing in the repository is touched); every regenerated file is
compared with the shipped one, ignoring CR bytes, and the set of regenerated module names must equal the set of shipped
modules of each family. What is regenerated:

  Theorem C   computation/theorem-c/lean_cert_ex.py   the 124 certificate modules P1186ExCert{1..5}* of the five
              ranges, from data/cert_region{1..5}.json, with the settings recorded in its docstring:
                --regions 1 2 4 --drows 70
                --regions 5 --prows 15 --drows 70 --tchunk 250 --tgroup 5
                --regions 3 --prows 15 --drows 70 --tchunk 250 --tgroup 6
              computation/theorem-c/gen_interface.py   P1186ExData.lean (the grids) and data/grids.json, from
                                                        data/certs_rev1186c.json
              computation/theorem-c/bath/gen_bath_tab.py   P1186ExBathTab.lean, from data/grids.json
  Theorem B   computation/theorem-b/lean_cert2.py      P1186M2Cert{64,128,256}* (10 + 21 + 76 modules), from
                                                        data/sdp_model2cuts_L{64,128,256}.json (L = 256: --cuts-per-def 800)
              computation/theorem-b/lean_cert.py       P1186Cert{128,256}{Tab,Chk*,} (10 + 59 modules), from
                                                        data/sdp_dn_L{128,256}.json (--chunk-cost 90000 --pin-lower 1675/32768)
The two Theorem B generators round a floating-point Cholesky factor (numpy) to integers. The shipped files were
reproduced with numpy 2.2.6 on Windows; a different numpy or LAPACK build could in principle round an entry
differently. That would not affect the proofs (the kernel checks whatever tables are shipped), but this check would
then report a difference.

The generators of the other modules (the hand-written libraries, the reductions and the remaining Theorem C parts) are
not part of this repository; those modules are listed at the end.
Exit status 0 iff every regenerated file is identical to the shipped one and no family has missing or extra files.
"""
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
PROOFS = ROOT / "lean" / "Erdos" / "Proofs"
TC = ROOT / "computation" / "theorem-c"
TB = ROOT / "computation" / "theorem-b"


def run(args, cwd):
    r = subprocess.run([sys.executable, "-B", *map(str, args)], cwd=str(cwd), capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    if r.returncode != 0:
        print(r.stdout[-3000:], r.stderr[-3000:])
        raise SystemExit(f"generator failed (exit {r.returncode}): {' '.join(map(str, args))}")
    return r.stdout


def same(a: pathlib.Path, b: pathlib.Path) -> bool:
    return a.read_bytes().replace(b"\r", b"") == b.read_bytes().replace(b"\r", b"")


def compare_family(label, outdir, pattern, regenerated):
    shipped = {p.name for p in PROOFS.glob("*.lean") if re.fullmatch(pattern, p.name)}
    made = {p.name for p in outdir.glob("*.lean")}
    diff = sorted(n for n in shipped & made if not same(outdir / n, PROOFS / n))
    missing, extra = sorted(shipped - made), sorted(made - shipped)
    ok = not diff and not missing and not extra
    print(f"  {label}: {len(made)} regenerated, {len(shipped)} shipped, {len(shipped & made) - len(diff)} identical"
          f"{'' if ok else f'; DIFFER {diff}; not regenerated {missing}; extra {extra}'}")
    regenerated |= shipped & made
    return ok


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    ok = True
    regenerated = set()
    with tempfile.TemporaryDirectory(prefix="regen1186_") as tmp:
        tmp = pathlib.Path(tmp)
        print("Theorem C")
        out = tmp / "c"
        out.mkdir()
        gen = TC / "lean_cert_ex.py"
        for flags in (["--regions", "1", "2", "4", "--drows", "70"],
                      ["--regions", "5", "--prows", "15", "--drows", "70", "--tchunk", "250", "--tgroup", "5"],
                      ["--regions", "3", "--prows", "15", "--drows", "70", "--tchunk", "250", "--tgroup", "6"]):
            for line in run([gen, *flags, "--out", out], TC).splitlines():
                if "mirror failures" in line:
                    print("   ", line.strip())
        ok &= compare_family("certificate modules P1186ExCert{1..5}*", out, r"P1186ExCert[1-5](Data|[PDTQ]\d+|M)?\.lean",
                             regenerated)
        # gen_interface.py and gen_bath_tab.py write to fixed places relative to their own location: run copies of
        # them in a scratch tree that has the repository's layout.
        tree = tmp / "tree"
        shutil.copytree(TC, tree / "computation" / "theorem-c", ignore=shutil.ignore_patterns("__pycache__"))
        (tree / "lean" / "Erdos" / "Proofs").mkdir(parents=True)
        tc2 = tree / "computation" / "theorem-c"
        (tc2 / "data" / "grids.json").unlink()
        print("   ", run([tc2 / "gen_interface.py", tc2 / "data" / "certs_rev1186c.json"], tc2).strip().replace("\n", "\n    "))
        gj = same(tc2 / "data" / "grids.json", TC / "data" / "grids.json")
        print(f"  computation/theorem-c/data/grids.json: {'identical' if gj else 'DIFFERS'}")
        ok &= gj
        print("   ", run([tc2 / "bath" / "gen_bath_tab.py"], tc2).strip().replace("\n", "\n    "))
        ok &= compare_family("interface data and bathtub tables", tree / "lean" / "Erdos" / "Proofs",
                             r"P1186Ex(Data|BathTab)\.lean", regenerated)
        print("Theorem B")
        for L, extra in ((64, []), (128, []), (256, ["--cuts-per-def", "800"])):
            out = tmp / f"m2_{L}"
            out.mkdir()
            run([TB / "lean_cert2.py", TB / "data" / f"sdp_model2cuts_L{L}.json", "--out-dir", out, *extra], TB)
            ok &= compare_family(f"MODEL2 certificate L = {L} (P1186M2Cert{L}*)", out, rf"P1186M2Cert{L}(\D\w*)?\.lean",
                                 regenerated)
        for L in (128, 256):
            out = tmp / f"diag_{L}"
            out.mkdir()
            run([TB / "lean_cert.py", TB / "data" / f"sdp_dn_L{L}.json", "--module", f"P1186Cert{L}", "--out-dir", out,
                 "--chunk-cost", "90000", "--pin-lower", "1675/32768"], TB)
            ok &= compare_family(f"diagonal certificate L = {L} (P1186Cert{L}*)", out, rf"P1186Cert{L}(Tab|Chk\d+)?\.lean",
                                 regenerated)
    allmods = sorted(p.name for p in PROOFS.glob("*.lean"))
    rest = [n[:-5] for n in allmods if n not in regenerated]
    print(f"regenerated byte for byte: {len(regenerated)} of {len(allmods)} modules; not regenerated here "
          f"({len(rest)}): {', '.join(rest)}")
    print("RESULT:", "ALL IDENTICAL" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
