#!/usr/bin/env python3
"""Statement-fidelity check for the Erdos 1186 manuscript.

Compares, token by token (whitespace-normalised), the definitions and the statement of `prs_bounds` shipped in the
Lean development against the upstream formal-conjectures file they were copied from.

    py -I fidelity_check.py <upstream 1186.lean> <P1186.lean> <P1186LowMain.lean> [<P1186M2Main.lean> [<P1186ExFinal.lean>]]

The optional fifth file (Theorem C of Section 10, the claim's formalisation) is compared with the upstream
`erdos_1186.variants.prs_conjecture`.

Upstream pin used for the manuscript: formal-conjectures commit c83a94d785d0fb3b9b9a2a94e8ffff8cce76a346
(2026-10-22), file FormalConjectures/ErdosProblems/1186.lean, namespace `Erdos1186`.  The development uses the namespace
`Erdos1186Day`; nothing else may differ.

Exit status 0 iff every comparison below prints OK.
"""
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path


def norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def block(text: str, name: str) -> str:
    """The docstring and the body of `def name`, as one string (ends at the first blank line after the def)."""
    m = re.search(r"(/--(?:(?!-/).)*?-/)\s*\n((?:noncomputable )?def " + re.escape(name) + r"\b.*?)(?=\n\s*\n|\Z)",
                  text, re.S)
    if not m:
        raise SystemExit(f"definition {name} not found")
    return m.group(1) + "\n" + m.group(2)


def statement(text: str, name: str) -> str:
    """The type of `theorem name` (between the name and `:=`), whitespace-normalised."""
    m = re.search(r"theorem " + re.escape(name) + r"\b(.*?):=", text, re.S)
    if not m:
        raise SystemExit(f"theorem {name} not found")
    return norm(m.group(1))


def main(argv: list[str]) -> int:
    sys.stdout.reconfigure(encoding="utf-8")
    if len(argv) < 4:
        print(__doc__)
        return 2
    up = Path(argv[1]).read_text(encoding="utf-8")
    dev = Path(argv[2]).read_text(encoding="utf-8")
    low = Path(argv[3]).read_text(encoding="utf-8")
    ok = True

    print("== definitions (docstring + body), upstream Erdos1186 vs development Erdos1186Day")
    for name in ("monoCount", "minMonoCount", "δ"):
        a, b = norm(block(up, name)), norm(block(dev, name))
        same = a == b
        ok &= same
        print(f"  {name:13s} {'OK  ' if same else 'DIFF'} sha256[:12]={hashlib.sha256(a.encode()).hexdigest()[:12]}"
              f" ({len(a)} chars)")
        if not same:
            print("    upstream :", a)
            print("    developed:", b)

    print("== namespace and opens")
    for needle, label in (("namespace Erdos1186\n", "upstream namespace"), ("open Filter Asymptotics", "upstream open")):
        present = needle in up
        ok &= present
        print(f"  {label:20s} {'OK  ' if present else 'MISSING'}")
    present = "namespace Erdos1186Day" in dev and "open Filter Asymptotics" in dev
    ok &= present
    print(f"  {'development':20s} {'OK  ' if present else 'MISSING'} (namespace Erdos1186Day, open Filter Asymptotics)")

    print("== theorem statements (text between the name and `:=`)")
    pairs = [("erdos_1186.variants.prs_bounds", up, low, "P1186LowMain.lean"),
             ("erdos_1186.variants.van_der_waerden", up, dev, "P1186.lean"),
             ("erdos_1186.variants.probabilistic", up, dev, "P1186.lean")]
    for name, u, d, fname in pairs:
        a, b = statement(u, name), statement(d, name)
        same = a == b
        ok &= same
        print(f"  {name}: {'OK  ' if same else 'DIFF'}   {a}")
        if not same:
            print("    developed:", b)

    # the upstream statements the development does NOT claim: they must still be `sorry` upstream (status of the pin)
    print("== upstream status at the pin (informational)")
    for name in ("erdos_1186.variants.prs_bounds", "erdos_1186.variants.van_der_waerden",
                 "erdos_1186.variants.probabilistic", "erdos_1186.variants.prs_conjecture", "erdos_1186"):
        m = re.search(r"theorem " + re.escape(name) + r"\b.*?:=\s*by\s*(sorry)?", up, re.S)
        print(f"  upstream {name}: {'sorry' if m and m.group(1) else 'proved'}")

    if len(argv) > 4:
        m2 = Path(argv[4]).read_text(encoding="utf-8")
        print("== Theorem B statements present in the development")
        for want in ("(14324135 / 268435456 : ℝ) ≤ δ 3", "(1788837 / 33554432 : ℝ) ≤ δ 3",
                     "(1782409 / 33554432 : ℝ) ≤ δ 3"):
            present = want in m2
            ok &= present
            print(f"  {'OK  ' if present else 'MISSING'} {want}")

    if len(argv) > 5:
        # Section 10 / Theorem C: the final statement of the claim's formalisation must be the upstream `prs_conjecture`
        fin = Path(argv[5]).read_text(encoding="utf-8")
        print("== Theorem C statement (P1186ExFinal.lean) vs upstream erdos_1186.variants.prs_conjecture")
        name = "erdos_1186.variants.prs_conjecture"
        a, b = statement(up, name), statement(fin, name)
        same = a == b
        ok &= same
        print(f"  {name}: {'OK  ' if same else 'DIFF'}   {a}")
        if not same:
            print("    developed:", b)
        present = "namespace Erdos1186Day" in fin
        ok &= present
        print(f"  {'namespace':20s} {'OK  ' if present else 'MISSING'} (namespace Erdos1186Day)")
        nohyp = a.startswith(":") and b.startswith(":")  # no binders before the colon: no hypotheses
        ok &= nohyp
        print(f"  {'no binders':20s} {'OK  ' if nohyp else 'FAILED'}")

    print("RESULT:", "ALL OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
