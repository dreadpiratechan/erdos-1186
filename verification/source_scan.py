"""Source scan of the Lean development: module closure, hashes, and forbidden constructs.

Usage (from the repository root):  py verification/source_scan.py

1. Closure.  Starting from the imports of lean/Erdos1186.lean, follows `import Erdos.Proofs.X` edges and checks that the
   import closure is exactly the set of files in lean/Erdos/Proofs/ (342 modules, none missing, none unused), and that
   the only other import is `Mathlib`.
2. Hashes.  Checks every module against verification/lean_modules.sha256 (SHA-256 and size of each file as copied
   from the research repository; see docs/PROVENANCE.md), and that every module has LF line endings only.
3. Forbidden constructs.  Removes comments, docstrings and string literals, then searches the remaining code for
   the words below. Any hit fails the scan.
     sorry admit                         unfinished proofs
     native_decide +native ofReduceBool trustCompiler
                                         evaluation by the compiler instead of the kernel
     axiom                               new axioms
     skipKernelTC debug.                 options that switch off kernel checking
     unsafe implemented_by extern        code the kernel does not see
     run_cmd run_elab run_meta #eval elab macro syntax initialize
                                         metaprogramming inside the project modules
   Occurrences of these words inside comments are listed for information (they are not code).
The axiom audit (verification/AxiomAudit.lean) is the authoritative test for sorry, native_decide and added axioms;
this scan is a second, independent test on the source text, and the only one that sees `skipKernelTC`.
Exit status 0 iff every check passes.
"""
import hashlib
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
SRC = LEAN / "Erdos" / "Proofs"
HASHES = ROOT / "verification" / "lean_modules.sha256"
EXPECTED = 342

FORBIDDEN = ["sorry", "admit", "native_decide", "+native", "ofReduceBool", "trustCompiler", "axiom", "skipKernelTC",
             "debug.", "unsafe", "implemented_by", "extern", "run_cmd", "run_elab", "run_meta", "#eval", "elab",
             "macro", "syntax", "initialize"]
IDCHARS = re.compile(r"[\w'!?.₀-₟ᵢ-ᵪⁱⁿ]")
WORD = re.compile("|".join(r"(?<![\w'.])" + re.escape(w) + (r"(?![\w'])" if w[-1].isalnum() else "") for w in FORBIDDEN))
IMPORT = re.compile(r"^import\s+(\S+)\s*$", re.M)


def split_code_comments(text):
    """Return (code, comments): the source with comments/docstrings/strings replaced by spaces (newlines kept),
    and the text of the comments and docstrings."""
    code, comm = [], []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            comm.append(text[i:j])
            code.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if depth:
                raise ValueError("unterminated block comment")
            comm.append(text[i:j])
            code.append(re.sub(r"[^\n]", " ", text[i:j]))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            if j >= n:
                raise ValueError("unterminated string literal")
            code.append('"' + re.sub(r"[^\n]", " ", text[i + 1:j]) + '"')
            i = j + 1
        elif c == "'" and (i == 0 or not IDCHARS.match(text[i - 1])):
            m = re.compile(r"'(\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4}|\\.|[^\\'\n])'").match(text, i)
            if m:
                code.append("'" + " " * (m.end() - i - 2) + "'")
                i = m.end()
            else:
                code.append(c)
                i += 1
        else:
            code.append(c)
            i += 1
    return "".join(code), "\n".join(comm)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    ok = True
    files = {p.stem: p for p in SRC.glob("*.lean")}
    roots = [m.split(".")[-1] for m in IMPORT.findall((LEAN / "Erdos1186.lean").read_text(encoding="utf-8"))]
    seen, stack, other = {}, list(roots), set()
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        if m not in files:
            print(f"MISSING module Erdos.Proofs.{m}")
            ok = False
            continue
        seen[m] = files[m]
        for imp in IMPORT.findall(files[m].read_text(encoding="utf-8")):
            if imp.startswith("Erdos.Proofs."):
                stack.append(imp[len("Erdos.Proofs."):])
            else:
                other.add(imp)
    unused = sorted(set(files) - set(seen))
    print(f"roots (lean/Erdos1186.lean): {', '.join(roots)}")
    print(f"import closure: {len(seen)} modules; files in lean/Erdos/Proofs: {len(files)}; unused files: {unused or 'none'}")
    print(f"imports from outside the project: {sorted(other)}")
    ok &= len(seen) == len(files) == EXPECTED and not unused and other == {"Mathlib"}

    listed = {}
    for line in HASHES.read_text(encoding="utf-8").splitlines():
        h, name, size = line.split("  ")
        listed[name] = (h, int(size))
    bad, crlf, total = [], [], 0
    for m, p in sorted(files.items()):
        b = p.read_bytes()
        total += len(b)
        if b"\r" in b:
            crlf.append(p.name)
        if listed.get(p.name) != (hashlib.sha256(b).hexdigest(), len(b)):
            bad.append(p.name)
    unlisted = sorted(set(listed) - {p.name for p in files.values()})
    print(f"hashes: {len(files)} files, {total} bytes; {len(bad)} differ from {HASHES.name}; "
          f"{len(unlisted)} listed but absent; {len(crlf)} with CR bytes")
    for x in bad + unlisted + crlf:
        print("  ", x)
    ok &= not bad and not unlisted and not crlf and len(listed) == EXPECTED

    code_hits, comment_hits = [], []
    for m, p in sorted(files.items()):
        text = p.read_text(encoding="utf-8")
        code, comm = split_code_comments(text)
        for no, line in enumerate(code.splitlines(), 1):
            for w in WORD.findall(line):
                code_hits.append(f"{p.name}:{no}: [{w}] {text.splitlines()[no - 1].strip()[:140]}")
        for w in WORD.findall(comm):
            comment_hits.append((p.name, w))
    print(f"forbidden words in code (comments, docstrings and strings removed): {len(code_hits)}")
    for h in code_hits:
        print("  ", h)
    ok &= not code_hits
    by = {}
    for name, w in comment_hits:
        by.setdefault(w, set()).add(name)
    print(f"the same words inside comments or docstrings (information only): {len(comment_hits)} occurrences: "
          + ("; ".join(f"{w} x{sum(1 for _, x in comment_hits if x == w)} in {len(fs)} files" for w, fs in sorted(by.items()))
             or "none"))
    print("RESULT:", "ALL OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
