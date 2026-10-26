"""Write or check MANIFEST.sha256 for this repository.

Usage (from the repository root, on a fresh checkout; running verification/run_all.sh rewrites the logs):
    py verification/make_manifest.py          # (re)write MANIFEST.sha256
    py verification/make_manifest.py --check  # verify every listed file; exit 1 on any mismatch or missing file
    py verification/make_manifest.py --check --skip-logs   # the same, ignoring verification/logs/ (run_all.sh uses this,
                                                           # so that it also passes after an earlier run rewrote the logs)

Text files are hashed with LF line endings (CR bytes before LF removed), so the manifest is the same on any checkout;
binary files are hashed as stored. (.gitattributes stores every file byte for byte, so a checkout has the committed
line endings anyway.) Excluded: lean/.lake, build output, caches, LaTeX intermediates, verification/generated/
(rewritten on every run), the manifest itself.
"""
import hashlib
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "MANIFEST.sha256"
SKIP_DIRS = {".lake", "target", "__pycache__", ".git", "generated"}
SKIP_FILES = {"MANIFEST.sha256"}
SKIP_SUFFIX_IN_MANUSCRIPT = {".aux", ".blg", ".out", ".log"}
BINARY = {".pdf", ".png", ".tiff", ".jpg", ".exe", ".lock"}


def wanted(p: pathlib.Path) -> bool:
    rel = p.relative_to(ROOT)
    if any(part in SKIP_DIRS for part in rel.parts) or p.name in SKIP_FILES:
        return False
    if rel.parts[0] == "manuscript" and (p.suffix in SKIP_SUFFIX_IN_MANUSCRIPT or p.name == "bibtex.out"):
        return False
    return p.is_file()


def digest(p: pathlib.Path) -> str:
    data = p.read_bytes()
    if p.suffix not in BINARY and b"\0" not in data:
        data = data.replace(b"\r\n", b"\n")
    return hashlib.sha256(data).hexdigest()


def files():
    return sorted((p for p in ROOT.rglob("*") if wanted(p)), key=lambda p: p.relative_to(ROOT).as_posix())


def main() -> int:
    if "--check" in sys.argv:
        skip = (lambda rel: rel.startswith("verification/logs/")) if "--skip-logs" in sys.argv else (lambda rel: False)
        bad = 0
        for line in OUT.read_text(encoding="utf-8").splitlines():
            h, rel = line.split("  ", 1)
            if skip(rel):
                continue
            p = ROOT / rel
            if not p.is_file():
                print(f"MISSING  {rel}")
                bad += 1
            elif digest(p) != h:
                print(f"CHANGED  {rel}")
                bad += 1
        listed = {line.split("  ", 1)[1] for line in OUT.read_text(encoding="utf-8").splitlines()}
        extra = [p.relative_to(ROOT).as_posix() for p in files()
                 if p.relative_to(ROOT).as_posix() not in listed and not skip(p.relative_to(ROOT).as_posix())]
        listed = {rel for rel in listed if not skip(rel)}
        for rel in extra:
            print(f"UNLISTED {rel}")
        print(f"{len(listed)} files listed, {bad} missing or changed, {len(extra)} unlisted")
        return 1 if bad or extra else 0
    lines = [f"{digest(p)}  {p.relative_to(ROOT).as_posix()}" for p in files()]
    OUT.write_bytes(("\n".join(lines) + "\n").encode("utf-8"))
    print(f"wrote {OUT.name}: {len(lines)} files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
