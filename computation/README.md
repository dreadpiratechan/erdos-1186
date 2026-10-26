# Computation: certificates, generators, verifiers and small-case checks

This directory holds the data and programs behind the finite parts of the paper: the exact certificates of Theorems B
and C, the scripts that turn them into Lean modules, independent exact verifiers of the certificates, and small-case
checks of the definitions and of two lemmas. The programs were written and run by AI agents of the research project
(see `../docs/PROVENANCE.md`). None of the claimant's files or code (see the Theorem C row of `../README.md`) is
included here, and none was run.

## What is a proof here, and what is not

| Kind | Files | Trusted? |
|---|---|---|
| **Proofs** | none in this directory. The proofs are the Lean modules in `../lean/`, checked by the Lean kernel. | yes (the kernel) |
| **Generators** of Lean modules | `theorem-b/lean_cert.py`, `theorem-b/lean_cert2.py`, `theorem-c/lean_cert_ex.py` (with its exact mirror `theorem-c/cexmirror.py`), `theorem-c/gen_interface.py`, `theorem-c/bath/gen_bath_tab.py` | no. Their output is checked by the kernel; a wrong table makes a module fail to compile, it cannot make a false theorem. `../verification/regen_check.py` shows that they reproduce the shipped modules byte for byte from the JSON data. |
| **Exact cross-checks** (integer and rational arithmetic) | `theorem-b/verify_*.py`, `theorem-c/verify_certs.py`, `theorem-c/verify_pd_bareiss.py`, `theorem-c/check_star.py`, `theorem-c/fidelity_check.py` (with `fidelity.lean`), `small-cases/*.py` | not part of any proof. They re-check, with separately written code, what the kernel also checks (Theorems B, C), or they check things that are not in Lean (the certificates at L = 32, 192, 512 and the evidence of Section 8; the small-case checks). |
| **Certificate builders and search code** (floating point) | `theorem-b/shorlb.py`, `theorem-b/shorcert.py`, `theorem-c/make_certs.py`, `theorem-c/psdcert.py`, `theorem-c/import_rev.py`, `theorem-c/sdpmodel.py` (the model used by the builders and by `verify_certs.py`) | **untrusted by design**. How a certificate was found does not matter: only the exact checks of its content do. |
| **Numerical sanity test** | `theorem-c/test_interface.py` | evidence only: prints slacks of the Theorem C interface on samples, decides nothing. |
| **Negative-control generator** | `theorem-b/lean_cert2_controls.py` | writes seven corrupted copies of a scratch L = 32 certificate module; each must be rejected by the kernel. The scratch input is made by `lean_cert2.py --single`; the controls are not part of `run_all.sh`. |

The search programs that produced the Theorem B cut certificates (Burer-Monteiro with an augmented Lagrangian,
cutting planes and a repair step) are not part of this repository; only their output, the JSON certificates, is.

## Layout

| Path | Contents | Paper |
|---|---|---|
| `theorem-b/data/sdp_model2cuts_L{32,64,128,192,256,512}.json` | Shor + triangle-cut certificates for the sharper cover. **L = 64, 128, 256 are checked in Lean** (Theorem B); 32, 192, 512 by Python only | Sections 6, 8 |
| `theorem-b/data/sdp_dn_L{128,256,512}.json` | diagonal certificates for the strip cover of Parrilo, Robertson and Saracino. **L = 128 and 256 are checked in Lean** (Theorem A and the L = 256 strip bound); 512 by Python only | Sections 3, 8 |
| `theorem-b/data/sdp_model2_L{64,128,256}.json`, `sdp_tri_L{64,128,256,512}.json` | evidence only: diagonal certificates on the sharper cover; the strip cover with triangle cuts | Section 8 |
| `theorem-b/verify_model2cuts.py`, `verify_model2cuts_dd.py` | exact checks of the cut certificates: the cell kernel against brute-force cell counts, every cut at all eight cube vertices, positive definiteness by Bareiss elimination (L ≤ 256) or by diagonal dominance after an integer congruence (L = 128, 256, 512), the exact bound | Sections 5, 6 |
| `theorem-b/verify_sdp.py`, `verify_model2.py`, `verify_tri.py`, `verify_dd.py` | the same for the diagonal and strip-cover certificates | Sections 3, 8 |
| `theorem-b/lean_cert.py`, `lean_cert2.py` | generators of the diagonal (`P1186Cert128*`, `P1186Cert256*`) and cut (`P1186M2Cert{64,128,256}*`) certificate modules | Section 7 |
| `theorem-b/run_checks.sh` | runs all Theorem B verifiers: `quick` (L ≤ 256, about 3 minutes) or `full` (adds L = 512, about 13 minutes) | |
| `theorem-b/logs/` | recorded outputs of the run of 26 October 2026 on the research package (`full` mode) | |
| `theorem-c/data/cert_region{1..5}.json` | the integer certificates of the five finite statements `RegionLB` of Theorem C (format: `theorem-c/FORMAT.md`) | Section 10 |
| `theorem-c/data/grids.json` | the two grids G24 and G8 with the cell signs and exact pair areas (written by `gen_interface.py`) | Section 10 |
| `theorem-c/data/certs_rev1186c.json` | the starting multipliers of `make_certs.py`: exact certificates that a reviewing AI agent of the research project built from the claim's text with its own code (`rev1186c` is that agent's identifier, not a person). These are not the claimant's certificates, which were never run. | Section 10 |
| `theorem-c/data/fidelity_lean_out.txt` | the values of the Lean definitions at test points, printed by `theorem-c/fidelity.lean` | |
| `theorem-c/verify_certs.py` | exact verifier of the five certificates, a second implementation of the matrix: structure, the matrix rebuilt from the multipliers, the polynomial identity at random rational points, positive semidefiniteness by a Cholesky-and-dominance certificate, and the margin | Section 10 |
| `theorem-c/verify_pd_bareiss.py` | a second, independent positive-definiteness check (Bareiss elimination, no Cholesky data used) | Section 10 |
| `theorem-c/check_star.py` | the star value Σ K4(548, p, q) sg(c1 p) sg(c1 q) = -43840 by two formulas, and the Lean bound on `Wm` of the 12-block colouring for w ≤ 4 | Section 10 (a) |
| `theorem-c/fidelity.lean`, `fidelity_check.py` | the Python model `sdpmodel.py` against the Lean definitions: Lean evaluates the definitions at test points, the script compares exactly. A check at sample points, not a proof that the two agree | |
| `theorem-c/lean_cert_ex.py`, `cexmirror.py` | generator of the 124 certificate modules `P1186ExCert{1..5}*` (it re-derives, in exact Python integers, every identity the kernel will evaluate before writing anything) | Section 10 |
| `theorem-c/gen_interface.py`, `bath/gen_bath_tab.py` | generators of `P1186ExData.lean` (the grids) and `P1186ExBathTab.lean` (the bathtub tables) | Section 10 |
| `theorem-c/make_certs.py`, `psdcert.py`, `import_rev.py`, `sdpmodel.py` | the certificate builder (rounding, margin, derived multipliers, Cholesky) | |
| `theorem-c/test_interface.py` | numerical sanity test of the interface | |
| `theorem-c/FORMAT.md` | the certificate format and how each number is derived (from the research repository) | |
| `small-cases/oeis_small.py` | exhaustive minimum of `monoCount 3 n` over all colourings for n ≤ 26, against the terms of OEIS A121385 | Section 7.2 |
| `small-cases/disc_cutcell_check.py` | exhaustive check of the discrete cut-cell inequality of Section 5 for w = 2, 4, ..., 10 | Section 5 |
| `small-cases/lemma2_symbolic.py` | symbolic check (sympy) of the case analysis of the continuum cut-cell lemma | Section 5 |
| `small-cases/logs/` | their recorded outputs (26 October 2026) | |

The certificates at L = 32, 192 and 512, the strip-cover certificates with cuts, the diagonal certificates on the sharper
cover, and the whole of Section 8 of the paper are checked by Python only, not by Lean.

## Changes from the research repository's copies

The Theorem B scripts and data, the small-case scripts and their logs are byte-identical to the research package. The
Theorem C files are the git blobs of the research repository's Theorem C commit (named in `../docs/PROVENANCE.md`), with these
changes, all of them to paths (the research repository keeps them in `problems/1186/exact/`):

- `sdpmodel.py`: `EXACT` is this folder and `ROOT` the repository root (two lines).
- `lean_cert_ex.py`: the default output folder is the repository's `lean/Erdos/Proofs` (one line).
- `test_interface.py`: reads `data/grids.json` next to itself (two lines become one).
- `gen_interface.py`, `bath/gen_bath_tab.py`: the repository root and the location of `grids.json` (two lines each).
- `FORMAT.md`: one line naming a local folder of the research machine replaced by the location in this repository.

Docstrings that give paths such as `problems/1186/exact/...` or `../problems/1186/out/...` refer to the research
repository; here they are `computation/theorem-c/...`. The comments and docstrings name internal lanes and agents of
the research project (for example `excert`, `excertsdp`, `sdp1186m`, `rev1186c`); these are identifiers of AI agent
sessions, not people. `theorem-b/run_checks.sh` was rewritten: it records the exit status of every run and reports
failure (the package's version printed `ALL-DONE` whatever the outcome).

## Requirements

- Python 3 (recorded runs: 3.13.3) with numpy (2.2.6), scipy (1.16.2) and sympy (1.14.0; `lemma2_symbolic.py` only).
- All scripts locate their inputs relative to their own location, so they can be run from any directory. On Windows use
  `py` for `python3`; the shell script needs Bash.
- Pass `-B` (or set `PYTHONDONTWRITEBYTECODE=1`) to keep `__pycache__` folders out of the tree.

## Quick start

From the repository root. Runtime classes: *seconds* (under a minute), *minutes* (1 to 15 minutes).

```
python3 -B computation/theorem-c/verify_certs.py          # seconds (about 20 s): ALL OK for regions [1, 2, 3, 4, 5]
python3 -B computation/theorem-c/verify_pd_bareiss.py     # about 1 minute: BAREISS OK for regions [1, 2, 3, 4, 5]
python3 -B computation/theorem-c/check_star.py            # seconds: OK
python3 -B computation/theorem-c/fidelity_check.py        # seconds: FIDELITY OK (against the recorded Lean output)
bash computation/theorem-b/run_checks.sh quick /tmp/b     # about 3 minutes: ALL CHECKS PASSED (18 runs, mode quick)
python3 -B verification/regen_check.py                    # seconds (about 20 s): RESULT: ALL IDENTICAL
python3 -B computation/small-cases/oeis_small.py 26       # about 4 minutes: RESULT: ALL OK
python3 -B computation/small-cases/disc_cutcell_check.py  # seconds: RESULT: ALL OK
python3 -B computation/small-cases/lemma2_symbolic.py     # seconds: ALL OK
```

`bash computation/theorem-b/run_checks.sh full /tmp/b` adds the L = 512 checks (about 13 minutes in all). The times are
those of the authoring machine (Windows 10, 16 logical processors, 32 GB, shared with other jobs).
