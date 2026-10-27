# Erdős Problem 1186, k = 3: machine-checked results on monochromatic 3-term progressions

This repository accompanies the paper *Machine-checked results on the minimum number of monochromatic 3-term arithmetic
progressions in two-colourings (Erdős Problem 1186, case k = 3)* by Chandler Snively (Quana Labs, 2026). It contains:

- the manuscript;
- the Lean 4 formalization of its theorems, pinned to an exact toolchain;
- a script that repeats every formal check from a clean build, and the logs of its last run;
- the programs and data behind the paper's finite computations.

**The question.** For a 2-colouring c of {1, …, n}, count the monochromatic 3-term arithmetic progressions a, a + d,
a + 2d (d ≥ 1) and minimise over c; δ₃ is the lim inf of that minimum divided by n². Parrilo, Robertson and Saracino
(2008) proved 1675/32768 ≤ δ₃ ≤ 117/2192 and conjectured that the upper bound is the truth. Problem 1186 of
[erdosproblems.com](https://www.erdosproblems.com/1186) asks about δ_k for all k; this repository is only about k = 3
and says nothing about the general problem.

> **How this work was done.** Theorem B and its proof, and all the Lean proofs, were produced by AI systems in a research
> project directed by the author (the mathematics of Theorem A is that of Parrilo, Robertson and Saracino). The paper and
> the verification were also prepared with AI. **Theorem C is a Lean formalisation of Carlos Toledo's unrefereed proof
> claim; the mathematics of Theorem C is Toledo's, not ours.** No independent human mathematician has checked the proofs,
> no human has read the Lean sources beyond the statements, and the paper has not been peer reviewed. The formal verification below is the main evidence for correctness. See
> [docs/PROVENANCE.md](docs/PROVENANCE.md) and the statement on AI use at the end of the paper.

**Release v1.0.0** (prepared 26 October 2026; not yet published).

## Results and their status

| Result | Statement | Status |
|---|---|---|
| Theorem A | 1675/32768 ≤ δ₃ ≤ 117/2192 (the bounds of Parrilo, Robertson and Saracino) | **Formally verified** in Lean, as the Formal Conjectures statement `erdos_1186.variants.prs_bounds`. A formalisation of known mathematics |
| Theorem B | δ₃ ≥ 14324135/268435456 = 0.05336156…; also δ₃ ≥ 1788837/33554432 = 0.0533114… and δ₃ ≥ 1782409/33554432 = 0.0531199… (smaller certificates) | **Formally verified** in Lean. The written proof's continuum cut-cell lemma is not formalised (Lean proves a weaker integer inequality directly) and was checked only by AI readers and small-case computations. The bound was "not found in the searches described" |
| Theorem C | δ₃ = 117/2192 (the conjecture of Parrilo, Robertson and Saracino) | **Formally verified** in Lean, as the Formal Conjectures statement `erdos_1186.variants.prs_conjecture`. It is a Lean formalisation, by AI agents of the research project, of the **unrefereed proof claim of Carlos Toledo**, *The twelve-block colouring is optimal: δ₃ = 117/2192* (draft v0.2, posted on [the problem's proof-claims thread](https://www.erdosproblems.com/forum/thread/1186/proof-claims) on 5 October 2026). **The mathematics is the claimant's.** The claimant states that the claim was produced with substantial AI assistance (Claude) and that they read and checked it line by line. The formalisation is in a discrete form with five stated departures from the claim (below). Theorem C implies Theorems A and B |
| Further upstream statements | `van_der_waerden` (0 < δ_k) and `probabilistic` (δ_k ≤ 1/((k − 1)2^k)) for k ≥ 2 | Formally verified in the same development; not results of the paper |
| Strip cover at L = 256 | δ₃ ≥ 6928985/134217728 = 0.0516249… | Formally verified; the method of Parrilo et al. with a larger certificate, not a new idea |
| Evidence (Section 8 of the paper) | exact certificates outside Lean up to 0.0533678 (size 512); a gap to 117/2192 that shrinks like 1/L² for L ≤ 256; floating-point minima | **Computational evidence**, checked in exact arithmetic by Python only, or (the floating-point values) not checked at all |

The constants are exact. Decimal expansions such as 14324135/268435456 = 0.05336156… are truncated, never rounded (but see
the known errors below for the Lean comments).

**The five departures of Theorem C from the claim** (from an AI audit of the Lean interface against the claim's TeX
source, [docs/REVIEWS.md](docs/REVIEWS.md), Section 6):
1. the counting step uses the exact ±1 identity at n = 1096w and monotonicity, not the claim's use of the counting lemma
   of Parrilo et al.;
2. the value −5/137 at the 12-block colouring comes from the paper's cover inequality, not from the claim's exact
   computation;
3. only ±1 colourings are treated, not every measurable function;
4. the five finite statements are proved in the weaker form L ≥ 0, so the claim's equality case, its corollary and the
   existence of the limit are not formalised;
5. the certificates are the project's own, not the claimant's (the claimant's certificates and code were never run).

None of the claimant's files or code is in this repository.

**Novelty is not established.** The searches found no improvement of the bounds of Parrilo et al. in print and no
earlier formal proof of them; Theorem B was "not found in the searches described". A search cannot prove novelty. See
[docs/LITERATURE.md](docs/LITERATURE.md).

## What the formal verification establishes

The Lean development proves the statements above for definitions `monoCount`, `minMonoCount` and `δ` that are copied
verbatim from the [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) project
(`FormalConjectures/ErdosProblems/1186.lean`, commit `c83a94d785d0`, 22 October 2026) and checked, by `rfl`, to be
**definitionally equal** to them. `verification/make_upstream_pin.py` also copies the upstream statements of
`prs_bounds`, `prs_conjecture`, `van_der_waerden` and `probabilistic` verbatim and proves them from our theorems, so the
statements proved are the upstream ones.

The last recorded run (`verification/logs/`) shows:
- **Build.** A clean `lake build` of all 342 modules succeeds with Lean `v4.27.0` and Mathlib `a3a10db` (tag `v4.27.0`).
- **Axioms.** Every declaration of the 342 modules depends only on Lean's standard axioms `propext`, `Classical.choice`
  and `Quot.sound` (`verification/AxiomAudit.lean`). There is no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`) and
  no added axiom; a source scan finds none of them, nor any `unsafe`, `extern` or metaprogramming, in the code.
- **Statements.** `verification/Headline.lean` prints every statement the paper uses and its axioms (36 theorems).
- **Kernel replay.** [lean4checker](https://github.com/leanprover/lean4checker) `v4.27.0` replays every one of the 342
  modules, one process per module (`verification/logs/lean4checker.log`).
- **Exact arithmetic.** Independent Python verifiers re-check the certificates of Theorems B and C in integer and
  rational arithmetic, the 302 generated Lean modules are regenerated byte for byte from the JSON data, and the small
  cases of the definitions (n ≤ 26, against OEIS A121385) and of the cut-cell lemma are checked exhaustively.

What it does **not** establish:
- that the upstream definitions express the constant the problem intends (the Formal Conjectures authors' claim, which
  we only checked to be the one we proved);
- that Theorem C formalises the claim as its author meant it: the Lean interface was compared with the claim's TeX source
  by one AI agent, the claim, the reviewers and the formalising agents all used Claude models, and so a shared misreading
  cannot be excluded (this does not affect the truth of Theorem C, whose statement is the upstream one);
- the prose proofs of the paper, in particular its continuum cut-cell lemma;
- that the results are new;
- anything about δ_k for k ≥ 4.

The trust base is the standard one for Lean: the kernel, Mathlib's definitions, and the three axioms. A guide for a human
checker, with the plain meaning of each statement and a reading order, is [docs/CHECKING-GUIDE.md](docs/CHECKING-GUIDE.md).

## Known errors and oddities

The Lean sources are left unchanged, so that they stay identical to the research version described in
[docs/PROVENANCE.md](docs/PROVENANCE.md). The following affect comments only; no proof depends on them.

- **Rounded decimals.** Some docstrings round to the nearest digit instead of truncating, so that, read as inequalities,
  they overstate the lower bounds and understate the upper bound: `P1186M2Main.lean` lines 21, 35, 39, 43 and 47
  (`0.0533616` and `0.0533115` for the proved 0.0533615… and 0.0533114…, and `δ 3 ≤ 0.0533759` for 117/2192 = 0.0533759124…)
  and `P1186LowMain.lean` lines 16 and 33 (`0.0516250` for 0.0516249…, `0.0511170` for 1675/32768 = 0.0511169…).
- **Credit sentence.** The headers of the Theorem C files say "Formalises the proof claimed on erdosproblems.com/1186
  (Proof claims, 2026-10-05, unrefereed); the mathematics is its author's." The sentence is in 151 of the 153 files;
  `P1186Ex.lean` has a variant of it, and the generated `P1186ExData.lean` mentions "the claimed proof" without it.
- **Internal names.** Namespaces such as `Erdos1186Night2` and `Erdos1186Night2M2`, and words in comments such as "lane
  `exglue`", `excert` or `rev1186c`, are identifiers of AI agent sessions of the research project, not people.
- **Negative controls.** The shipped controls `P1186ExCertCtl.lean` (kernel-checked examples showing that the
  certificate checker rejects corrupted data) cover only the fifth of the five finite statements of Theorem C.
- **Research notes.** Comments mention research notes and folders (for example `problems/1186/...`) that are not part of
  this release.

## Layout

| Path | Contents |
|---|---|
| `manuscript/` | `main.tex` (the manuscript as one file, bibliography inlined; it compiles without BibTeX), `refs.bib` (the BibTeX source of that bibliography) and the compiled `main.pdf`, copied from the paper's workspace (see [docs/PROVENANCE.md](docs/PROVENANCE.md)) |
| `lean/` | A standalone Lake project: the 342 proof files under `Erdos/Proofs/`, byte-identical to the research repository's, and `Erdos1186.lean`, which imports the modules of Theorems A, B and C and the negative controls (its closure is all 342 files) |
| `verification/` | `run_all.sh`, which repeats every check; `Headline.lean`; `AxiomAudit.lean`; the upstream pin (`make_upstream_pin.py`, `upstream/`); `source_scan.py` with `lean_modules.sha256`; `fidelity_check.py`; `regen_check.py`; `number_checks.py`; `make_manifest.py`; `build_closure.py` (an alternative module-by-module build with plain `lean`); `logs/` from the last run; `earlier-runs/` (the logs of the paper package's runs, for reference) |
| `computation/` | Certificates (JSON), the generators of the Lean certificate modules, the exact verifiers, the certificate builders and the small-case checks; see [computation/README.md](computation/README.md), which says which files are proofs, which are exact cross-checks and which are untrusted search code |
| `docs/` | [PROVENANCE.md](docs/PROVENANCE.md) (who and what produced the work), [CHECKING-GUIDE.md](docs/CHECKING-GUIDE.md) (for a human checker), [LITERATURE.md](docs/LITERATURE.md) (literature search and novelty), [REVIEWS.md](docs/REVIEWS.md) (internal AI reviews and how each finding was resolved) |
| `MANIFEST.sha256` | SHA-256 of every file, with LF line endings. Check it on a fresh checkout with `python3 verification/make_manifest.py --check` (on Windows, `py` instead of `python3`). Running the verification rewrites the logs, so they will then differ; `--check --skip-logs` leaves `verification/logs/` out |

## Reproducing the formal verification

Requirements:
- [elan](https://github.com/leanprover/elan), the Lean toolchain installer. It reads `lean/lean-toolchain`.
- Git, Bash, and Python 3 with numpy, scipy and sympy (recorded runs: Python 3.13.3, numpy 2.2.6, scipy 1.16.2,
  sympy 1.14.0).
- About 8 GB of disk for Mathlib and its build cache.
- Memory: the largest generated certificate modules reached 8.7 GB of resident memory each in the run of record. Allow
  about 9 GB per parallel job (`JOBS`), so 18 GB or more with the default `JOBS=2`.
- Network access for the first run.

```bash
FETCH_CACHE=1 JOBS=2 bash verification/run_all.sh
```

`FETCH_CACHE=1` downloads Mathlib (pinned in `lean/lake-manifest.json`) and its prebuilt cache; later runs can omit it.
The script deletes `lean/.lake/build`, builds the 342 modules from scratch, runs every check, and writes
`verification/logs/SUMMARY.txt`. `JOBS` (default 2) sets the parallelism: Lake 4.27.0 has no `-j` option, so the script
passes it as `LEAN_NUM_THREADS`, which limits Lake's job pool and each Lean process's threads.

To include the kernel replay, build lean4checker and pass its path:

```bash
git clone --branch v4.27.0 https://github.com/leanprover/lean4checker /tmp/lean4checker
(cd /tmp/lean4checker && lake build)
LEAN4CHECKER=/tmp/lean4checker/.lake/build/bin/lean4checker JOBS=2 bash verification/run_all.sh
```

Without `LEAN4CHECKER`, the lean4checker line reads `SKIPPED (LEAN4CHECKER not set)` and the last line
`RESULT: PASS (kernel replay skipped)`. The run of record (`verification/logs/SUMMARY.txt`) printed:

```
# summary 2026-10-27T05:05:19Z (started 2026-10-26T22:59:39Z, JOBS=2)
manifest:       457 files listed, 0 missing or changed, 0 unlisted [exit=0]
build:          Build completed successfully (8228 jobs). 0 sorry warnings [exit=0]
headline:       36 axiom lines, 0 non-standard, 0 error lines [exit=0]
axioms:         TOTAL: 4978 constants (2356 theorems) in 342 modules AXIOM AUDIT PASSED: every constant of the 342 modules depends only on propext, Classical.choice, Quot.sound  [exit=0]
upstream pin:   7 axiom lines, 0 non-standard, 0 error lines [exit=0]
model fidelity: Lean output equals computation/theorem-c/data/fidelity_lean_out.txt: True FIDELITY OK  [exit=0]
lean4checker:   342 of 342 modules exit 0
source scan:    import closure: 342 modules; files in lean/Erdos/Proofs: 342; unused files: none forbidden words in code (comments, docstrings and strings removed): 0 RESULT: ALL OK  [exit=0]
statement text: RESULT: ALL OK [exit=0]
numbers:        ALL 14 CHECKS PASSED [exit=0]
regeneration:   regenerated byte for byte: 302 of 342 modules RESULT: ALL IDENTICAL  [exit=0]
C certificates: ALL OK for regions [1, 2, 3, 4, 5]  [exit=0]
C Bareiss:      BAREISS OK for regions [1, 2, 3, 4, 5] [exit=0]
C star value:   T direct = -43840  T (274-term form) = -43840 OK  [exit=0]
B certificates: ALL CHECKS PASSED (18 runs, mode quick)  [exit=0]
OEIS A121385:   RESULT: ALL OK [exit=0]
cut-cell lemma: RESULT: ALL OK [exit=0]
lemma symbolic: ALL OK [exit=0]
RESULT: PASS
```

The script exits with status 0 only if every step it ran passed; otherwise the summary ends with `RESULT: FAIL`.

**The run of record.** It was made on 26 October 2026 from a fresh clone of this repository's first commit (`f68f061`),
at a short path, on Windows 10 with Git Bash, `JOBS=2` and lean4checker `v4.27.0`, on a machine shared with other jobs
and through its job gate, which kills any single process above 9 GB of memory. Mathlib was not downloaded: the
compiled Mathlib checkout of the research repository (the same commit `a3a10db`) was copied into `lean/.lake/packages`,
and Lake was run with `LAKE_NO_CACHE=1`. Result: `RESULT: PASS` after 6 hours 6 minutes, of which the build took
147 minutes and the kernel replay 3 hours 18 minutes (342 lean4checker processes, two at a time; the longest took
442 seconds); the other steps took about 20 minutes. The largest resident memory of a single process was 8.7 GB for
`lean` (compiling `P1186ExCert2P2`) and 8.1 GB for lean4checker. The build log has 11 linter warnings (10 unused `simp`
arguments, one deprecated lemma name) and no `sorry`. The scripts committed after that run differ from the ones that
ran only in comments and in the line of `environment.txt` that names lean4checker, which printed the executable's full
local path; in the committed log that line is replaced by what the corrected script prints. The logs are otherwise
copied unchanged.

To run without network access on a machine that already has this Mathlib, copy its `.lake/packages` folder into
`lean/.lake/packages` and set `LAKE_NO_CACHE=1`.

On Windows, run the script from Git Bash; it uses `py` if present. **Clone to a short path**, such as `C:\erdos-1186`.
Mathlib's build cache contains deep paths, and under a long parent folder some of them exceed Windows' 260-character
limit; the cache then unpacks without reporting an error, but the build fails on missing files.

The workflow in `.github/workflows/verify.yml` runs the same script on Linux, with one Lean job (a standard runner has
16 GB of memory) and without the kernel replay (the build alone takes hours, and hosted jobs stop after 6 hours).
**It has not been run yet**: it will run for the first time when the repository is pushed to a host that runs it, and it
may not finish within the limit.

The Python checks alone (no Lean, about 10 minutes) are listed in [computation/README.md](computation/README.md).

## Citing

Please cite the paper; see [CITATION.cff](CITATION.cff). Until an identifier exists, cite this repository and its release
tag. If you use Theorem C, please also cite the proof claim of Carlos Toledo, whose mathematics it formalises.

## Licence

- **Code**: Lean files, scripts and programs, under the [Apache License 2.0](LICENSE).
- **Text and data**: the manuscript, the documentation, and the data and logs, under [CC BY 4.0](LICENSE-CC-BY-4.0.md).
- **Third-party material**: `verification/upstream/` contains a verbatim copy of a Formal Conjectures file, under its own
  Apache 2.0 licence, and `lean/Erdos/Proofs/P1186.lean` copies its three definitions. `computation/small-cases/oeis_small.py`
  contains terms of OEIS A121385 (CC BY-SA 4.0). See [NOTICE](NOTICE).

## Contact

Quana Labs: [lab@quanalabs.com](mailto:lab@quanalabs.com), [quanalabs.com](https://quanalabs.com). Reports of errors are
welcome. A confirmed error is corrected in a new release, recorded in the release notes, and noted in a replacement
version of the paper.
