# A guide for a human checker

This guide is for a reader who wants to check the results of this repository without trusting the AI systems that
produced them. It says what each headline Lean statement means in ordinary mathematics, what has to be trusted, which
files to read and in which order, what the generated files do, how to run each check and how long it takes, and what is
not checked at all.

## 1. The statements, in plain mathematics

**The quantities.** For a colouring c: ℕ → {true, false}, `monoCount 3 n c` is the number of pairs (a, d) with
a ≥ 1, d ≥ 1 and a + 2d ≤ n such that c(a) = c(a + d) = c(a + 2d): the monochromatic 3-term progressions in
{1, …, n}, each counted once. `minMonoCount 3 n` is its minimum over all colourings, and

    δ 3 = liminf_{n → ∞} minMonoCount 3 n / n²   (a real number; the quotient lies in [0, 1], so this is not a junk value).

These are the definitions `monoCount`, `minMonoCount` and `δ` of Formal Conjectures (`FormalConjectures/ErdosProblems/
1186.lean`, commit `c83a94d785d0`), copied verbatim into `lean/Erdos/Proofs/P1186.lean` (namespace `Erdos1186Day`).

| Lean name | Statement | Meaning |
|---|---|---|
| `Erdos1186Day.erdos_1186.variants.prs_bounds` (Theorem A) | `1675 / 32768 ≤ δ 3 ∧ δ 3 ≤ 117 / 2192` | the bounds of Parrilo, Robertson and Saracino (2008): every colouring of {1, …, n} has at least (1675/32768 − o(1)) n² monochromatic 3-APs, and some colourings have at most (117/2192 + o(1)) n² of them, along a subsequence |
| `Erdos1186Day.delta3_ge_model2_L256` (Theorem B) | `(14324135 / 268435456 : ℝ) ≤ δ 3` | δ₃ ≥ 0.0533615…; also `delta3_ge_model2_L64` (1782409/33554432) and `delta3_ge_model2_L128` (1788837/33554432), from smaller certificates |
| `Erdos1186Day.erdos_1186.variants.prs_conjecture` (Theorem C) | `δ 3 = 117 / 2192` | the conjecture of Parrilo, Robertson and Saracino: the 12-block colouring is asymptotically optimal. **The mathematics is another author's** (see `../README.md`) |
| `Erdos1186Day.delta3_ge_L256` | `(6928985 / 134217728 : ℝ) ≤ δ 3` | the strip cover of Parrilo et al. with a larger certificate (L = 256); not a claim of the paper beyond its use in the evidence tables |
| `Erdos1186Day.erdos_1186.variants.van_der_waerden`, `...probabilistic` | `0 < δ k` and `δ k ≤ 1 / ((k − 1) 2^k)` for k ≥ 2 | two further upstream statements proved in the same development; not results of the paper |

`verification/generated/UpstreamPin.lean` (written by `verification/make_upstream_pin.py` from the vendored upstream file)
copies the upstream statements of `prs_bounds`, `prs_conjecture`, `van_der_waerden` and `probabilistic`, **verbatim**,
about verbatim copies of the upstream definitions, and proves each of them from the corresponding theorem here. So the
statements proved are the upstream ones, character for character, and the only thing a reader must judge is whether the
upstream definitions express the problem.

## 2. What has to be trusted

- The Lean 4 kernel (v4.27.0) and Mathlib at commit `a3a10db0e9d6` (tag `v4.27.0`): the definitions used (`Finset`,
  `sInf` on ℕ, `Filter.liminf`, the real numbers) and the three axioms `propext`, `Classical.choice`, `Quot.sound`.
- That the upstream definitions express the intended constant δ₃. This is the Formal Conjectures authors' formalisation
  of the problem; it is not checked here beyond the small-case comparison with OEIS A121385 (n ≤ 26).
- That the checks below were run on what you read: `MANIFEST.sha256` pins every file, and
  `verification/lean_modules.sha256` pins the 342 Lean modules to the research repository's files.

Not trusted: any Python script, any generator, any certificate, any comment or docstring, any AI report. The proofs are
checked by the kernel; the scripts are independent cross-checks, and the generators only produce input for the kernel.

`decide +kernel` is used for every finite computation. It asks the kernel itself to evaluate a Boolean function to `true`
(no compiled code is trusted, no extra axiom is used). `native_decide`, which would trust the compiler, is not used
anywhere: the source scan and the axiom audit both check this.

## 3. What to read, in order

The 342 modules are about 21 MB of Lean. About 400 KB of it (40 modules) is hand-written; the rest (302 modules) is
generated certificate data.
Reading the hand-written part in the order below is enough to understand every proof; reading the statements (steps 1 to
3) is enough to know what is proved, given the kernel's check.

**Step 1: the problem.** `verification/upstream/FormalConjectures_ErdosProblems_1186.lean` (the upstream file, about 130
lines): the three definitions and the statements `prs_bounds`, `prs_conjecture`, `van_der_waerden`, `probabilistic`,
`erdos_1186` (all `sorry` upstream).

**Step 2: the copies and the pin.** The first 80 lines of `lean/Erdos/Proofs/P1186.lean` (the copied definitions), then
`verification/make_upstream_pin.py` and the file it writes, `verification/generated/UpstreamPin.lean` (about 110 lines):
`pin_monoCount`, `pin_minMonoCount`, `pin_delta` are `rfl`, and the four upstream statements are proved by rewriting
with `pin_delta`. `verification/fidelity_check.py` makes the same comparison on the text.

**Step 3: the headline statements.** `verification/Headline.lean` and its output `verification/logs/headline.log`: the
statements as Lean prints them, and the axioms of each.

**Step 4: Theorems A and B** (13 hand-written modules, about 180 KB).
- `P1186Prs.lean` (56 lines): `DiagCert L d` (a diagonal certificate: d ≥ 0 and xᵀAx ≥ −Σ dᵢxᵢ² for all real x, for
  the strip matrix A of Parrilo et al.) and `prsBound`.
- `P1186Low.lean`, `P1186LowA.lean`: `lower_of_cert`: for every even L ≥ 2 and every diagonal certificate,
  `prsBound L d ≤ δ 3` (the counting argument of Parrilo et al., with the exact ±1 identity of `P1186LowA.lean`).
- `P1186Cert128Lib.lean`: the soundness of the integer form of a diagonal certificate (`CertData.diagCert`: if an
  approximate integer Cholesky factor leaves a diagonally dominant remainder, the certificate holds). No numbers.
- `P1186Tab.lean` and the end of `P1186.lean`: the upper bound, from the 12-block colouring (four counts by
  `decide +kernel`).
- `P1186M2.lean` (49 lines): the cell kernel `K4`, the form `cform`, `CubeLB L σ` (xᵀCx ≥ −σ on the cube [−1, 1]^L) and
  `bound2 L σ = 1/16 − (L + σ)/(4L²)`.
- `P1186M2LowA.lean` (the discrete cut-cell inequality `lemA`), `P1186M2LowB.lean` (the cover inequality `W_lower`),
  `P1186M2Low.lean` (`lower_of_cubeLB`: for every even L ≥ 4 and every σ, `CubeLB L σ → bound2 L σ ≤ δ 3`).
- `P1186M2CertLib.lean` (761 lines): the soundness of the integer cut certificates (`Cert.link_sound`, `Cert.psd`,
  `cubeLB_of_cert`). No numbers.
- `P1186LowMain.lean`, `P1186M2Main.lean`: the instances that give Theorems A and B.

**Step 5: Theorem C** (27 hand-written modules, about 220 KB). The mathematics is the claimant's; the Lean is the project's.
- `P1186Ex.lean` (131 lines), **the interface**. Read all of it. It fixes the scale n = 1096w, the 12-block colouring
  `sstar`, the counting region `rdI` and its quadratic form `Qd`, the linear coefficients `H2`, the grids and their cell
  data (`Grid.N`, `lo`, `hi`, `wt`, `ai`, `bi`, `sgn`, `A4`), the cell densities `yv`, the pair bound `pterm`, the finite
  lower bound `Lval` and the density `mval`, and **the five target propositions**:
  `StarOK` (the 12-block colouring: Wm(s*) ≥ −(5/137)n² − Cw), `BathOK G` (the bathtub bound on every cell of the grid G),
  `PairOK G` (the cell-pair bound summed over the grid), and `RegionLB G lo hi` (Lval G y ≥ 0 for every y ∈ [0, 1]^N with
  lo ≤ m(y) ≤ hi). `P1186ExData.lean` holds the two grids (data, generated).
- `P1186ExGlue.lean` (430 lines), **the glue**: `Wm_eq_Qd`, the exact expansion
  Qd(s) = Qd(s*) + 2 Σ H2 σ + 4 Qd(s*σ) for s = s*(1 − 2σ), the grid lemmas, `combine`, `wm_lower` (the case split on the
  density m and the symmetry σ ↦ 1 − σ), and `lower_of_parts` / `delta3_eq_of_parts`. `P1186ExMain.lean` states
  `delta3_eq_of_regions`: the five `RegionLB` statements imply δ 3 = 117/2192. `P1186ExFinal.lean` applies it to
  `region1` … `region5`.
- The parts: `P1186ExStar.lean` (`starOK`), `P1186ExPair.lean` (`pairOK_of_WF : G.WF → PairOK G`),
  `P1186ExBath.lean` with `P1186ExBathLib`, `-Cell`, `-H2`, `-FU`, `-Chk` (`bathOK24`, `bathOK8`; the per-cell checks
  `P1186ExBathC24a`…`C8d` are one `decide +kernel` line each over the tables of `P1186ExBathTab.lean`).
- **The certificate checker's soundness library**: `P1186ExCertLib.lean` (packed integer tables, the quadratic
  polynomials `evq`, the Gram expansion, the pair bound), `P1186ExCertAlg.lean` (the form side and the pair side),
  `P1186ExCertChk.lean` (the Boolean checks `gridChk`, `vecChk`, `scalChk`, `pairChk`, `linChk`, `czRowChk`,
  `constChk`, `lenChk`, `domRow`, and `region_of_tabs`, which turns them into `RegionLB`), with `P1186ExCertTri.lean`
  and `P1186ExCertPk.lean` (the triangle forms, as exact sums of packed integers). These files contain no certificate
  numbers. The one theorem to understand is `region_of_tabs`: if every check returns `true` on the tables, the region
  statement holds.

## 4. The generated modules, and why they need not be read line by line

302 of the 342 modules are generated from JSON data by the scripts in `computation/` (the diagonal and cut certificates
of Theorems A and B, the 124 certificate modules of Theorem C, the grid data and the bathtub tables). Each consists of
`def`s of integer data (lists of numbers, often packed into large natural numbers), theorems of the form
`theorem t : <Boolean check defined in a hand-written library> <data> = true := by decide +kernel`, and, in the top
module of each family, a short proof that applies the soundness theorem of the library (`region_of_tabs`,
`cubeLB_of_cert`, `CertData.diagCert`) to these facts.

Why that is enough:
- A wrong number cannot produce a false theorem. It makes a `decide +kernel` fail, and the module does not compile.
- What the data mean is fixed by the hand-written checks and their soundness proofs (step 4 and step 5 above), and the
  top theorem's type (for example `RegionLB G24 0 (1 / 5)`) is checked by the kernel where it is used
  (`delta3_eq_of_regions` in `P1186ExFinal.lean`).
- The only other things a generated module could contain are forbidden by `verification/source_scan.py`: no `sorry`,
  `native_decide`, `axiom`, `unsafe`, `extern`, `implemented_by`, options that switch off the kernel, or
  metaprogramming. `verification/AxiomAudit.lean` checks the axioms of every declaration of every module.
- `verification/regen_check.py` shows that the 302 files are exactly what the generators produce from the JSON data, so
  no file was edited by hand after generation.

A checker who wants to see one at work can read `P1186ExCert4.lean` (the top module of range 4, about 110 lines) and one
chunk, for example `P1186ExCert4D0.lean`.

## 5. Running the checks

Requirements: elan, Git, Bash, Python 3 with numpy, scipy and sympy; about 8 GB of disk for Mathlib; and memory for the
build: the largest generated modules need several GB each, so allow about 5 GB per parallel job (`JOBS`).

```bash
FETCH_CACHE=1 JOBS=2 bash verification/run_all.sh                 # everything except the kernel replay
FETCH_CACHE=1 JOBS=2 LEAN4CHECKER=/path/to/lean4checker bash verification/run_all.sh   # with the replay
```

| Step (log in `verification/logs/`) | What it checks | Time on the authoring machine |
|---|---|---|
| `manifest.log` | every file against `MANIFEST.sha256` | seconds |
| `build.log` | a clean `lake build` of all 342 modules | hours (earlier module-by-module builds of the same files: 47 min for the 189 modules of Theorems A and B, 88 min for the 152 further modules of Theorem C; `verification/logs/build.log` has the time of the run of record) |
| `headline.log` | the statements and the axioms of 36 theorems | minutes |
| `axioms.log` | the axioms of every declaration of the 342 modules | minutes |
| `upstream_pin.log` | the verbatim upstream definitions and statements, by `rfl` and from our theorems | minutes |
| `model_fidelity.log` | the Python model of the Theorem C certificates against the Lean definitions, at test points | minutes |
| `lean4checker.log` | an independent replay of every module by the kernel checker lean4checker (optional) | hours |
| `source_scan.log`, `fidelity_check.log`, `number_checks.log` | closure and hashes, forbidden constructs, the statement text, the decimals | seconds |
| `regen_check.log` | the 302 generated modules regenerated byte for byte | about 20 s |
| `theorem_c_certs.log`, `theorem_c_bareiss.log`, `theorem_c_star.log` | the Theorem C certificates in exact arithmetic, a second positive-definiteness check, the star value | about 1.5 min |
| `theorem_b_checks.log`, `theorem-b/` | the Theorem B and evidence certificates (L ≤ 256) | about 3 min |
| `oeis_small.log`, `disc_cutcell.log`, `lemma2_symbolic.log` | the small-case checks | about 4 min |

The summary `verification/logs/SUMMARY.txt` ends with `RESULT: PASS` only if every step passed.

To read a single statement without building everything, build its module and print it, for example
`lake build Erdos.Proofs.P1186ExFinal` and then `lake env lean ../verification/Headline.lean`.

## 6. What is not checked

- That the upstream definitions express the problem (see Section 2). The small-case comparison with OEIS checks the
  counting convention only for n ≤ 26.
- The prose proofs of the paper. The Lean proofs do not depend on them, but the continuum cut-cell lemma and its discrete
  transfer (Section 5 of the paper) are not formalised (Lean proves a weaker integer inequality directly) and have been
  checked only by AI readers and by small-case computations.
- The correspondence between the Lean interface of Theorem C and the claim's own text, beyond one AI audit against the
  claim's TeX source (`REVIEWS.md`, Section 6). Theorem C does not depend on it: its statement is the upstream one. But
  "formalises the claim" is the project's reading of the claim, with five stated departures (`PROVENANCE.md`).
- The parts of the claim that are not formalised: its equality case and corollary, the existence of the limit, the
  claim's statement for measurable functions, its own certificates.
- Everything in Section 8 of the paper (the evidence): the certificates at L = 32, 192, 512, the gap law and all
  floating-point values are checked by Python only, or not at all.
- Novelty (`LITERATURE.md`).
- Any human reading of the Lean sources: so far as we know there has been none.
