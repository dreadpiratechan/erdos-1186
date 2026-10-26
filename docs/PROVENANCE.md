# Provenance: how the results were produced

This file records who and what produced the results in this repository, in more detail than the paper's statement on
the use of AI. It contains the same facts as that statement, and the facts about how this repository was assembled.

## Summary

- **Theorems A and B.** The mathematics of Theorem B (the sharper cover of the counting region, its lemmas, the
  relaxation with triangle cuts and the exact certificates), all the Lean proofs of Theorems A and B, the scripts and
  the text of the paper were produced by AI agents of a research project at Quana Labs. Theorem A is a formalisation of
  known mathematics: its bounds, the strip cover and the 12-block colouring are those of Parrilo, Robertson and Saracino
  (2008); the colouring was found independently by Butler, Costello and Graham (2010).
- **Theorem C.** Its mathematics is **not ours**. It is the argument of an unrefereed proof claim, *The twelve-block
  colouring is optimal: δ₃ = 117/2192* (draft v0.2), posted on [erdosproblems.com/1186](https://www.erdosproblems.com/1186)
  ("Proof claims", 5 October 2026) by Carlos Toledo (user `carlos_toledo`). The claimant's post says that the claim
  was "Produced with substantial AI assistance (Claude)" and that they read and checked the mathematics line by line.
  AI agents of the research project wrote the Lean formalisation of that argument, as the project read it, in a
  discrete form with five stated departures (below). None of the claimant's files is included in this repository, and
  none of the claimant's code was run (see "The claim behind Theorem C" below).
- **The author**, Chandler Snively, owns and directs the research project at Quana Labs, a one-person independent lab.
  That work consisted of choosing the problem, commissioning the runs described below, and deciding what to publish.
  The records show no human mathematical contribution to the cover, the certificates, the proofs or the
  formalisation.
- **Models and tools.** The agents were Claude models (Anthropic). The coordinating agent, which wrote the interface of
  Theorem C and assembled the parts, ran Claude Opus 5.5; most lanes (separate agent sessions with their own briefs and
  reports), including the lane that wrote the manuscript, ran Claude Sonnet 5.5; a few lanes ran Claude Opus 5.5. The
  project's ledger does not record a model for every lane, and for some lanes it disagrees with the `Co-Authored-By`
  lines of their commits, so a per-lane attribution is not given here. The proofs are in Lean 4 (v4.27.0) with
  Mathlib (v4.27.0).

No independent human mathematician has checked the proofs, and the paper has not been peer reviewed. No human has read
the Lean sources of Theorem C beyond its statement, so far as we know. The author takes full responsibility for the paper
and this repository, including the accuracy of this account, and for correcting or withdrawing any result that is found
to be wrong.

Names such as `lean1186a` to `lean1186d`, `sdp1186m`, `sdp1186c`, `exglue`, `exstar`, `exbath`, `expair`, `excert`,
`excertsdp`, `rev1186m`, `rev1186c`, `ver1186c` and `paper1186`, which appear in Lean comments, script docstrings and
data headers, are identifiers of AI agent lanes of the research project, not people. "Night 2", "night 3" and the Lean
namespaces `Erdos1186Night2` and `Erdos1186Night2M2` name work sessions.

## Timeline

All dates are 2026; times are Pacific Daylight Time, from the research repository's commits.

| Date and time | What was produced | By |
|---|---|---|
| 23 October | Lean proofs of δ₃ ≤ 117/2192 (the upper half of Theorem A, from the 12-block colouring), of the probabilistic bound and of van der Waerden positivity (research commit `a8ebdb4`) | AI agents (Claude) |
| 26 October, 00:19-02:43 | The lower half of Theorem A: the strip-cover reduction for every even L, the kernel-checked diagonal certificates at L = 128 and 256, and the upstream statement `prs_bounds` (`4be2764`) | AI agents (Claude) |
| 26 October, 02:22-06:34 | Theorem B: the sharper cover and its lemmas, its exact certificates, the Lean reduction `lower_of_cubeLB`, the integer certificate checker and the certificates at L = 64, 128, 256; δ₃ ≥ 14324135/268435456 in Lean (`99fec40`) | AI agents (Claude) |
| 26 October, 00:20-07:15 | Three read-only AI reviews of the proof claim (see `REVIEWS.md`, Section 1) | AI agents (Claude) |
| 26 October, 08:10-12:07 | Theorem C: the interface `P1186Ex.lean` and the grid data (`47bee1f`) and the assembly `P1186ExMain.lean`, by the coordinating agent; the star, pair, bathtub and assembly parts (merged by `b23e2f8`, about 09:30); the Python certificates of the five finite statements; the Lean certificate checker, the five kernel-checked certificates and `P1186ExFinal` (`97b5bfa`, 12:06; branch tip `f726409`, 12:07, branch `agent/n3c`) | AI agents (Claude); the coordinating agent ran Claude Opus 5.5 |
| 26 October, 13:24-15:22 | In the research repository: every one of the 131 certificate-side modules of Theorem C built from source with its own gated `lake build` (13:24-15:13, all successful), and the merge commit `202f974` ("merge agent/n3c", 15:22) on master; its Lean files `P1186*` are byte-identical to those of this repository (checked for all 342) | the coordinating agent |
| 26 October, afternoon | An audit of the Theorem C formalisation against the claim's TeX source (`REVIEWS.md`, Section 6) | an AI agent (Claude) |
| 26 October, day | The manuscript, a reproducibility package, two standalone rebuilds of the shipped Lean files with plain `lean` (08:42-09:29 and 12:36-14:04), three AI referee reviews of the manuscript (`REVIEWS.md`, Sections 3-5) | AI agents (Claude); the manuscript lane ran Claude Sonnet 5.5 |
| 26 October, evening | This repository: assembled from the package and the research repository, with new verification scripts; a run of `verification/run_all.sh` on a fresh clone (its logs are in `verification/logs/`) | an AI agent (Claude) |

## What is in this repository, and where it came from

- **`lean/Erdos/Proofs/` (342 files).** Byte-identical copies of the research repository's git blobs: 191 files exist
  at commit `47bee1f` (the 189 modules of Theorems A and B and the two interface files of Theorem C), and they are
  identical at commit `f726409` of the branch `agent/n3c`; the other 151 exist at `f726409` only. All 342 are LF
  text. Their SHA-256 values and sizes are in `verification/lean_modules.sha256` (copied from the research package),
  and `verification/source_scan.py` checks every file against it. The module `P1186ExCertCtl` (negative controls of
  the Theorem C checker) is one of the 342; it is not imported by Theorem C.
- **`lean/lakefile.toml`, `lean/lake-manifest.json`, `lean/lean-toolchain`, `lean/Erdos1186.lean`.** The toolchain
  file and the package entries of the manifest (Mathlib `a3a10db0e9d66acbebf76c5e6a135066525ac900`, tag `v4.27.0`,
  and its dependencies) are those of the research repository; only the manifest's own `name` field was changed, to
  the package name `erdos1186`. The lakefile was written for this repository: its Lean options are those of the
  research repository, except that `warn.sorry = false` is not set (so a `sorry` would show in the build log). The
  root module `Erdos1186.lean` is new; it imports the modules of Theorems A, B, C and the controls.
- **Comments in the Lean files** mention research notes, scripts and lanes of the research project; the proofs do not
  depend on them. They were not edited, so that the files stay identical to the research version. The known errors in
  them are listed in `../README.md`.
- **`computation/`.** The Theorem B scripts and data, the small-case scripts and their logs are byte-identical to the
  research package; the Theorem C scripts and data are the blobs of `f726409` (`problems/1186/exact/`), with the
  path changes listed in `computation/README.md`. `computation/theorem-b/run_checks.sh` was rewritten to record exit
  codes.
- **`verification/`.** `fidelity_check.py` and `build_closure.py` are byte-identical to the research package.
  `Headline.lean`, `AxiomAudit.lean`, `make_upstream_pin.py`, `make_manifest.py` and `run_all.sh` were adapted from
  the release of the project's Erdős Problem 357 paper; `source_scan.py`, `regen_check.py` and `number_checks.py` are
  new. `upstream/` holds the upstream Formal Conjectures file verbatim (commit `c83a94d785d0`, 22 October 2026) and its
  licence. `earlier-runs/2026-10-26-package/` holds the logs of the checks made on the research package before this
  repository existed, with two local folder names replaced by `<research-repository>` and `<paper-workspace>`.
- **`manuscript/`.** `main.tex`, `refs.bib` and `main.pdf` are copies of the manuscript workspace's `paper.tex`,
  `references.bib` and `paper.pdf` at the manuscript workspace's commit `6912e94` (26 October 2026, 15:24 PDT;
  SHA-256 of the three files: `891e4836…`, `c731a3a8…`, `a597b4d6…`). They are a draft, copied unchanged, and will be
  replaced by the final text. They still refer to the paper package's layout (`reproducibility/...`, `checks/...`), and
  `main.tex` loads the bibliography as `references` (`ibliography{references}`), so compiling it here needs
  `refs.bib` renamed or that line changed; no `.bbl` file is included.

## The claim behind Theorem C

The claim was posted on the problem's page on 5 October 2026 (the post links a PDF, a report page, the source in the
claimant's public repository and an archive; see `manuscript/refs.bib`). The post says that the claim was "Produced
with substantial AI assistance (Claude)", that the claimant read and checked the mathematics line by line, that it is
not peer reviewed and that it is not formalised in Lean. Its argument has four steps: a counting reduction to a
quadratic functional, an expansion around the 12-block profile, a bathtub lemma and a cell-pair lemma that bound the
functional below by a function of finitely many cell averages, and five finite certificates covering the density range
[0, 1/2].

What the research project took from it, and what it did not:
- **Its argument, as text.** The architecture of the Lean interface `P1186Ex.lean` (the four steps, the two grids of
  130 and 146 cells, the five density ranges, the split into bathtub and pair parts, the rule for the cell constants)
  is the claim's, as the project read it. The interface was written by the coordinating agent; the proofs of the parts,
  with their explicit error terms, are the lanes' own.
- **Five departures.** An audit by an AI agent of the project (26 October 2026; `REVIEWS.md`, Section 6) compared the
  Lean development with the claim's TeX source (draft v0.2, read as text; the PDF was not read) and found that it
  follows the claim's argument step by step, in a discrete form at n = 1096 w, with five departures:
  1. the counting step uses the exact ±1 identity at n = 1096 w and a monotonicity lemma, where the claim uses the
     counting lemma of Parrilo, Robertson and Saracino with step functions;
  2. the value -5/137 of the functional at the 12-block colouring comes from the paper's cover inequality, where the
     claim computes it exactly;
  3. only ±1 colourings are treated, where the claim covers every measurable φ: [0, 1] → [-1, 1];
  4. the five finite statements `RegionLB` prove L ≥ 0, weaker than the claim's L ≥ B_j > 0, so the claim's equality
     case, its corollary and the existence of the limit (the claim's Theorem 1; Theorem C is the Formal Conjectures
     statement about the `liminf`) are not formalised;
  5. the certificates are the project's own, not the claimant's.
  The claim, its reviewers, the formalising agents and the auditor all used Claude models, so these checks cannot
  exclude a misreading of the claim that they share. That does not affect the truth of Theorem C, whose statement is
  the upstream one.
- **No files and no code.** None of the claimant's files (paper, source, certificates, programs, reports) is included
  in this repository, and none of the claimant's code was run. The integer certificates of the five finite statements
  were built by the project (`computation/theorem-c/make_certs.py`) from the exact certificates of a reviewing agent
  (`computation/theorem-c/data/certs_rev1186c.json`), which that agent built from its own reading of the claim's text
  with its own code. That agent saved the claim's PDF report and extracted its text, against its brief, which forbade
  downloads; it ran none of the claimant's code, and the coordinating agent deleted both files the same night. The
  auditing agent read the claim's post, report page and TeX source as text, and compared the grids with two of the
  claimant's published certificate files; it ran no code of the claimant.
- **No contact.** The research project's agents have not contacted the claimant about this formalisation.

## Records not included

The research repository is kept privately by Quana Labs. Its commit history, research notes, the agents' briefs and
reports, the coordinating agent's ledgers and the session logs stay there. This file, `REVIEWS.md` and `LITERATURE.md`
summarise what is needed to assess the results. The prompts, agent configuration and internal infrastructure of the
research project are not part of this release.

## State of the research repository

On 26 October 2026 the branch `agent/n3c` (Theorem C) was merged into the research repository's master branch (merge
commit `202f974`, 15:22), after each of its 131 certificate-side modules had been built from source there with its own
gated `lake build` (13:24-15:13, all successful). According to the coordinating agent, a `#print axioms` of Theorem C,
of `delta3_eq_of_regions` and of the five `region` theorems in that tree printed `[propext, Classical.choice,
Quot.sound]` for each, and the research repository's own verification command reported 861 proved statements and none
with `sorry`. The Lean files `P1186*` at `202f974` are byte-identical to the 342 files of this repository. Nothing here
depends on that build: the build of record is the clean `lake build` of this repository in `verification/logs/`.
