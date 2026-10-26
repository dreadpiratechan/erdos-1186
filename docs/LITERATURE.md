# Literature search and novelty

This file describes the literature search behind the paper's statements on prior work (Section 9 of the paper, "Prior
figures and novelty"). The searches were done with AI in October 2026; how much of each source was read is recorded in
the `verification` fields of `manuscript/refs.bib` and summarised below.

**Novelty has not been established.** A search can find prior work; it cannot show that none exists. The paper
therefore says only "not found in the searches described". The gaps in coverage are listed at the end.

## Figures for δ₃ and their status

"Lean" means a proof against the Formal Conjectures definitions with the three standard axioms only.

| Figure for δ₃ | Source | Status |
|---|---|---|
| ≤ 1/16 = 0.0625 | random colouring (the probabilistic method, as stated on erdosproblems.com/1186 and in Formal Conjectures) | classical; its Lean statement `probabilistic` is proved in the same development (not a claim of the paper) |
| ≥ 1675/32768 = 0.0511169… | Parrilo, Robertson and Saracino (2008) | refereed; Lean: Theorem A |
| ≤ 117/2192 = 0.0533759… | Parrilo, Robertson and Saracino (2008); the 12-block colouring was found independently by Butler, Costello and Graham (2010) | refereed; conjectured sharp; Lean: Theorem A |
| ≈ 0.052341 (lower) | Sjöland, with O. Kivinen (arXiv:1408.1088v3, Section 8) | numerical, degree-3 relaxation, no certificate ("work under progress") |
| the 12-block colouring is optimal among anti-symmetric colourings with at most 12 blocks | Greenwood, Kariv and Williams (Math. Comp. 2024; arXiv:2301.00336) | refereed; not a bound on δ₃ |
| ≥ 0.0516249, 0.0518729 (L = 256, 512) | this work, the method of Parrilo et al. | exact; Lean for L = 256; not claimed as a record |
| ≥ 0.0532492 (L = 256) | the proof claim of C. Toledo, its Section 7 (a cell model with Shor relaxation and triangle cuts, not used by its proof) | unrefereed; a reviewer reproduced the model's local-search minima to six digits; nobody here reproduced the certified bound; not Lean |
| ≥ 14324135/268435456 = 0.0533615… | this work (Theorem B) | Lean; "not found in the searches described" |
| = 117/2192 | the proof claim of C. Toledo, *The twelve-block colouring is optimal: δ₃ = 117/2192* (draft v0.2), on erdosproblems.com/1186 (5 October 2026) | unrefereed; its author reports checking it line by line, and the claim's report records an outside audit (auditor not named) that led to a correction (20 October 2026); three AI reviewers (one: "undetermined, no gap found"; one rebuilt the finite problems from the claim's text and certified them with its own certificates, in its reading of the definitions; a third re-verified those; the lemmas were not proved as proofs). Formalised in Lean as Theorem C of this repository (merged into the research repository's master branch and built there from source); the mathematics is the claimant's; no human referee |

The searches found no improvement of the bounds of Parrilo, Robertson and Saracino in print, no formal proof of them in
Formal Conjectures at commit `c83a94d785d0` (where the statements `prs_bounds`, `prs_conjecture`, `probabilistic`,
`van_der_waerden` and `erdos_1186` are `sorry`), and, apart from the proof claim, nothing on δ₃ newer than Parrilo et al.,
Greenwood-Kariv-Williams and Sjöland (De Loera, Ventura, Wang and Wesley, Discrete Appl. Math. 2025, compute optimal
colourings of small intervals for x + y = 2z and discuss the method of Parrilo et al., without a new bound for δ₃). A 2026 preprint by Yang and Mao (arXiv:2604.02115) concerns the
Butler-Costello-Graham conjecture on whether every pattern admits a colouring beating the random one; it states no value
or bound for δ₃.

What is **not** new in the paper's own method: a Shor relaxation with triangle inequalities is a standard device
(Shor 1987; the triangle inequalities are among the inequality classes of Padberg 1989). A cell model that charges each
cut pair its inside and outside areas instead of the worst case, bounded by such a relaxation, already appears in a
section of the proof claim that its proof does not use (its Section 7). What the paper believes is specific to its cover is the cut-cell estimate (weights
1/8 and 3/8), the retained parity term, the resulting higher minima (a comparison of two floating-point computations), the
exact certificates and the Lean proofs.

## Sources and how much of each was read

| Source | How much was read (October 2026) |
|---|---|
| Parrilo, Robertson, Saracino, J. Combin. Theory Ser. A 115 (2008) 185-192, arXiv:math/0609532 | the arXiv abstract and full text; journal data from the Formal Conjectures file |
| Butler, Costello, Graham, Experiment. Math. 19 (2010) 399-411 | the Project Euclid record and the abstract; an AI agent of the research project extracted the full text and searched it for the constant (it restates the bounds of Parrilo et al.) |
| Greenwood, Kariv, Williams, Math. Comp. (2024), arXiv:2301.00336 | the abstract; an AI agent extracted the full text and searched it for the constant |
| De Loera, Ventura, Wang, Wesley, Discrete Appl. Math. (2025) | Crossref record; the arXiv HTML searched by an AI agent for the method of Parrilo et al. and x + y = 2z: no new bound for δ₃ |
| Butler, Graham, Lu, *Unrolling residues to avoid progressions*, Math. Mag. 87 (2014) 83-94, arXiv:1209.2687 | Crossref record; the arXiv HTML states that two groups found the same colouring independently |
| Sjöland, arXiv:1408.1088v3 (2014) | the arXiv listing and Section 8 |
| Yang, Mao, arXiv:2604.02115 (2026) | the arXiv listing and the abstract; an AI agent extracted the full text and searched it for the constant |
| Erdős, *A survey of problems in combinatorial number theory*, Ann. Discrete Math. 6 (1980) 89-115, p. 93 | not read; the citation is the one of the research notes and of the Formal Conjectures file; no longer cited for the random bound |
| erdosproblems.com/1186 and its proof-claims page | read 26 October 2026 (the bounds, the remark that the upper bound is conjectured correct, one proof claim) |
| the proof claim of C. Toledo (the post, and the PDF, report page, TeX source and archive linked from it) | the post, the report page and the TeX source (draft v0.2) were read as text by an AI agent of the project on 26 October 2026; the PDF and the archives were not read, and the claimant's code was not run (see `PROVENANCE.md` for what a reviewing agent did) |
| Formal Conjectures, `FormalConjectures/ErdosProblems/1186.lean` at `c83a94d785d0` | full (vendored in `verification/upstream/`) |
| OEIS A121385 | the page, read 26 October 2026 |
| Shor (1987); Padberg (1989); Lean 4 (de Moura and Ullrich 2021); Mathlib (CPP 2020) | bibliographic data confirmed by web search only (publisher pages not opened); for Shor 1987 the Russian original was confirmed, the details of the English translation are **unverified** |

## Searches run

- Web and arXiv searches during October 2026 for improvements of either bound of Parrilo et al. and for the constants of
  the paper.
- The citing literature of Parrilo et al. and of Greenwood-Kariv-Williams, searched by an AI agent of the research project,
  which extracted the full texts of the papers it judged relevant and searched them for the constant.
- On 26 October 2026, on local snapshots, the AI agent that formalised Theorem C reported that none of the 660 open pull requests
  of Formal Conjectures mentions problem 1186, that the `lean-proofs` snapshot has no file for it, and that the database
  lists the problem as open with no formal solution; the first two checks were not repeated.
- A refresh on 26 October 2026 found no improvement of the bounds of Parrilo et al., no claim of δ₃ = 117/2192 other
  than the one formalised here, and no aiXiv paper on the problem. The database's data file then listed problem 1186 as
  open, with a formalised statement (since 20 October 2026) and formal status "unformalized"; the upstream file had a
  single commit (`4beab72`, 20 October 2026), its statements were still `sorry` on the main branch, and no open pull
  request or issue there concerned the problem.

## Coverage gaps and residual risks

- Other repositories of formal proofs were not searched systematically.
- Only the abstracts of Butler-Costello-Graham, Greenwood-Kariv-Williams and Yang-Mao were read by the agent that wrote
  the manuscript; their full texts were only searched for the constant.
- Erdős (1980) was not read.
- The claimant's PDF was not read; the Lean interface of Theorem C was compared with the claim's TeX source by one AI agent
  only (`REVIEWS.md`, Section 6).
- AI-assisted work on Erdős problems is active; claims could exist in places that these searches do not index.

Readers who know of relevant work are asked to write to lab@quanalabs.com. A missed reference will be added and
acknowledged in a new release and a replacement version of the paper.
