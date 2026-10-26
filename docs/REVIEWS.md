# Internal reviews and how their findings were resolved

Before this release the work was reviewed by **AI systems** (Claude, Anthropic); none of these reviews is a human or
journal review. They are recorded here so that readers can see what was checked, what was found and what changed. The
paper has not been peer reviewed, and no human has read it or the Lean sources of Theorem C. Section 1 concerns the
proof claim behind Theorem C; Section 2 the research note of Theorem B; Sections 3 to 5 the manuscript; Section 6 the
audit of the Theorem C formalisation against the claim; Section 7 the audits made before release.

## 1. Reviews of the proof claim (26 October 2026, before its formalisation)

Three read-only AI agents of the research project examined the claim posted on erdosproblems.com/1186 (see
`PROVENANCE.md`). Their reports stay in the research project's records; this is a summary of them.

- **The first** read the argument and re-derived its first three steps with its own code. It checked the exact finite
  identity behind the counting reduction for every n = 3, ..., 549 against a brute-force count, checked the value -5/137
  of the functional at the 12-block profile exactly, re-derived the bathtub and cell-pair lemmas and tested the resulting
  pointwise inequality in 120 exact and about 400 random cases (no violation), and checked that the five density ranges
  cover [0, 1/2]. Verdict: **undetermined end to end, with no gap found.** It did not reproduce the finite certificates.
- **The second** rebuilt the five finite problems from the claim's text, in its own reading of the definitions, and
  produced exact certificates of its own (with its own semidefinite code and exact rationals), each with a bound at
  least the constant printed in the claim and with Gram matrices positive definite in exact arithmetic. It wrote out the
  implication from the five inequalities to δ₃ ≥ 117/2192. Its certificates are the starting data of
  `computation/theorem-c/data/certs_rev1186c.json`. It saved the claim's PDF report and extracted its text, against its
  brief's no-download rule; it ran none of the claimant's code, and the files were deleted.
- **The third**, working from the definitions only (it read and ran none of the second agent's code), re-derived the
  anchors (the 11 edges of the profile from the Lean colouring, the functional value -5/137, the linear term and its
  zeros), found the same cell constants and cut lists as the second agent's data, and verified every certificate in
  exact arithmetic (Bareiss elimination on all four slabs, a second method on the two without triangle terms). It also
  ran 1360 exact random tests of the pointwise inequality (no violation).

None of them ran or checked the claimant's own certificates, and none proved the lemmas of the argument as proofs; the
finite inequalities were checked in the reviewers' reading of the definitions. That is not a referee report. The Lean
formalisation (Theorem C) was written afterwards, against the Lean definitions, from the project's reading of the
argument.

## 2. Review of the research note of Theorem B (26 October 2026)

One AI agent (a fresh Claude Opus agent) was asked to break the reduction, the cell geometry, the cut-cell lemma and the
cover inequality of the research note on the sharper cover, without reading its scripts. It found no error. It did not
check any certificate or table. Its report stays in the research project's records.

## 3. First AI referee of the manuscript (26 October 2026)

A fresh Claude agent, with no access to the manuscript lane's reasoning and told to find errors, read an earlier draft
and checked it against the research repository's sources, scripts and logs. Its own scripts re-derived the identity, the
strip cover, the cell geometry, the cut-cell lemma, the 12-block counts and (by Bareiss elimination) the positive
definiteness of the L = 32 to 256 certificates. It reported **no blocking problem** and confirmed that the Lean statements
and definitions equal the upstream ones, that the axioms are standard, that every certificate number, cut count and gap
value equals the JSON data and logs, and the integrity of the package (189 modules at the time, manifest). It did not
check the Lean proofs beyond their statements and axioms, did not run the Lean build, and checked the section on the
claim only against the project's reviewer reports. Its findings, and what was done:

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | The text said the claim's certificates were "reproduced by AI reviewers"; the reviewers re-certified the finite problems with their own certificates built from the claim's text and never ran the claimant's | Reworded in the Introduction, Table 5 and Section 10 |
| 2 | major | Section 10 said two reviewers rebuilt the finite problems; only one did, and the other re-verified that one's certificates; a quotation was not verbatim | Rewritten with the three reviewers' roles and the verbatim phrase |
| 3 | major | Novelty overstated: the claim's superseded section already uses a cell model with a Shor + triangle-cut relaxation (certified 0.0532492 at L = 256) | "Credit and origin" paragraph added; the relaxation is stated as not new; what is specific (the cover with its cut-cell lemma, the certificates, the Lean check) is "not found in the searches described" |
| 4 | major | Floating-point evidence presented as exact; ceilings mislabelled as float; an "about 10⁻⁷" gap was wrong | Every float value marked (float); ceilings relabelled as rigorous at exact rational cube points (recorded, not recomputed); gaps stated as 1.4 to 4.0 × 10⁻⁷ |
| 5 | major | No readable proof of the discrete cut-cell inequality that the cover inequality needs; the continuum lemma was called "exposition" | Lemma 5.4 (step-function transfer, error w/2 per cell), Corollary 5.5, a rewritten proof of Theorem 5.7 (the cover inequality), Remark 5.6 on what Lean proves (the weaker 4w + 16, directly in integers); new exhaustive check `computation/small-cases/disc_cutcell_check.py` (w ≤ 10, largest excess 4) |
| 6 | major | `\top` stored as TAB + "op" (the PDF read "xopCx") | Repaired at 20 places; the PDF text layer has no TAB and no "xop" |
| 7 | minor | Lower bounds rounded up; the enclosure's upper end was below 117/2192; a gap × L² summary hid 0.94 | Certified lower bounds printed rounded down; enclosure [0.0533615, 0.0533760]; the range 0.94 to 1.06 stated |
| 8 | minor | Statements about who reviewed and who read what were inaccurate | Corrected in Section 7.5, Section 9 and `refs.bib` |
| 9 | minor | Lemma 3.1 needed a two-sided bound; Corollary 5.6 needs step 2L in the monotonicity lemma; supersaturation; an unclear phrase | Proofs repaired, phrase removed |
| 10 | minor | Module counts in Table 2 | Corrected (10 / 21 / 76 including top modules; 11 / 59 for the diagonal families) |
| 11 | minor | An argument of the OEIS check; the axioms of `cert128` and `cert256` were not printed; the axiom log was from the research repository; the L = 1024 certificate was not shipped; no hash list | Command fixed; the audit file was extended and re-run on the rebuilt package; L = 1024 marked "not shipped"; hash list created |
| 12 | minor | Notation reuse; "K4" reads as K times 4; internal lane names; Lean and Mathlib not cited; "everything the kernel checks is finite arithmetic" too strong; status-box conflation; "nothing newer" contradicted the rows of the claim; Graham attribution; an inconsistency about `probabilistic` | All fixed, except the notation reuse and the symbol K4, which are flagged (a sentence at the end of the Introduction says that letters are reused) |

## 4. Second AI referee of the manuscript (26 October 2026)

A fresh Claude agent, with a read-only brief on the revised text, tried to break every proof of Sections 2 to 6 and every
Theorem B certificate, and found **no blocking problem**. Its own scripts re-checked: Lemmas 2.2 and 3.1 exhaustively for
n ≤ 14 (L ∈ {2, 4, 6}); the 12-block constants and the exact count; the cell geometry by brute force (L ∈ {4, 6, 8},
w ∈ {2, 4, 6}); the continuum cut-cell lemma (sympy and a numerical maximisation); the discrete lemma exhaustively over
sign vectors for w ≤ 12 (largest excess 4 for even w, 2 for odd w); a real-valued adversarial search for the cut-cell
corollary (minimum slack -1/2 against the allowed -w/2); the cover inequality exhaustively for (L, w) ∈ {(4, 2), (4, 4),
(6, 2), (8, 2)} and at random beyond; Corollary 5.8; the certificate algebra; an independent rebuild of the matrix N from
the JSON data with its own K4 and its own Bareiss check for L = 32, 64, 128, 192, 256; every decimal and rounding
direction; the package hashes and byte equality with the research repository (at the commit named in `PROVENANCE.md`); the build log; and a re-run
of `fidelity_check.py` against a local clone of Formal Conjectures at `c83a94d` (all OK). Not checked by it: the Lean
proofs themselves, positive definiteness at L = 512, L = 1024 and the strip ceilings, the bibliographic claims, the
claim's own mathematics, the model names.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| M1 | major | The idea of not charging cut cells at worst case is already in the claim's superseded cell model; the paper only said "a cell model of the same kind" | Abstract, Introduction and "Credit and origin" rewritten: that idea and the relaxation are not new; what is specific is the cut-cell estimate (weights 1/8, 3/8), the retained parity term, the higher float minima (stated as a float comparison), the exact certificates and the Lean proofs |
| M2 | major | The Introduction and Table 5 dropped the qualifiers on what the three reviewers of the claim established | Both rewritten to match Section 10 (verdict "undetermined, no gap found"; finite problems rebuilt from the claim's text and certified in the reviewer's reading of the definitions; lemmas not proved as proofs; the claimant's certificates not run) |
| M3 | major | Section 10's paragraph on the Lean state said more than the lane reports support; the Python checks of the certificates were presented as stronger than they are (same author; identity tested at random points); no recorded axiom output for `delta3_eq_of_regions` | Each sentence corrected; the limits of the certificate checks stated |
| M4 | major | "Checked by machine" in the status box and the Discussion covered the prose lemmas, which are not formalised | Both rewritten: the Lean statements and the certificates are machine-checked; the prose proofs of Lemma 5.2 to Theorem 5.7 are not formalised and have had only AI and small-case checks |
| m1 | minor | Table 4 quoted the ceiling formula with the sharper cover's bound instead of the strip formula | Caption corrected |
| m2 | minor | σ used for the cut signs and for the cube bound | Cut signs renamed ε |
| m3 | minor | `lemA` is proved for even w only | Stated in Remark 5.6 |
| m4 | minor | "the parity of p decides which two" holds for a-blocks only | Both cases spelled out after Lemma 5.1 |
| m5 | minor | A paragraph on local minima had an unnecessary hypothesis | Rewritten |
| m6 | minor | "Solver slack, not a property of the model" asserted from a float primal | "Most likely solver slack ... (we did not prove that)" |
| m7 | minor | "Findings incorporated" while two items were only flagged | The review paragraph says two AI referees, final text not re-refereed, no human read it |
| m8 | minor | The Discussion contrasted the claim's method with ours too sharply | Reworded |
| m9 | minor | Rounding of 117/2192 in Table 5; shipped Lean docstrings round certified lower bounds up | "..." added; Section 7.2 says that the comments round to nearest and the rational is what is proved. The Lean files were not edited (see `../README.md`, "Known errors") |
| m10 | minor | "Every figure" in Section 9; lane jargon | Reworded |
| m11 | minor | The abstract said "under the direction of the author" while Appendix B leaves the author's role open; the relaxation was listed as AI-produced although standard | Abstract and Appendix B reworded |
| m12 | minor | "(any L ...)" in Table 2 | "any even L" |
| m13 | minor | Two build-time figures measured under different conditions were compared | Stated as not comparable |
| m14 | minor | "Not formalised" versus the partial formalisation | "Not fully formalised" |
| m15 | minor | The negative controls of the Theorem B checker were stated as fact although only the formalising lane ran them | Stated as that lane's report, with no log, not re-run |
| m16 | minor | Lean proves positive semidefiniteness for the diagonal certificates, not definiteness | Corrected after Theorem 3.3 |
| m17 | minor | Placeholders in the readiness file; byte counts of the closure differed between a CRLF and an LF copy | Placeholders filled; the difference explained in the package README |

## 5. Third AI referee of the manuscript (26 October 2026)

A fresh Claude agent read, with a read-only brief, the draft that contained Theorem C. Its report is not shipped; the
list below is from the manuscript lane's notes of it, which record no blocking finding (the notes may be incomplete).
Its findings concerned statements about the Theorem C lanes and the research repository that were stronger than the
ledger and the lane reports support.

| # | Finding | Resolution |
|---|---|---|
| T1 | History of the formalisation: wrong times and commit attributions | Corrected: the assembly was merged at about 09:30; the commit of 12:06 added `P1186ExFinal` and `P1186ExCertCtl`, and the next one (12:07) changed only the import list and notes (the commits are named in `PROVENANCE.md`) |
| T2 | Merge and build status of `agent/n3c` stated from an earlier look, not from the ledger | Rewritten from the ledger (a merge without commit; a gated `lake build` of the 131 certificate-side modules running); the rebuild for the package used plain `lean` |
| T3 | "Rebuilt here" sentences written before the rebuild had finished | Made conditional, then filled in with the result |
| T4 | The description of the certificates was loose | A quadratic form with an exact integer matrix plus nonnegative multiples of valid inequalities; integer data from a reviewer's reconstruction |
| T5 | The statement check was described as proving more than it does | Stated as: name, type and absence of binders of the upstream statement, and the namespace of the development |
| T6 | Negative controls described too broadly | Region 5 only; the nine bathtub examples are a lane's report, not re-examined; none for ranges 1 to 4; a Cholesky entry changed by 1 is not rejected (the row has margin) |
| T7 | Model names of the Theorem C lanes presented as settled | Appendix B and the authorship note say that the ledger disagrees with some commit trailers |
| T8 | The claim's author was not named where Theorem C is introduced | Named in the Introduction |
| T9 | The 11 modules shared between the two closures were not listed | Listed in the package README |

The text was not re-refereed after this round. The sentences written after the third report have been read by no
referee.

## 6. Audit of the Theorem C formalisation against the claim (26 October 2026)

An AI agent of the research project compared the Lean development of Theorem C with the claim. It read the claim's
post, its report page and its TeX source (draft v0.2 in the claimant's public repository) as text; it did not read the
PDF, and it could not confirm that this source is the version linked on 5 October. It ran no code of the claimant.
It found that the Lean development follows the claim's argument step by step, in a discrete form at n = 1096 w: the
expansion is the discrete form of the claim's identity E(σ) = ∫hσ + Q(φ*σ); the bathtub part is the claim's Lemma 2
with the claim's rule for the constants a_i, b_i; the pair part is the bound used in the proof of the claim's Lemma 3;
the function L, the five ranges, the symmetry and the two grids are the claim's (the grids agree point for point with
those of the claimant's published certificates for the ranges [1/5, 3/10] and [2/5, 9/20]; the other three
certificate files were not opened). It listed five departures, which the paper and `PROVENANCE.md` state: the counting
step, the value -5/137, ±1 colourings only, `RegionLB` proving L ≥ 0 rather than L ≥ B_j > 0 (so the equality case,
its corollary and the existence of the limit are not formalised), and the project's own certificates. The claimant's
values of a_i, b_i (which their certificates do not store) were not compared with the project's, only the rule that
produces them. The claim's Lemma 1 is not formalised and is not needed.

The claim, its reviewers, the formalising agents and this auditor all used Claude models, so the audit cannot exclude a
misreading of the claim that they share.

## 7. Audits of 26 October (coordinator)

*Placeholder: the coordinating agent will add its audits of this repository and of the final manuscript here before
release.*

## What none of the reviews did

None of them was done by a human. None ran the claimant's code or checked the claimant's certificates; the Lean
interface of Theorem C was compared with the claim's TeX source by one AI agent only (Section 6), not with its PDF. None read the Lean proofs of Theorem C beyond their
statements and axioms. None replaced journal peer review.
