import Erdos.Proofs.P1186Low
import Erdos.Proofs.P1186Cert128
import Erdos.Proofs.P1186Cert256

/-!
# Erdos 1186 - the PRS08 lower bound, assembled (night 2, 2026-10-26)

Glue of the two night-2 lanes over the shared interface `Erdos.Proofs.P1186Prs`:
- lane lean1186a, `Erdos1186Night2.lower_of_cert` (`P1186Low.lean`): every even `L` and every diagonal
  certificate `DiagCert L d` give `prsBound L d ≤ δ 3` (Parrilo-Robertson-Saracino 2008, Sections 2-3);
- lane lean1186b, `Erdos1186Night2.cert128` / `cert256` (`P1186Cert128*.lean`, `P1186Cert256*.lean`): the exact
  certificates `problems/1186/data/sdp_dn_L128.json` and `sdp_dn_L256.json`, checked by the kernel.

`δ`, `monoCount`, `minMonoCount` are the verbatim upstream definitions (formal-conjectures c83a94d,
`FormalConjectures/ErdosProblems/1186.lean`) copied in `P1186.lean`. `erdos_1186.variants.prs_bounds` below has the
upstream statement verbatim. `delta3_ge_L256` is PRS08's own method at `L = 256` (0.0516250 > 1675/32768 = 0.0511170):
not found in print, but an instance of PRS08's method, and below the uncertified 0.052341 of Sjoland-Kivinen
(arXiv:1408.1088, Section 8). Mathematics: [PRS08]; nothing new in the method.
-/

namespace Erdos1186Day

open Erdos1186Night2

/-- The left half of upstream `erdos_1186.variants.prs_bounds` (PRS08, `L = 128`). -/
theorem erdos_1186.variants.prs_bounds_lower : (1675 / 32768 : ℝ) ≤ δ 3 :=
  lower_of_cert128 d128 cert128 sum_d128

/-- Upstream formal-conjectures c83a94d `erdos_1186.variants.prs_bounds`, statement verbatim. -/
theorem erdos_1186.variants.prs_bounds : 1675 / 32768 ≤ δ 3 ∧ δ 3 ≤ 117 / 2192 :=
  ⟨erdos_1186.variants.prs_bounds_lower, erdos_1186.variants.prs_bounds_upper⟩

/-- PRS08's method at `L = 256`: `δ 3 ≥ 6928985/134217728 = 0.0516250`. -/
theorem delta3_ge_L256 : (6928985 / 134217728 : ℝ) ≤ δ 3 := by
  have h := lower_of_cert 256 (by norm_num) (by decide) d256 cert256
  rwa [prsBound_d256] at h

end Erdos1186Day
