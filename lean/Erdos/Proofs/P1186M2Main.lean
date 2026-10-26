import Erdos.Proofs.P1186LowMain
import Erdos.Proofs.P1186M2Low
import Erdos.Proofs.P1186M2Cert64
import Erdos.Proofs.P1186M2Cert128
import Erdos.Proofs.P1186M2Cert256

/-!
# Erdos 1186 - the MODEL2 lower bound, assembled (night 2, 2026-10-26)

Glue of the two night-2 MODEL2 lanes over the shared interface `Erdos.Proofs.P1186M2`:
- lane lean1186c, `Erdos1186Night2M2.lower_of_cubeLB` (`P1186M2Low*.lean`): for every even `L ≥ 4`, a lower bound
  `xᵀ C x ≥ -σ` on the cube `[-1,1]^L` (`CubeLB L σ`) gives `1/16 - (L + σ)/(4L²) ≤ δ 3`
  (`problems/1186/MODEL2.md`, Theorems 1-2: the exact cell-area kernel of the PRS08 count plus the cut-cell inequality);
- lane lean1186d, `Erdos1186Night2M2.cubeLB64` / `cubeLB128` / `cubeLB256` (`P1186M2Cert64*.lean`, `P1186M2Cert128*.lean`,
  `P1186M2Cert256*.lean`): the exact Shor + triangle-cut certificates `problems/1186/data/sdp_model2cuts_L64.json` /
  `L128.json` / `L256.json`, checked by the kernel.

`δ` is the verbatim upstream definition (formal-conjectures c83a94d) copied in `P1186.lean`. The upper bound is the
day-1 `erdos_1186.variants.prs_bounds_upper` (`δ 3 ≤ 117/2192 = 0.0533759`).

Status of the numbers: `0.0531199` (L = 64), `0.0533115` (L = 128) and `0.0533616` (L = 256) are above PRS08's 1675/32768 = 0.0511170 and
the uncertified 0.052341 of Sjoland-Kivinen (arXiv:1408.1088, Section 8). Not found in print; the MODEL2 relaxation
is this repo's own (lane sdp1186m) and has not been refereed by anyone outside it. See `problems/1186/README.md` (E8)
for the unrefereed proof claim on the problem page.
-/

namespace Erdos1186Day

open Erdos1186Night2M2

/-- MODEL2 at `L = 64`: `δ 3 ≥ 1782409/33554432 = 0.0531199`. -/
theorem delta3_ge_model2_L64 : (1782409 / 33554432 : ℝ) ≤ δ 3 :=
  lower_of_cubeLB64 cubeLB64

/-- MODEL2 at `L = 128`: `δ 3 ≥ 1788837/33554432 = 0.0533115`. -/
theorem delta3_ge_model2_L128 : (1788837 / 33554432 : ℝ) ≤ δ 3 :=
  lower_of_cubeLB128 cubeLB128

/-- Both bounds proved in this repo: `0.0533115 ≤ δ 3 ≤ 0.0533759`. -/
theorem delta3_bounds_model2_L128 : (1788837 / 33554432 : ℝ) ≤ δ 3 ∧ δ 3 ≤ 117 / 2192 :=
  ⟨delta3_ge_model2_L128, erdos_1186.variants.prs_bounds_upper⟩

/-- MODEL2 at `L = 256`: `δ 3 ≥ 14324135/268435456 = 0.0533616`. -/
theorem delta3_ge_model2_L256 : (14324135 / 268435456 : ℝ) ≤ δ 3 :=
  lower_of_cubeLB256 cubeLB256

/-- Both bounds proved in this repo: `0.0533616 ≤ δ 3 ≤ 0.0533759`. -/
theorem delta3_bounds_model2_L256 : (14324135 / 268435456 : ℝ) ≤ δ 3 ∧ δ 3 ≤ 117 / 2192 :=
  ⟨delta3_ge_model2_L256, erdos_1186.variants.prs_bounds_upper⟩

end Erdos1186Day
