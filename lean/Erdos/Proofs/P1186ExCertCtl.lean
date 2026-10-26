import Mathlib
import Erdos.Proofs.P1186ExCert5

/-!
# Erdos 1186 - negative controls of the certificate checkers (lane excert, night 3)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is
its author's.  The kernel checks of `P1186ExCert*` are `decide +kernel` evaluations of Boolean / integer equations;
a check that always succeeded would prove nothing.  So, for region 5 (the one with triangle terms on grid `G8`), each
claimed number is corrupted by one unit and the corrupted claim is REJECTED (also by the kernel), while the true
claim is accepted.
-/

namespace Erdos1186Ex.R5

open Erdos1186Ex

/-- the true tables are accepted by the entry checks. -/
example : constChk tabs G8 (Tri.ofPacked triW triCc triL triQR) = true := by decide +kernel
example : linChk tabs G8 (Tri.ofPacked triW triCc triL triQR) 7 = true := by decide +kernel
example : pairChk tabs G8 (Tri.ofPacked triW triCc triL triQR) 3 0 = true := by decide +kernel

/-- a constant off by one, a linear entry off by one, a quadratic entry off by one: each is rejected. -/
example : constChk tabs G8 (Tri.ofPacked triW (triCc + 1) triL triQR) = false := by decide +kernel
example : linChk tabs G8 (Tri.ofPacked triW triCc (triL + 2 ^ (triW * 7)) triQR) 7 = false := by decide +kernel
example : pairChk tabs G8 (Tri.ofPacked triW triCc triL (triQR.map (· + 1))) 3 0 = false := by decide +kernel

/-- a dominance row (`E = N - C C^T` row-diagonally dominant) is accepted for the true Cholesky data and rejected when one Cholesky entry is changed by `10^12` (a change by `1` keeps that row dominant, which is fine: the certificate only needs SOME valid `C`). -/
example : domRow tabs 100 = true := by decide +kernel
example : domRow { tabs with crows := tabs.crows.set 100 ((tabs.crows.getD 100 []).set 3 ((tabs.crows.getD 100 []).getD 3 0 + 10 ^ 12)) } 100 = false := by
  decide +kernel

/-- the exact integer sums of the (single) triangle group are sensitive to one unit: constant, linear and quadratic part. -/
example : gsum cterm grp0 ≠ Cg0 + 1 := by decide +kernel
example : gsum (lterm triW) grp0 ≠ Lg0 + 1 := by decide +kernel
example : gsum (qterm triW tabs.n) grp0 ≠ Qg0 + 1 := by decide +kernel

end Erdos1186Ex.R5
