import Erdos.Proofs.P1186ExBathCell
import Erdos.Proofs.P1186ExBathC24a
import Erdos.Proofs.P1186ExBathC24b
import Erdos.Proofs.P1186ExBathC24c
import Erdos.Proofs.P1186ExBathC24d
import Erdos.Proofs.P1186ExBathC24e
import Erdos.Proofs.P1186ExBathC8a
import Erdos.Proofs.P1186ExBathC8b
import Erdos.Proofs.P1186ExBathC8c
import Erdos.Proofs.P1186ExBathC8d

/-!
# Erdos 1186 - Lemma 2 (bathtub) of the claimed proof of `δ 3 = 117/2192`: `BathOK G24` and `BathOK G8`

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's.

Route (all in this lane's modules `P1186ExBath*`):
* `P1186ExBathFU`: the sign table `Usg` of the PRS colouring on unit cells and its prefix sums `FU`;
* `P1186ExBathH2`: at scale `n = 1096 w`, `H2 w (p' w + j) = α_{p'} w + β_{p'} j + ε` for `0 ≤ p' ≤ 1095`, `1 ≤ j ≤ w`,
  `|ε| ≤ 2`, with the explicit integers `alphaF`, `betaF` (`H2_lin`);
* `P1186ExBathLib`: the discrete bathtub (layer-cake) lemma, the arithmetic-progression counting lemma, the ramp /
  level-count lemmas;
* `P1186ExBathCell`: soundness of the per-cell certificate (`cell_sound`): a passing `cellChk` gives the cell's
  bathtub inequality with an explicit constant;
* `P1186ExBathChk`, `P1186ExBathTab`, `P1186ExBathC*`: the executable check and its kernel evaluation on all
  130 cells of `G24` and all 146 cells of `G8`.
-/

namespace Erdos1186Ex

theorem chkRange_sound {G : Grid} {nuT : List ℤ} {tT : List ℕ} {a b i : ℕ}
    (h : chkRange G nuT tT a b = true) (h1 : a ≤ i) (h2 : i < b) : cellChk G nuT tT i = true := by
  unfold chkRange at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'_1.2 ⟨h1, by omega⟩)

/-- **Lemma 2 (bathtub) on the 130 cells of `G24`.** -/
theorem bathOK24 : BathOK G24 := by
  apply bathOK_of_chk G24 nuTab24 tTab24
  intro i hi
  have hN : G24.N = 130 := by decide +kernel
  rw [hN] at hi
  by_cases c1 : i < 26
  · exact chkRange_sound chk24a (by omega) c1
  by_cases c2 : i < 52
  · exact chkRange_sound chk24b (by omega) c2
  by_cases c3 : i < 78
  · exact chkRange_sound chk24c (by omega) c3
  by_cases c4 : i < 104
  · exact chkRange_sound chk24d (by omega) c4
  · exact chkRange_sound chk24e (by omega) hi

/-- **Lemma 2 (bathtub) on the 146 cells of `G8`.** -/
theorem bathOK8 : BathOK G8 := by
  apply bathOK_of_chk G8 nuTab8 tTab8
  intro i hi
  have hN : G8.N = 146 := by decide +kernel
  rw [hN] at hi
  by_cases c1 : i < 37
  · exact chkRange_sound chk8a (by omega) c1
  by_cases c2 : i < 74
  · exact chkRange_sound chk8b (by omega) c2
  by_cases c3 : i < 110
  · exact chkRange_sound chk8c (by omega) c3
  · exact chkRange_sound chk8d (by omega) hi

/-! ### Controls: the check accepts the true certificate and rejects corrupted ones (kernel-evaluated) -/

example : cellChk G24 nuTab24 tTab24 12 = true := by decide +kernel
example : cellChk G24 nuTab24 tTab24 129 = true := by decide +kernel
example : cellChk G8 nuTab8 tTab8 100 = true := by decide +kernel
/-- `ν` one too large: the profile does not stay above it. -/
example : cellChk G24 (nuTab24.set 12 (nuTab24.getD 12 0 + 1)) tTab24 12 = false := by decide +kernel
/-- `T` one too small: the slope sum exceeds it at some level. -/
example : cellChk G24 nuTab24 (tTab24.set 12 (tTab24.getD 12 0 - 1)) 12 = false := by decide +kernel
/-- `T` one too large: the interface's `b_i` is then too optimistic for it. -/
example : cellChk G24 nuTab24 (tTab24.set 12 (tTab24.getD 12 0 + 1)) 12 = false := by decide +kernel
/-- `ν` one too small: the interface's `a_i` is then too optimistic for it. -/
example : cellChk G24 (nuTab24.set 12 (nuTab24.getD 12 0 - 1)) tTab24 12 = false := by decide +kernel
example : cellChk G8 (nuTab8.set 100 (nuTab8.getD 100 0 + 1)) tTab8 100 = false := by decide +kernel
example : cellChk G8 nuTab8 (tTab8.set 100 (tTab8.getD 100 0 - 1)) 100 = false := by decide +kernel

end Erdos1186Ex
