import Mathlib

/-!
# Erdos 1186 - shared interface for the MODEL2 lower bound (night 2, definitions only)

`problems/1186/MODEL2.md` (lane sdp1186m, branch agent/n2s2): blocks `I_p = ((p-1)w, pw]` of `n = L w`, the exact
cell-area kernel `K` of `R_n = {(a,b) : 1 ≤ 2b - a ≤ n}` (Lemma 1), the cut-cell inequality (Lemmas 2-3), and
`4V ≥ ⌊(n-1)²/4⌋ + w² F(x) - 2Lw - 3n/2` with `F(x) = xᵀ C x - L`, `C = S + I + J/4`, `S = (K + Kᵀ)/2` (Theorem 1).
A lower bound `xᵀ C x ≥ -σ` on the cube then gives `δ₃ ≥ 1/16 - (L + σ)/(4L²)` (Theorem 2 / Section 9).

Lane `lean1186c` proves `lower_of_cubeLB` (the combinatorics, any even `L ≥ 4`, any `σ`); lane `lean1186d` proves
`CubeLB 64 σ64` and `CubeLB 128 σ128` from the exact Shor + triangle-cut certificates
`problems/1186/data/sdp_model2cuts_L{64,128}.json`. Do not change these definitions; add lemmas in your own module.
-/

namespace Erdos1186Night2M2

open Finset

/-- `4 K_pq` (MODEL2.md Lemma 1), 1-indexed `1 ≤ p, q ≤ L`: with `m = 2q - p - 1`, the cell `I_p × I_q` meets `R_n`
in all of it (`1 ≤ m ≤ L - 2`), three quarters (`m = 0` or `m = L - 1`), one quarter (`m = -1` or `m = L`), or nothing. -/
def K4 (L p q : ℕ) : ℕ :=
  if 1 ≤ 2 * (q : ℤ) - p - 1 ∧ 2 * (q : ℤ) - p - 1 ≤ (L : ℤ) - 2 then 4
  else if 2 * (q : ℤ) - p - 1 = 0 ∨ 2 * (q : ℤ) - p - 1 = (L : ℤ) - 1 then 3
  else if 2 * (q : ℤ) - p - 1 = -1 ∨ 2 * (q : ℤ) - p - 1 = (L : ℤ) then 1
  else 0

/-- `8 C = K4 + K4ᵀ + 8 I + 2 J` (so `C = (K + Kᵀ)/2 + I + J/4`). -/
def C8 (L p q : ℕ) : ℤ := (K4 L p q : ℤ) + K4 L q p + (if p = q then 8 else 0) + 2

/-- The quadratic form `xᵀ C x` over the indices `1..L`. -/
noncomputable def cform (L : ℕ) (x : ℕ → ℝ) : ℝ :=
  (1 / 8 : ℝ) * ∑ p ∈ Icc 1 L, ∑ q ∈ Icc 1 L, (C8 L p q : ℝ) * x p * x q

/-- `xᵀ C x ≥ -σ` on the cube `[-1,1]^L`. -/
def CubeLB (L : ℕ) (σ : ℚ) : Prop :=
  ∀ x : ℕ → ℝ, (∀ p ∈ Icc 1 L, |x p| ≤ 1) → -(σ : ℝ) ≤ cform L x

/-- The resulting lower bound `1/16 - (L + σ)/(4L²)` (MODEL2.md Theorem 2 with `Σ e` replaced by `σ`). -/
noncomputable def bound2 (L : ℕ) (σ : ℚ) : ℝ := 1 / 16 - ((L : ℝ) + (σ : ℝ)) / (4 * (L : ℝ) ^ 2)

/-- Sanity: the two certificate values of `problems/1186/data/sdp_model2cuts_L64/L128.json`. -/
example : bound2 64 (183671 / 2048) = 1782409 / 33554432 := by unfold bound2; push_cast; norm_num
example : bound2 128 (242779 / 512) = 1788837 / 33554432 := by unfold bound2; push_cast; norm_num

/-- Sanity of the kernel against Lemma 1 at `L = 8`. -/
example : K4 8 1 1 = 3 ∧ K4 8 2 1 = 1 ∧ K4 8 1 2 = 4 ∧ K4 8 8 8 = 3 ∧ K4 8 7 8 = 1 ∧ K4 8 8 1 = 0 := by decide

end Erdos1186Night2M2
