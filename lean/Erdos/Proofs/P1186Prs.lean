import Mathlib

/-!
# Erdos 1186 - shared interface for the PRS08 lower bound (night 2, definitions only)

Parrilo-Robertson-Saracino, J. Combin. Theory Ser. A 115 (2008) 185-192 (arXiv:math/0609532), Section 3:
cover the parallelogram `0 < 2y - x ≤ n` by `L` strips; the cell matrix is `A = B + Bᵀ` with
`B i j = [j + 1 ≤ 2 i ≤ j + L]` (1-indexed, `1 ≤ i, j ≤ L`), and a diagonal certificate `d ≥ 0` with
`A + diag d ⪰ 0` gives `V(n) ≥ ½ (3/8 - c) n² (1 + o(1))`, `c = 1/(4L) + 1/4 + (Σ d)/(4L²)`.

This file fixes the definitions both night-2 Lean lanes build on, so their theorems glue without
translation: lane `lean1186a` proves `lower_of_cert` (any even `L`, any certificate) in
`P1186Low.lean`; lane `lean1186b` proves `DiagCert 128 d128` in `P1186Cert128.lean`.
Do not change these definitions; add lemmas in your own module.
-/

namespace Erdos1186Night2

open Finset

/-- PRS08's strip incidence, 1-indexed: `Bprs L i j = 1` iff `j + 1 ≤ 2 i ≤ j + L`. -/
def Bprs (L i j : ℕ) : ℕ := if j + 1 ≤ 2 * i ∧ 2 * i ≤ j + L then 1 else 0

/-- PRS08's matrix `A = B + Bᵀ` (so `A i i = 2` for `1 ≤ i ≤ L`). -/
def Aprs (L i j : ℕ) : ℕ := Bprs L i j + Bprs L j i

/-- The quadratic form `xᵀ A x` over the indices `1..L`. -/
noncomputable def qform (L : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (Aprs L i j : ℝ) * x i * x j

/-- A diagonal certificate: `d ≥ 0` on `1..L` and `A + diag d ⪰ 0`, as a quadratic-form inequality. -/
def DiagCert (L : ℕ) (d : ℕ → ℚ) : Prop :=
  (∀ i ∈ Icc 1 L, 0 ≤ d i) ∧
    ∀ x : ℕ → ℝ, -(∑ i ∈ Icc 1 L, (d i : ℝ) * x i ^ 2) ≤ qform L x

/-- The constant `c = 1/(4L) + 1/4 + (Σ d)/(4L²)` of PRS08, and the resulting bound `½ (3/8 - c)`. -/
noncomputable def prsBound (L : ℕ) (d : ℕ → ℚ) : ℝ :=
  (1 / 2 : ℝ) * (3 / 8 - (1 / (4 * (L : ℝ)) + 1 / 4 + (∑ i ∈ Icc 1 L, (d i : ℝ)) / (4 * (L : ℝ) ^ 2)))

/-- Sanity: the bound only depends on `Σ d`; PRS08's own `L = 128` certificate has `Σ d = 1364`, which gives
exactly `1675/32768`. -/
theorem prsBound_of_sum (L : ℕ) (d : ℕ → ℚ) (s : ℚ) (hs : ∑ i ∈ Icc 1 L, d i = s) :
    prsBound L d = (1 / 2 : ℝ) * (3 / 8 - (1 / (4 * (L : ℝ)) + 1 / 4 + (s : ℝ) / (4 * (L : ℝ) ^ 2))) := by
  unfold prsBound
  rw [← hs]
  push_cast
  ring

example : (1 / 2 : ℝ) * (3 / 8 - (1 / (4 * (128 : ℝ)) + 1 / 4 + ((1364 : ℚ) : ℝ) / (4 * (128 : ℝ) ^ 2)))
    = 1675 / 32768 := by
  norm_num

/-- Sanity: `A i i = 2` inside the range. -/
example : Aprs 128 1 1 = 2 ∧ Aprs 128 64 64 = 2 ∧ Aprs 128 128 128 = 2 := by decide

end Erdos1186Night2
