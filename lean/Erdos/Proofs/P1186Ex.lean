import Mathlib
import Erdos.Proofs.P1186
import Erdos.Proofs.P1186Low
import Erdos.Proofs.P1186M2
import Erdos.Proofs.P1186ExData

/-!
# Erdos 1186 - shared interface for formalising the claimed proof of `δ 3 = 117/2192` (definitions only)

The proof formalised here is the unrefereed proof claim on erdosproblems.com/1186 ("Proof claims", dated 2026-10-05);
the mathematics is its author's. Its finite part was reproduced in exact arithmetic by the reviewers rev1186c and
ver1186c (2026-10-26); the coordinator's reports describe it. This file fixes a DISCRETE version of the argument, at
`n = 1096 w`, so that no measure theory is needed:

* `Wm s n` (lean1186a's window correlation, `P1186LowA.lean`) equals `Σ_{x,y ∈ [1,n]} rdI n x y s_x s_y`, the ordered
  (end, middle) pairs of 3-APs; lean1186c's `V_lower` gives `32 V ≥ 2n² - 16n + 8 Wm`, so `Wm ≥ -(5/137) n² - O(n)` for
  every colouring gives `δ 3 ≥ 117/2192`.
* `s = s* (1 - 2σ)` with `s*` the PRS colouring `sstar w` and `σ` the 0/1 indicator of disagreement:
  `Wm s = Wm s* + 2 Σ_x H2 w x σ_x + 4 Qd (s* σ)` (the claim's expansion `E(σ) = ∫ h σ + Q(φ* σ)`, `H2 ≈ 2 n h`).
* `StarOK`: `Wm s* ≥ -(5/137) n² - O(n)`.
* `BathOK G`: on every cell of the grid `G`, `Σ H2 σ ≥ 2 n² (a_i y_i + b_i y_i²) - O(n)` (the claim's Lemma 2, bathtub).
* `PairOK G`: `Qd (s* σ) ≥ n² Σ_{i,j} pterm - O(n)` (the claim's Lemma 3, cell pairs).
* `RegionLB G lo hi`: `Lval G y ≥ 0` for `y ∈ [0,1]^N` with `lo ≤ m ≤ hi` (the claim's five finite certificates; the
  regions `[0,1/5]`, `[1/5,3/10]`, `[3/10,2/5]` on `G24` and `[2/5,9/20]`, `[9/20,1/2]` on `G8`; `σ ↦ 1 - σ` gives `m ≤ 1/2`).

Do not change these definitions; add lemmas in your own module.
-/

namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

/-- The scale: `n = 1096 w`. -/
def nn (w : ℕ) : ℕ := 1096 * w

/-- `φ*` at scale `n = 1096 w`: the PRS 12-block colouring `ck (2w)` of `[1, n]`, as `±1`. -/
def sstar (w x : ℕ) : ℤ := sg (ck (2 * w)) x

/-- `1` if `1 ≤ 2y - x ≤ n` (`x` an end and `y` the middle of a 3-AP inside `[1, n]`, for `x, y ∈ [1, n]`), else `0`. -/
def rdI (n x y : ℕ) : ℤ := if 1 ≤ 2 * (y : ℤ) - x ∧ 2 * (y : ℤ) - x ≤ n then 1 else 0

/-- `Q_d(u) = Σ_{(x,y) ∈ R_d} u_x u_y` over `[1, n]²`. -/
def Qd (n : ℕ) (u : ℕ → ℤ) : ℤ := ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n, rdI n x y * u x * u y

/-- `2 H_x = -s*_x (Σ_{y : (x,y) ∈ R_d} s*_y + Σ_{e : (e,x) ∈ R_d} s*_e)` (the claim's `h`, scaled: `H2 w x ≈ 2 n h(x/n)`). -/
def H2 (w x : ℕ) : ℤ :=
  -sstar w x * (∑ y ∈ Icc 1 (nn w), rdI (nn w) x y * sstar w y + ∑ e ∈ Icc 1 (nn w), rdI (nn w) e x * sstar w e)

/-- `σ` is a 0/1 indicator. -/
def IsInd (σ : ℕ → ℤ) : Prop := ∀ x, σ x = 0 ∨ σ x = 1

namespace Grid

/-- number of cells -/
def N (G : Grid) : ℕ := G.pts.length - 1
/-- left / right endpoint of cell `i` (0-based), in units of `1/1096` -/
def lo (G : Grid) (i : ℕ) : ℕ := G.pts.getD i 0
def hi (G : Grid) (i : ℕ) : ℕ := G.pts.getD (i + 1) 0
/-- length of cell `i` in units of `1/1096` -/
def len (G : Grid) (i : ℕ) : ℕ := G.hi i - G.lo i
/-- `w_i`, the length of cell `i` as a fraction of `[0, 1]` -/
def wt (G : Grid) (i : ℕ) : ℚ := (G.len i : ℚ) / 1096
def ai (G : Grid) (i : ℕ) : ℚ := G.a.getD i 0
def bi (G : Grid) (i : ℕ) : ℚ := G.b.getD i 0
/-- the sign of `φ*` on cell `i` (`c1` index of its first unit cell) -/
def sgn (G : Grid) (i : ℕ) : ℤ := sg c1 (G.lo i / 2 + 1)
/-- `4 · 1096² · area(R ∩ I_i × I_j)` from the exact unit-cell kernel `K4 1096` (`P1186M2.lean`, MODEL2 Lemma 1). -/
def A4 (G : Grid) (i j : ℕ) : ℕ := ∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j), K4 1096 p q
/-- the points of cell `i` at scale `w`: `(lo_i w, hi_i w]` -/
def cell (G : Grid) (w i : ℕ) : Finset ℕ := Ioc (G.lo i * w) (G.hi i * w)

/-- `y_i(σ)`: the density of `σ` on cell `i` at scale `w`. -/
noncomputable def yv (G : Grid) (w : ℕ) (σ : ℕ → ℤ) (i : ℕ) : ℝ :=
  ((∑ x ∈ G.cell w i, σ x : ℤ) : ℝ) / ((G.len i * w : ℕ) : ℝ)

/-- The claim's Lemma 3 bound for the ordered cell pair `(i, j)`, with `P = w_i w_j y_i y_j`:
`max(0, P - A_out)` if the signs agree and `max(-A_in, -P)` if not (full and empty pairs are the cases
`A_out = 0` and `A_in = 0`). -/
noncomputable def pterm (G : Grid) (i j : ℕ) (yi yj : ℝ) : ℝ :=
  let P : ℝ := (G.wt i : ℝ) * G.wt j * yi * yj
  let Ain : ℝ := (G.A4 i j : ℝ) / (4 * 1096 ^ 2)
  let Aout : ℝ := (G.wt i : ℝ) * G.wt j - Ain
  if G.sgn i * G.sgn j = 1 then max 0 (P - Aout) else max (-Ain) (-P)

/-- The claim's finite lower bound `L(y)` (Lemmas 2-3). -/
noncomputable def Lval (G : Grid) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range G.N, ((G.ai i : ℝ) * y i + (G.bi i : ℝ) * y i ^ 2)
    + ∑ i ∈ range G.N, ∑ j ∈ range G.N, G.pterm i j (y i) (y j)

/-- `m = Σ w_i y_i` -/
noncomputable def mval (G : Grid) (y : ℕ → ℝ) : ℝ := ∑ i ∈ range G.N, (G.wt i : ℝ) * y i

/-- Well-formedness (decidable): endpoints `0 = p_0 < ... < p_N = 1096`, one `a` and one `b` per cell, and `φ*`
constant on every cell. -/
def WF (G : Grid) : Prop :=
  G.pts.head? = some 0 ∧ G.pts.getLast? = some 1096 ∧ G.pts.Pairwise (· < ·) ∧
    G.a.length = G.N ∧ G.b.length = G.N ∧
    ∀ i < G.N, ∀ k ∈ Ico (G.lo i) (G.hi i), c1 (k / 2 + 1) = c1 (G.lo i / 2 + 1)

instance (G : Grid) : Decidable G.WF := by unfold WF; infer_instance

end Grid

/-- The PRS colouring's window correlation: `Wm s* ≥ -(5/137) n² - O(n)`. -/
def StarOK : Prop :=
  ∃ C : ℝ, ∀ w : ℕ, 1 ≤ w → -(5 / 137 : ℝ) * (nn w : ℝ) ^ 2 - C * w ≤ (Wm (sstar w) (nn w) : ℝ)

/-- Lemma 2 (bathtub), discrete, on every cell of `G`. -/
def BathOK (G : Grid) : Prop :=
  ∃ C : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ σ : ℕ → ℤ, IsInd σ → ∀ i < G.N,
    2 * (nn w : ℝ) ^ 2 * ((G.ai i : ℝ) * G.yv w σ i + (G.bi i : ℝ) * G.yv w σ i ^ 2) - C * w
      ≤ ((∑ x ∈ G.cell w i, H2 w x * σ x : ℤ) : ℝ)

/-- Lemma 3 (cell pairs), discrete, summed over all ordered pairs of cells of `G`. -/
def PairOK (G : Grid) : Prop :=
  ∃ C : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ σ : ℕ → ℤ, IsInd σ →
    (nn w : ℝ) ^ 2 * ∑ i ∈ range G.N, ∑ j ∈ range G.N, G.pterm i j (G.yv w σ i) (G.yv w σ j) - C * w
      ≤ (Qd (nn w) (fun x => sstar w x * σ x) : ℝ)

/-- The finite certificates: `L(y) ≥ 0` on `{y ∈ [0,1]^N : lo ≤ m ≤ hi}`. -/
def RegionLB (G : Grid) (lo hi : ℚ) : Prop :=
  ∀ y : ℕ → ℝ, (∀ i < G.N, 0 ≤ y i ∧ y i ≤ 1) → (lo : ℝ) ≤ G.mval y → G.mval y ≤ hi → 0 ≤ G.Lval y

/-! Sanity checks of the data (cheap). -/
example : G24.N = 130 ∧ G8.N = 146 := by decide +kernel
example : G24.lo 0 = 0 ∧ G24.hi 129 = 1096 ∧ G8.hi 145 = 1096 := by decide +kernel
example : sstar 1 1 = 1 ∧ sstar 1 56 = 1 ∧ sstar 1 57 = -1 ∧ sstar 1 1096 = -1 := by decide +kernel
example : G24.WF ∧ G8.WF := by decide +kernel
example : G8.A4 0 0 = 192 ∧ G8.sgn 0 = 1 := by decide +kernel

end Erdos1186Ex
