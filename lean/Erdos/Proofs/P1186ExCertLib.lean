import Mathlib
import Erdos.Proofs.P1186Ex
import Erdos.Proofs.P1186M2CertLib

/-!
# Erdos 1186 - soundness library for the five `RegionLB` certificates (lane excert, night 3)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is
its author's.  This file is hand-written and contains NO certificate numbers (they live in the generated modules
`P1186ExCert<r>*.lean`, produced by `problems/1186/exact/lean_cert_ex.py` from the data of lane excertsdp).

Part A: packed integer tables (`dec`), the quadratic-polynomial calculus `evq`, the Gram expansion of the matrix
`vᵀ N v`, the exact pair counts `A4v` (corner tests = `Grid.A4`), and the pair bound
`Dz * pterm ≥ s K y_i y_j - c` for every `θ ∈ [0, 2^40]`.
-/

namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

/-! ### Packed integer tables -/

/-- Signed digit `j` of the packed natural number `r` in base `2^W` (digit minus `2^(W-1)`). -/
def dec (W r j : ℕ) : ℤ := (((r / 2 ^ (W * j)) % 2 ^ W : ℕ) : ℤ) - ((2 ^ (W - 1) : ℕ) : ℤ)

/-- Entry `(i, j)` of a table given as a list of packed rows. -/
def tb (W : ℕ) (rows : List ℕ) (i j : ℕ) : ℤ := dec W (rows.getD i 0) j

/-- Entry `i` of a packed vector. -/
def vc (W : ℕ) (v : ℕ) (i : ℕ) : ℤ := dec W v i

/-! ### Elementary sum lemmas -/

theorem sum_Icc_one {β : Type*} [AddCommMonoid β] (L : ℕ) (f : ℕ → β) :
    ∑ a ∈ Icc 1 L, f a = ∑ t ∈ range L, f (1 + t) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]

/-! ### Quadratic polynomials in `n` variables with integer coefficients -/

/-- `c0 + Σ l_i y_i + Σ_{ij} q_ij y_i y_j`. -/
noncomputable def evq (n : ℕ) (c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) : ℝ :=
  (c0 : ℝ) + ∑ i ∈ range n, (l i : ℝ) * y i + ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)

theorem evq_add (n : ℕ) (c0 c0' : ℤ) (l l' : ℕ → ℤ) (q q' : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    evq n (c0 + c0') (fun i => l i + l' i) (fun i j => q i j + q' i j) y
      = evq n c0 l q y + evq n c0' l' q' y := by
  unfold evq
  push_cast
  simp only [add_mul, Finset.sum_add_distrib]
  ring

theorem evq_neg (n : ℕ) (c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    evq n (-c0) (fun i => -l i) (fun i j => -q i j) y = -evq n c0 l q y := by
  unfold evq
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem evq_smul (n : ℕ) (u c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    (u : ℝ) * evq n c0 l q y = evq n (u * c0) (fun i => u * l i) (fun i j => u * q i j) y := by
  unfold evq
  have h1 : (u : ℝ) * ∑ i ∈ range n, (l i : ℝ) * y i = ∑ i ∈ range n, ((u * l i : ℤ) : ℝ) * y i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  have h2 : (u : ℝ) * ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, ((u * q i j : ℤ) : ℝ) * (y i * y j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [mul_add, mul_add, h1, h2]
  push_cast
  ring

/-- The quadratic part only sees `q i j + q j i`. -/
theorem sum_sym (n : ℕ) (q q' : ℕ → ℕ → ℤ) (y : ℕ → ℝ)
    (hq : ∀ i < n, ∀ j < n, q i j + q j i = q' i j + q' j i) :
    ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, (q' i j : ℝ) * (y i * y j) := by
  have e1 : ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, (q j i : ℝ) * (y i * y j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have e2 : ∑ i ∈ range n, ∑ j ∈ range n, (q' i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, (q' j i : ℝ) * (y i * y j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have e3 : ∑ i ∈ range n, ∑ j ∈ range n, ((q i j : ℝ) + (q j i : ℝ)) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, ((q' i j : ℝ) + (q' j i : ℝ)) * (y i * y j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have := hq i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
    have : ((q i j : ℝ) + (q j i : ℝ)) = ((q' i j : ℝ) + (q' j i : ℝ)) := by exact_mod_cast this
    rw [this]
  simp only [add_mul, Finset.sum_add_distrib] at e3
  linarith

theorem evq_congr (n : ℕ) (c0 c0' : ℤ) (l l' : ℕ → ℤ) (q q' : ℕ → ℕ → ℤ) (y : ℕ → ℝ)
    (h0 : c0 = c0') (hl : ∀ i < n, l i = l' i) (hq : ∀ i < n, ∀ j < n, q i j + q j i = q' i j + q' j i) :
    evq n c0 l q y = evq n c0' l' q' y := by
  unfold evq
  rw [h0, sum_sym n q q' y hq]
  have : ∑ i ∈ range n, (l i : ℝ) * y i = ∑ i ∈ range n, (l' i : ℝ) * y i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hl i (Finset.mem_range.mp hi)]
  rw [this]

/-- sum over `Icc 1 (n+1)` = first term + the rest shifted by two. -/
theorem sum_Icc_split {β : Type*} [AddCommMonoid β] (n : ℕ) (F : ℕ → β) :
    ∑ a ∈ Icc 1 (n + 1), F a = F 1 + ∑ i ∈ range n, F (i + 2) := by
  rw [sum_Icc_one, Finset.sum_range_succ', add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show 1 + (i + 1) = i + 2 by omega]

/-- Gram expansion: indices `1` (the constant) and `i + 2` (the variable `y i`). -/
theorem gram_ev (n : ℕ) (M : ℕ → ℕ → ℤ) (x y : ℕ → ℝ) (h1 : x 1 = 1) (h2 : ∀ i, x (i + 2) = y i) :
    ∑ a ∈ Icc 1 (n + 1), ∑ b ∈ Icc 1 (n + 1), (M a b : ℝ) * x a * x b =
      evq n (M 1 1) (fun i => M 1 (i + 2) + M (i + 2) 1) (fun i j => M (i + 2) (j + 2)) y := by
  have hs : ∀ a : ℕ, ∑ b ∈ Icc 1 (n + 1), (M a b : ℝ) * x a * x b
      = (M a 1 : ℝ) * x a * x 1 + ∑ j ∈ range n, (M a (j + 2) : ℝ) * x a * x (j + 2) :=
    fun a => sum_Icc_split n (fun b => (M a b : ℝ) * x a * x b)
  simp only [hs]
  rw [sum_Icc_split n (fun a => (M a 1 : ℝ) * x a * x 1 + ∑ j ∈ range n, (M a (j + 2) : ℝ) * x a * x (j + 2))]
  simp only [h1, h2]
  unfold evq
  push_cast
  simp only [Finset.sum_add_distrib, add_mul, mul_one, mul_assoc]
  ring

/-! ### The exact pair counts -/

/-- `A4 i j` by corner tests (full / empty blocks) and the real count only for the remaining pairs. -/
def A4v (G : Grid) (i j : ℕ) : ℕ :=
  if 1 ≤ 2 * ((G.lo j : ℤ) + 1) - G.hi i - 1 ∧ 2 * (G.hi j : ℤ) - ((G.lo i : ℤ) + 1) - 1 ≤ 1094 then
    4 * G.len i * G.len j
  else if 2 * (G.hi j : ℤ) - ((G.lo i : ℤ) + 1) - 1 ≤ -2 ∨ 1097 ≤ 2 * ((G.lo j : ℤ) + 1) - G.hi i - 1 then 0
  else G.A4 i j

theorem A4v_eq (G : Grid) (i j : ℕ) : A4v G i j = G.A4 i j := by
  unfold A4v
  split_ifs with h1 h2
  · unfold Grid.A4
    have hk : ∀ p ∈ Ioc (G.lo i) (G.hi i), ∀ q ∈ Ioc (G.lo j) (G.hi j), K4 1096 p q = 4 := by
      intro p hp q hq
      rw [Finset.mem_Ioc] at hp hq
      unfold K4
      rw [if_pos]
      push_cast
      omega
    rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (hk p hp))]
    simp only [Finset.sum_const, Nat.card_Ioc, smul_eq_mul]
    unfold Grid.len
    ring
  · unfold Grid.A4
    have hk : ∀ p ∈ Ioc (G.lo i) (G.hi i), ∀ q ∈ Ioc (G.lo j) (G.hi j), K4 1096 p q = 0 := by
      intro p hp q hq
      rw [Finset.mem_Ioc] at hp hq
      unfold K4
      rw [if_neg, if_neg, if_neg]
      · push_cast
        omega
      · push_cast
        omega
      · push_cast
        omega
    rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (hk p hp))]
    simp
  · rfl

/-! ### The pair bound -/

/-- the denominator of the multipliers `θ`. -/
def Qn : ℤ := 1099511627776

/-- `D = Qn * 360364800`, the common denominator of the data. -/
def Dz : ℤ := Qn * 360364800

/-- `s_ij = +1` if the signs agree, `-1` otherwise. -/
def sgnP (G : Grid) (i j : ℕ) : ℤ := if G.sgn i * G.sgn j = 1 then 1 else -1

/-- integer coefficient of `y_i y_j`:  `300 (Q - θ) len_i len_j`. -/
def Kp (G : Grid) (θ : ℤ) (i j : ℕ) : ℤ := 300 * (Qn - θ) * (G.len i : ℤ) * (G.len j : ℤ)

/-- integer constant of the pair bound. -/
def cp (G : Grid) (θ : ℤ) (i j : ℕ) : ℤ :=
  if G.sgn i * G.sgn j = 1 then 75 * (Qn - θ) * (4 * (G.len i : ℤ) * (G.len j : ℤ) - (A4v G i j : ℤ))
  else 75 * θ * (A4v G i j : ℤ)

theorem pterm_scaled (G : Grid) (i j : ℕ) (θ : ℤ) (h0 : 0 ≤ θ) (h1 : θ ≤ Qn) (yi yj : ℝ) :
    ((sgnP G i j * Kp G θ i j : ℤ) : ℝ) * (yi * yj) - (cp G θ i j : ℝ)
      ≤ (Dz : ℝ) * G.pterm i j yi yj := by
  have hA := A4v_eq G i j
  unfold Grid.pterm sgnP Kp cp Grid.wt
  rw [hA]
  simp only [Qn, Dz] at *
  have hθ0 : (0 : ℝ) ≤ (θ : ℝ) := by exact_mod_cast h0
  have hθ1 : (θ : ℝ) ≤ 1099511627776 := by exact_mod_cast h1
  push_cast
  set a : ℝ := (G.len i : ℝ) with ha
  set b : ℝ := (G.len j : ℝ) with hb
  set A : ℝ := (G.A4 i j : ℝ) with hAd
  by_cases hs : G.sgn i * G.sgn j = 1
  · simp only [hs, if_true]
    set u : ℝ := a / 1096 * (b / 1096) * yi * yj - (a / 1096 * (b / 1096) - A / (4 * 1096 ^ 2)) with hu
    have hm1 : u ≤ max 0 u := le_max_right _ _
    have hm2 : 0 ≤ max 0 u := le_max_left _ _
    have key : (1099511627776 * 360364800 : ℝ) * ((1 - (θ : ℝ) / 1099511627776) * u)
        = 1 * (300 * (1099511627776 - (θ : ℝ)) * a * b) * (yi * yj)
          - 75 * (1099511627776 - (θ : ℝ)) * (4 * a * b - A) := by
      rw [hu]
      field_simp
      ring
    have hq : 0 ≤ 1 - (θ : ℝ) / 1099511627776 := by
      rw [sub_nonneg, div_le_one (by norm_num)]; exact hθ1
    have ht : 0 ≤ (θ : ℝ) / 1099511627776 := by positivity
    have hle : (1 - (θ : ℝ) / 1099511627776) * u ≤ max 0 u := by
      nlinarith [mul_nonneg hq (sub_nonneg.mpr hm1), mul_nonneg ht hm2]
    have hD : (0 : ℝ) ≤ 1099511627776 * 360364800 := by norm_num
    have hh := mul_le_mul_of_nonneg_left hle hD
    rw [← key]
    linarith
  · simp only [hs, if_false]
    set P : ℝ := a / 1096 * (b / 1096) * yi * yj with hP
    set Ain : ℝ := A / (4 * 1096 ^ 2) with hAin
    have hm1 : -Ain ≤ max (-Ain) (-P) := le_max_left _ _
    have hm2 : -P ≤ max (-Ain) (-P) := le_max_right _ _
    have key : (1099511627776 * 360364800 : ℝ) * ((θ : ℝ) / 1099511627776 * (-Ain)
          + (1 - (θ : ℝ) / 1099511627776) * (-P))
        = (-1 * (300 * (1099511627776 - (θ : ℝ)) * a * b)) * (yi * yj) - 75 * (θ : ℝ) * A := by
      rw [hP, hAin]
      field_simp
      ring
    have hq : 0 ≤ 1 - (θ : ℝ) / 1099511627776 := by
      rw [sub_nonneg, div_le_one (by norm_num)]; exact hθ1
    have ht : 0 ≤ (θ : ℝ) / 1099511627776 := by positivity
    have hle : (θ : ℝ) / 1099511627776 * (-Ain) + (1 - (θ : ℝ) / 1099511627776) * (-P)
        ≤ max (-Ain) (-P) := by
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hm1), mul_nonneg hq (sub_nonneg.mpr hm2)]
    have hD : (0 : ℝ) ≤ 1099511627776 * 360364800 := by norm_num
    have hh := mul_le_mul_of_nonneg_left hle hD
    rw [← key]
    linarith

end Erdos1186Ex
