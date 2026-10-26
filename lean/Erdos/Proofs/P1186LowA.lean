import Mathlib
import Erdos.Proofs.P1186Prs

/-!
# Erdos 1186 - the PRS08 lower-bound reduction, part A (combinatorics, no colourings)

Generic lemmas on integer sequences `s : ℕ → ℤ` (later `s = ±1` from a 2-colouring), used by
`P1186Low.lean` to prove `Erdos1186Night2.lower_of_cert`.  Everything is in `ℤ`; reals appear only in
`qform_eq` / `cert_apply` (the interface with `DiagCert`).

Notation: `pre s t = Σ_{x ∈ (0, t]} s x`; for `n` and `y ∈ [1, n]`, `Dm n y = min (y-1) (n-y)` is the largest
`d` with `y - d, y + d ∈ [1, n]` (3-APs are indexed by midpoint `y` and step `d ∈ [1, Dm n y]`).

* `mid_sum`/`parity_sq`/`Rm_nonneg`/`Rm_one`: `Σ s² + 2 R(s) = E² + O²` where `R s n = Σ_y Σ_d s_{y-d} s_{y+d}`
  and `E, O` are the sums of `s` over even / odd `x ∈ [1, n]`.  Hence `R ≥ -n/2` for `s = ±1`, and with `s ≡ 1`
  (`R = #3-APs`): `n² ≤ 2 n + 4 #3-APs`.
* `mid_expand`: `Σ_{(y,d)} (1 + s_{y-d}s_y + s_y s_{y+d} + s_{y-d}s_{y+d}) = #3-APs + (W - Σ s²) + R`, with the window
  correlation `W s n = Σ_y s_y (pre s (y + D_y) - pre s (y - D_y - 1))`.
* `Wm_lower`: for `n = 2 h m`, `W ≥ Σ_i X_i C_i - 2 h Σ_β |2β-1-m|`, where `X_i` is the sum of `s` over the `i`-th
  block `((i-1) m, i m]` and `C_i = Σ_j B_ij X_j` the PRS strip/cell sum (`Bprs`).  Proof: in strip `i` the window
  `[y - D_y, y + D_y]` differs from the cell union by `|2β - 1 - m|` points (`T_err`, via the 1-Lipschitz `pre`).
* `gsum_le`: `2 Σ_β |2β-1-m| ≤ m²`.
* `cert_apply`: `-(m² Σ d) ≤ 2 Σ_i X_i C_i` from a `DiagCert` (`|X_i| ≤ m`).
-/

open Finset

namespace Erdos1186Night2

/-- prefix sum -/
def pre (s : ℕ → ℤ) (t : ℕ) : ℤ := ∑ x ∈ Ioc 0 t, s x

lemma pre_zero (s : ℕ → ℤ) : pre s 0 = 0 := by simp [pre]

lemma pre_succ (s : ℕ → ℤ) (t : ℕ) : pre s (t+1) = pre s t + s (t+1) := by
  unfold pre
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le t)]

lemma sum_Ioc_eq (s : ℕ → ℤ) {a b : ℕ} (h : a ≤ b) : ∑ x ∈ Ioc a b, s x = pre s b - pre s a := by
  unfold pre
  rw [← Finset.sum_Ioc_consecutive s (Nat.zero_le a) h]; ring

lemma pre_lip (s : ℕ → ℤ) (hs : ∀ x, |s x| ≤ 1) {a b : ℕ} (h : a ≤ b) :
    |pre s b - pre s a| ≤ ((b - a : ℕ) : ℤ) := by
  rw [← sum_Ioc_eq s h]
  calc |∑ x ∈ Ioc a b, s x| ≤ ∑ x ∈ Ioc a b, |s x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ Ioc a b, (1:ℤ) := Finset.sum_le_sum (fun x _ => hs x)
    _ = ((b - a : ℕ) : ℤ) := by simp

lemma pre_lip' (s : ℕ → ℤ) (hs : ∀ x, |s x| ≤ 1) (a b : ℕ) :
    |pre s a - pre s b| ≤ |(a : ℤ) - b| := by
  rcases le_total a b with h | h
  · rw [abs_sub_comm, abs_sub_comm (a:ℤ)]
    have := pre_lip s hs h
    have e : ((b - a : ℕ) : ℤ) = (b:ℤ) - a := by omega
    rw [e] at this
    rw [abs_of_nonneg (by omega : (0:ℤ) ≤ (b:ℤ) - a)]
    exact this
  · have := pre_lip s hs h
    have e : ((a - b : ℕ) : ℤ) = (a:ℤ) - b := by omega
    rw [e] at this
    rw [abs_of_nonneg (by omega : (0:ℤ) ≤ (a:ℤ) - b)]
    exact this

lemma sum_Icc_sym (g : ℕ → ℤ) (y : ℕ) : ∀ D, D ≤ y →
    ∑ x ∈ Icc (y - D) (y + D), g x = g y + ∑ d ∈ Icc 1 D, (g (y - d) + g (y + d)) := by
  intro D
  induction D with
  | zero => intro _; simp
  | succ D ih =>
    intro hD
    have h := ih (by omega)
    have e : Icc (y - (D+1)) (y + (D+1)) =
        insert (y - (D+1)) (insert (y + (D+1)) (Icc (y - D) (y + D))) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [e, Finset.sum_insert, Finset.sum_insert, h, Finset.sum_Icc_succ_top (by omega)]
    · ring
    · simp only [mem_Icc]; omega
    · simp only [mem_insert, mem_Icc]; omega

/-- the sum `∑ |2β-1-m|` -/
def gsum (m : ℕ) : ℤ := ∑ k ∈ range m, |2 * (k : ℤ) + 1 - m|

lemma gsum_add_two (m : ℕ) : gsum (m + 2) = gsum m + 2 * m + 2 := by
  unfold gsum
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have h1 : ∑ k ∈ range m, |2 * ((k + 1 : ℕ) : ℤ) + 1 - ((m + 2 : ℕ) : ℤ)| =
      ∑ k ∈ range m, |2 * (k : ℤ) + 1 - m| := by
    apply Finset.sum_congr rfl; intro k _; push_cast; congr 1; ring
  have h2 : |2 * ((m + 1 : ℕ) : ℤ) + 1 - ((m + 2 : ℕ) : ℤ)| = m + 1 := by
    push_cast
    rw [abs_of_nonneg (by omega)]; ring
  have h3 : |2 * ((0 : ℕ) : ℤ) + 1 - ((m + 2 : ℕ) : ℤ)| = m + 1 := by
    push_cast
    rw [abs_of_nonpos (by omega)]; ring
  rw [h1, h2, h3]; ring

lemma gsum_le : ∀ m : ℕ, 2 * gsum m ≤ (m : ℤ) ^ 2
  | 0 => by simp [gsum]
  | 1 => by simp [gsum]
  | m + 2 => by
    have := gsum_le m
    rw [gsum_add_two]; push_cast; nlinarith


/-- `Dm n y = min (y-1) (n-y)`: half-length of the longest 3-AP centred at `y` in `[1,n]`. -/
def Dm (n y : ℕ) : ℕ := min (y - 1) (n - y)

/-- the sum over 3-APs of the endpoint products, in midpoint form -/
def Rm (s : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ y ∈ Icc 1 n, ∑ d ∈ Icc 1 (Dm n y), s (y - d) * s (y + d)

lemma parity_sq (s : ℕ → ℤ) (n : ℕ) :
    ∑ x ∈ Icc 1 n, ∑ z ∈ Icc 1 n, (if x % 2 = z % 2 then s x * s z else 0)
      = (∑ x ∈ Icc 1 n, if x % 2 = 0 then s x else 0) ^ 2
        + (∑ x ∈ Icc 1 n, if x % 2 = 1 then s x else 0) ^ 2 := by
  have h : ∀ x z : ℕ, (if x % 2 = z % 2 then s x * s z else 0) =
      (if x % 2 = 0 then s x else 0) * (if z % 2 = 0 then s z else 0) +
      (if x % 2 = 1 then s x else 0) * (if z % 2 = 1 then s z else 0) := by
    intro x z
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one z with hz | hz <;> simp [hx, hz]
  simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul_sum, sq]

lemma mid_sum (s : ℕ → ℤ) (n : ℕ) :
    ∑ x ∈ Icc 1 n, ∑ z ∈ Icc 1 n, (if x % 2 = z % 2 then s x * s z else 0)
      = ∑ y ∈ Icc 1 n, s y * s y + 2 * Rm s n := by
  have h1 : ∑ x ∈ Icc 1 n, ∑ z ∈ Icc 1 n, (if x % 2 = z % 2 then s x * s z else 0)
      = ∑ p ∈ (Icc 1 n ×ˢ Icc 1 n), (if p.1 % 2 = p.2 % 2 then s p.1 * s p.2 else 0) := by
    rw [Finset.sum_product]
  have h2 : ∑ p ∈ (Icc 1 n ×ˢ Icc 1 n), (if p.1 % 2 = p.2 % 2 then s p.1 * s p.2 else 0)
      = ∑ q ∈ (Icc 1 n).sigma (fun y => Icc (y - Dm n y) (y + Dm n y)),
          s q.2 * s (2 * q.1 - q.2) := by
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_nbij' (fun q => (q.2, 2 * q.1 - q.2))
      (fun p => (⟨(p.1 + p.2) / 2, p.1⟩ : Σ _ : ℕ, ℕ))
    · intro q hq
      simp only [Finset.mem_sigma, Finset.mem_Icc, Dm, Finset.mem_filter, Finset.mem_product] at hq ⊢
      omega
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_Icc, Dm, Finset.mem_filter, Finset.mem_product] at hp ⊢
      omega
    · rintro ⟨y, x⟩ hq
      simp only [Finset.mem_sigma, Finset.mem_Icc, Dm] at hq
      have e : (x + (2 * y - x)) / 2 = y := by omega
      simp [e]
    · rintro ⟨x, z⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      have e : 2 * ((x + z) / 2) - x = z := by omega
      simp [e]
    · intro q hq
      simp only [Finset.mem_sigma, Finset.mem_Icc, Dm] at hq
      have : q.2 % 2 = (2 * q.1 - q.2) % 2 := by omega
      simp
  rw [h1, h2, Finset.sum_sigma]
  have h3 : ∀ y ∈ Icc 1 n, ∑ x ∈ Icc (y - Dm n y) (y + Dm n y), s x * s (2 * y - x)
      = s y * s y + 2 * ∑ d ∈ Icc 1 (Dm n y), s (y - d) * s (y + d) := by
    intro y hy
    have hD : Dm n y ≤ y := by unfold Dm; omega
    rw [sum_Icc_sym (fun x => s x * s (2 * y - x)) y (Dm n y) hD]
    have e1 : 2 * y - y = y := by omega
    rw [e1]
    have h4 : ∀ d ∈ Icc 1 (Dm n y), (s (y - d) * s (2 * y - (y - d)) + s (y + d) * s (2 * y - (y + d)))
        = 2 * (s (y - d) * s (y + d)) := by
      intro d hd
      simp only [Finset.mem_Icc, Dm] at hd
      have e1 : 2 * y - (y - d) = y + d := by omega
      have e2 : 2 * y - (y + d) = y - d := by omega
      rw [e1, e2]; ring
    rw [Finset.sum_congr rfl h4, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl h3, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl


lemma sum_split_parity (s : ℕ → ℤ) (n : ℕ) :
    (∑ x ∈ Icc 1 n, if x % 2 = 0 then s x else 0) + (∑ x ∈ Icc 1 n, if x % 2 = 1 then s x else 0)
      = ∑ x ∈ Icc 1 n, s x := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

/-- For every integer sequence, `Σ s² + 2 R ≥ 0` (a sum of two squares). -/
lemma Rm_nonneg (s : ℕ → ℤ) (n : ℕ) : 0 ≤ ∑ y ∈ Icc 1 n, s y * s y + 2 * Rm s n := by
  rw [← mid_sum, parity_sq]; positivity

/-- Number of 3-APs of `[1,n]`: `n² ≤ 2 n + 4 A` (here `A = R` of the constant sequence `1`). -/
lemma Rm_one (n : ℕ) : (n : ℤ) ^ 2 ≤ 2 * n + 4 * Rm (fun _ => 1) n := by
  have h := mid_sum (fun _ => (1:ℤ)) n
  rw [parity_sq] at h
  have h2 := sum_split_parity (fun _ => (1:ℤ)) n
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, mul_one,
    nsmul_eq_mul] at h h2
  set E := ∑ x ∈ Icc 1 n, if x % 2 = 0 then (1:ℤ) else 0
  set O := ∑ x ∈ Icc 1 n, if x % 2 = 1 then (1:ℤ) else 0
  nlinarith [sq_nonneg (E - O)]

/-- `Wm s n = Σ_y s_y (S(y + D_y) - S(y - D_y - 1))`, the "window correlation". -/
def Wm (s : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ y ∈ Icc 1 n, s y * (pre s (y + Dm n y) - pre s (y - Dm n y - 1))

lemma inner_sum (s : ℕ → ℤ) (n y : ℕ) (hy : y ∈ Icc 1 n) :
    ∑ d ∈ Icc 1 (Dm n y), (s (y - d) + s (y + d))
      = pre s (y + Dm n y) - pre s (y - Dm n y - 1) - s y := by
  simp only [Finset.mem_Icc] at hy
  have h1 := sum_Icc_sym s y (Dm n y) (by unfold Dm; omega)
  have h2 : Icc (y - Dm n y) (y + Dm n y) = Ioc (y - Dm n y - 1) (y + Dm n y) := by
    ext x; simp only [mem_Icc, mem_Ioc]; unfold Dm; omega
  rw [h2, sum_Ioc_eq s (by omega)] at h1
  linarith

lemma mid_term (s : ℕ → ℤ) (n y : ℕ) (hy : y ∈ Icc 1 n) :
    ∑ d ∈ Icc 1 (Dm n y), (1 + s (y - d) * s y + s y * s (y + d) + s (y - d) * s (y + d))
      = ∑ _d ∈ Icc 1 (Dm n y), (1:ℤ)
        + (s y * (pre s (y + Dm n y) - pre s (y - Dm n y - 1)) - s y * s y)
        + ∑ d ∈ Icc 1 (Dm n y), s (y - d) * s (y + d) := by
  have h := inner_sum s n y hy
  have e : ∑ d ∈ Icc 1 (Dm n y), (1 + s (y - d) * s y + s y * s (y + d) + s (y - d) * s (y + d))
      = ∑ _d ∈ Icc 1 (Dm n y), (1:ℤ) + s y * ∑ d ∈ Icc 1 (Dm n y), (s (y - d) + s (y + d))
        + ∑ d ∈ Icc 1 (Dm n y), s (y - d) * s (y + d) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro d _; ring
  rw [e, h]; ring

lemma mid_expand (s : ℕ → ℤ) (n : ℕ) :
    ∑ y ∈ Icc 1 n, ∑ d ∈ Icc 1 (Dm n y),
        (1 + s (y - d) * s y + s y * s (y + d) + s (y - d) * s (y + d))
      = ∑ y ∈ Icc 1 n, ∑ _d ∈ Icc 1 (Dm n y), (1:ℤ)
        + (Wm s n - ∑ y ∈ Icc 1 n, s y * s y) + Rm s n := by
  rw [Finset.sum_congr rfl (fun y hy => mid_term s n y hy)]
  unfold Wm Rm
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]


/-! ## Blocks, strips and the cell matrix -/

/-- block sum of the `j`-th block `((j-1) m, j m]`. -/
def Xb (s : ℕ → ℤ) (m j : ℕ) : ℤ := pre s (j * m) - pre s ((j - 1) * m)

/-- the strip's cell sum `C_i = Σ_j B_ij X_j`. -/
def Cb (s : ℕ → ℤ) (L m i : ℕ) : ℤ := ∑ j ∈ Icc 1 L, (Bprs L i j : ℤ) * Xb s m j

lemma tele (G : ℕ → ℤ) {p q : ℕ} (h : p ≤ q) :
    ∑ j ∈ Ioc p q, (G j - G (j - 1)) = G q - G p := by
  induction q, h using Nat.le_induction with
  | base => simp
  | succ q hq ih =>
    rw [Finset.sum_Ioc_succ_top hq, ih]
    simp only [Nat.add_sub_cancel]
    ring

lemma Cb_eq (s : ℕ → ℤ) (L m i : ℕ) (hi1 : 1 ≤ i) (hiL : i ≤ L) :
    Cb s L m i = pre s ((if 2 * i ≤ L then 2 * i - 1 else L) * m)
      - pre s ((if 2 * i ≤ L then 0 else 2 * i - L - 1) * m) := by
  have h1 : ∀ j, ((Bprs L i j : ℕ) : ℤ) * Xb s m j
      = if (j + 1 ≤ 2 * i ∧ 2 * i ≤ j + L) then Xb s m j else 0 := by
    intro j; unfold Bprs; split_ifs <;> simp
  unfold Cb
  simp only [h1]
  rw [← Finset.sum_filter]
  have h2 : (Icc 1 L).filter (fun j => j + 1 ≤ 2 * i ∧ 2 * i ≤ j + L)
      = Ioc (if 2 * i ≤ L then 0 else 2 * i - L - 1) (if 2 * i ≤ L then 2 * i - 1 else L) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    split_ifs <;> omega
  rw [h2]
  have h3 : ∀ j ∈ Ioc (if 2 * i ≤ L then 0 else 2 * i - L - 1) (if 2 * i ≤ L then 2 * i - 1 else L),
      Xb s m j = pre s (j * m) - pre s ((j - 1) * m) := fun j _ => rfl
  rw [Finset.sum_congr rfl h3]
  have := tele (fun j => pre s (j * m)) (p := if 2 * i ≤ L then 0 else 2 * i - L - 1)
    (q := if 2 * i ≤ L then 2 * i - 1 else L) (by split_ifs <;> omega)
  simpa using this

lemma sum_range_shift (s : ℕ → ℤ) (a m : ℕ) :
    ∑ k ∈ range m, s (a + k + 1) = pre s (a + m) - pre s a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, show a + (m + 1) = a + m + 1 by ring, pre_succ]
    ring

lemma T_err (s : ℕ → ℤ) (hs : ∀ x, |s x| ≤ 1) (h m i' k : ℕ) (hi : i' < 2 * h) (hk : k < m) :
    |(pre s ((i' * m + k + 1) + Dm (2 * (h * m)) (i' * m + k + 1))
        - pre s ((i' * m + k + 1) - Dm (2 * (h * m)) (i' * m + k + 1) - 1))
      - Cb s (2 * h) m (i' + 1)| ≤ |2 * (k : ℤ) + 1 - m| := by
  have hC := Cb_eq s (2 * h) m (i' + 1) (by omega) (by omega)
  have hn : 2 * h * m = 2 * (h * m) := by ring
  have hA1 : (i' + 1) * m = i' * m + m := by ring
  by_cases hc : i' + 1 ≤ h
  · have hlow : i' * m + m ≤ h * m := by
      have := Nat.mul_le_mul_right m hc
      rw [hA1] at this; exact this
    have e2 : (2 * (i' + 1) - 1) * m = 2 * (i' * m) + m := by
      have : 2 * (i' + 1) - 1 = 2 * i' + 1 := by omega
      rw [this]; ring
    have hcond : 2 * (i' + 1) ≤ 2 * h := by omega
    simp only [if_pos hcond] at hC
    rw [hC, e2]
    have h1 : i' * m + k + 1 + Dm (2 * (h * m)) (i' * m + k + 1) = 2 * (i' * m + k + 1) - 1 := by
      unfold Dm; omega
    have h2 : i' * m + k + 1 - Dm (2 * (h * m)) (i' * m + k + 1) - 1 = 0 := by
      unfold Dm; omega
    rw [h1, h2, zero_mul, pre_zero]
    have e3 : pre s (2 * (i' * m + k + 1) - 1) - 0 - (pre s (2 * (i' * m) + m) - 0)
        = pre s (2 * (i' * m + k + 1) - 1) - pre s (2 * (i' * m) + m) := by ring
    rw [e3]
    refine (pre_lip' s hs _ _).trans (le_of_eq ?_)
    congr 1
    omega
  · have hhigh : h * m ≤ i' * m := Nat.mul_le_mul_right m (by omega)
    have hall : i' * m + m ≤ 2 * (h * m) := by
      have := Nat.mul_le_mul_right m (show i' + 1 ≤ 2 * h by omega)
      rw [hA1, hn] at this; exact this
    have hcond : ¬ (2 * (i' + 1) ≤ 2 * h) := by omega
    simp only [if_neg hcond] at hC
    have e2 : (2 * (i' + 1) - 2 * h - 1) * m + 2 * (h * m) = 2 * (i' * m) + m := by
      have : (2 * (i' + 1) - 2 * h - 1) + 2 * h = 2 * i' + 1 := by omega
      calc (2 * (i' + 1) - 2 * h - 1) * m + 2 * (h * m)
          = ((2 * (i' + 1) - 2 * h - 1) + 2 * h) * m := by ring
        _ = 2 * (i' * m) + m := by rw [this]; ring
    have h1 : i' * m + k + 1 + Dm (2 * (h * m)) (i' * m + k + 1) = 2 * (h * m) := by
      unfold Dm; omega
    have h2 : i' * m + k + 1 - Dm (2 * (h * m)) (i' * m + k + 1) - 1
        = 2 * (i' * m + k + 1) - 2 * (h * m) - 1 := by
      unfold Dm; omega
    rw [hC, h1, h2, hn]
    have e3 : pre s (2 * (h * m)) - pre s (2 * (i' * m + k + 1) - 2 * (h * m) - 1)
        - (pre s (2 * (h * m)) - pre s ((2 * (i' + 1) - 2 * h - 1) * m))
        = pre s ((2 * (i' + 1) - 2 * h - 1) * m)
          - pre s (2 * (i' * m + k + 1) - 2 * (h * m) - 1) := by ring
    rw [e3, abs_sub_comm]
    refine (pre_lip' s hs _ _).trans (le_of_eq ?_)
    congr 1
    omega

lemma strip (s : ℕ → ℤ) (hs : ∀ x, |s x| ≤ 1) (h m i' : ℕ) (hi : i' < 2 * h) :
    Xb s m (i' + 1) * Cb s (2 * h) m (i' + 1) - gsum m ≤
      ∑ k ∈ range m, s (i' * m + k + 1) *
        (pre s ((i' * m + k + 1) + Dm (2 * (h * m)) (i' * m + k + 1))
          - pre s ((i' * m + k + 1) - Dm (2 * (h * m)) (i' * m + k + 1) - 1)) := by
  set C := Cb s (2 * h) m (i' + 1) with hCdef
  have hX : Xb s m (i' + 1) = ∑ k ∈ range m, s (i' * m + k + 1) := by
    rw [sum_range_shift]
    unfold Xb
    simp only [Nat.add_sub_cancel]
    rw [show (i' + 1) * m = i' * m + m by ring]
  have key : ∀ k ∈ range m, s (i' * m + k + 1) * C - |2 * (k : ℤ) + 1 - m| ≤
      s (i' * m + k + 1) *
        (pre s ((i' * m + k + 1) + Dm (2 * (h * m)) (i' * m + k + 1))
          - pre s ((i' * m + k + 1) - Dm (2 * (h * m)) (i' * m + k + 1) - 1)) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have he := T_err s hs h m i' k hi hk'
    set T := pre s ((i' * m + k + 1) + Dm (2 * (h * m)) (i' * m + k + 1))
          - pre s ((i' * m + k + 1) - Dm (2 * (h * m)) (i' * m + k + 1) - 1) with hT
    have h1 : |s (i' * m + k + 1) * (T - C)| ≤ |2 * (k : ℤ) + 1 - m| := by
      rw [abs_mul]
      calc |s (i' * m + k + 1)| * |T - C| ≤ 1 * |T - C| :=
            mul_le_mul_of_nonneg_right (hs _) (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact he
    have h2 := neg_abs_le (s (i' * m + k + 1) * (T - C))
    nlinarith
  calc Xb s m (i' + 1) * C - gsum m
      = ∑ k ∈ range m, (s (i' * m + k + 1) * C - |2 * (k : ℤ) + 1 - m|) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hX]; rfl
    _ ≤ _ := Finset.sum_le_sum key


lemma sum_Icc_eq_range (f : ℕ → ℤ) (N : ℕ) :
    ∑ y ∈ Icc 1 N, f y = ∑ t ∈ range N, f (t + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma sum_range_mul' (f : ℕ → ℤ) (m : ℕ) :
    ∀ L, ∑ t ∈ range (L * m), f t = ∑ i ∈ range L, ∑ k ∈ range m, f (i * m + k)
  | 0 => by simp
  | L + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul' f m L, Finset.sum_range_succ]

/-- The key estimate: the window correlation `W` is at least the cell quadratic form minus
`L * Σ|2β-1-m|`. -/
lemma Wm_lower (s : ℕ → ℤ) (hs : ∀ x, |s x| ≤ 1) (h m : ℕ) :
    ∑ i ∈ Icc 1 (2 * h), Xb s m i * Cb s (2 * h) m i - ((2 * h : ℕ) : ℤ) * gsum m
      ≤ Wm s (2 * (h * m)) := by
  have hn : 2 * (h * m) = 2 * h * m := by ring
  set G : ℕ → ℤ := fun y => s y * (pre s (y + Dm (2 * (h * m)) y) - pre s (y - Dm (2 * (h * m)) y - 1))
    with hG
  have h1 : Wm s (2 * (h * m)) = ∑ t ∈ range (2 * (h * m)), G (t + 1) := by
    unfold Wm; rw [sum_Icc_eq_range]
  have hb := sum_range_mul' (fun t => G (t + 1)) m (2 * h)
  rw [← hn] at hb
  rw [h1, hb, sum_Icc_eq_range]
  have h2 : ((2 * h : ℕ) : ℤ) * gsum m = ∑ i ∈ range (2 * h), gsum m := by
    simp
  rw [h2, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i' hi'
  exact strip s hs h m i' (Finset.mem_range.mp hi')

lemma Xb_abs (s : ℕ → ℤ) (hs : ∀ x, |s x| ≤ 1) (m i : ℕ) (hi : 1 ≤ i) : |Xb s m i| ≤ m := by
  unfold Xb
  have := pre_lip s hs (a := (i - 1) * m) (b := i * m)
    (Nat.mul_le_mul_right m (by omega))
  have e : i * m - (i - 1) * m = m := by
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Nat.add_mul, one_mul]; omega
  rw [e] at this
  exact this

lemma qform_eq (L : ℕ) (X : ℕ → ℤ) :
    qform L (fun j => (X j : ℝ)) =
      2 * ((∑ i ∈ Icc 1 L, X i * ∑ j ∈ Icc 1 L, (Bprs L i j : ℤ) * X j : ℤ) : ℝ) := by
  unfold qform Aprs
  push_cast
  have e1 : ∀ i j : ℕ, ((Bprs L i j : ℝ) + (Bprs L j i : ℝ)) * (X i : ℝ) * (X j : ℝ)
      = (Bprs L i j : ℝ) * X i * X j + (Bprs L j i : ℝ) * X i * X j := by
    intros; ring
  simp only [e1, Finset.sum_add_distrib]
  have e2 : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (Bprs L j i : ℝ) * X i * X j
      = ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (Bprs L i j : ℝ) * X i * X j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have e3 : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (Bprs L i j : ℝ) * X i * X j
      = ∑ x ∈ Icc 1 L, (X x : ℝ) * ∑ y ∈ Icc 1 L, (Bprs L x y : ℝ) * X y := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [e2, e3]; ring

lemma cert_apply (L m : ℕ) (d : ℕ → ℚ) (hd : DiagCert L d) (s : ℕ → ℤ) (hs : ∀ x, |s x| ≤ 1) :
    -((m : ℝ) ^ 2 * ∑ i ∈ Icc 1 L, (d i : ℝ))
      ≤ 2 * ((∑ i ∈ Icc 1 L, Xb s m i * Cb s L m i : ℤ) : ℝ) := by
  have h := hd.2 (fun j => (Xb s m j : ℝ))
  rw [qform_eq] at h
  have h2 : ∑ i ∈ Icc 1 L, (d i : ℝ) * (Xb s m i : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * ∑ i ∈ Icc 1 L, (d i : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hd0 : (0 : ℝ) ≤ (d i : ℝ) := by exact_mod_cast hd.1 i hi
    have hx := abs_le.mp (Xb_abs s hs m i hi1)
    have hx2 : (Xb s m i) ^ 2 ≤ (m : ℤ) ^ 2 := sq_le_sq' hx.1 hx.2
    have hx3 : (Xb s m i : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by exact_mod_cast hx2
    nlinarith
  have e : (∑ i ∈ Icc 1 L, Xb s m i * ∑ j ∈ Icc 1 L, (Bprs L i j : ℤ) * Xb s m j : ℤ)
      = ∑ i ∈ Icc 1 L, Xb s m i * Cb s L m i := rfl
  rw [e] at h
  linarith

end Erdos1186Night2
