import Mathlib
import Erdos.Proofs.P1186LowA
import Erdos.Proofs.P1186M2
import Erdos.Proofs.P1186M2LowA

/-!
# Erdos 1186 - MODEL2 lower bound, part B: the cover inequality for the window correlation (night 2, lane `lean1186c`)

`W = Wm s n = Σ_y s_y Σ_{x : 1 ≤ 2y - x ≤ n} s_x` (`P1186LowA.lean`; it is MODEL2's `W = Σ_{(a,b) ∈ R_n} s_a s_b`).
For `L = 2h`, `w = 2N`, `n = L w` and block sums `X_p = Xb s w p` (`P1186LowA.lean`):

`W_lower`: `2 Σ_q X_q Σ_p K4 L p q X_p - 8 Σ_p (w² - X_p²) - L (8w + 32) ≤ 8 W`,

i.e. MODEL2 Theorem 1's `W ≥ w² [xᵀ S x - Σ (1 - x_p²)] - O(Lw)`.  Proof: the `y`-sum is split into the lower half
(`y ≤ n/2`, window `[1, 2y-1]`) and the upper half (window `[2y-n, n]`), each into `h` blocks.  The lower block `q` and the
upper block `h + q` both see the a-double-block `(2q-1, 2q)` as their cut cells (types A, B resp. D, C of MODEL2 Lemma 1); the
full cells give `4 pre(...)` exactly (`KS_lo`, `KS_hi`: the column sums of `K4`), and the cut cells are bounded by
`DC_lower` / `DC_upper` (`P1186M2LowA.lean`).  Each block is an a-block of two cut cells and a b-block of two cut cells,
which is the bookkeeping `Σ_q (pen) = 8 Σ_p (w² - X_p²)`.
-/

open Finset

namespace Erdos1186Night2M2

open Erdos1186Night2 (pre pre_zero pre_succ sum_Ioc_eq pre_lip Dm Wm Xb sum_Icc_eq_range)

/-- the summand of `Wm` -/
def Gw (s : ℕ → ℤ) (n y : ℕ) : ℤ := s y * (pre s (y + Dm n y) - pre s (y - Dm n y - 1))

lemma Wm_eq (s : ℕ → ℤ) (n : ℕ) : Wm s n = ∑ y ∈ Icc 1 n, Gw s n y := rfl

lemma sum_blocks (F : ℕ → ℤ) (w : ℕ) : ∀ h, ∑ y ∈ Icc 1 (h * w), F y = ∑ q ∈ Icc 1 h, ∑ j ∈ Icc 1 w, F ((q - 1) * w + j)
  | 0 => by simp
  | h + 1 => by
    rw [show (h + 1) * w = h * w + w by ring, sum_Icc_add, sum_blocks F w h, Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]

lemma sum_pairs' (f : ℕ → ℤ) (h : ℕ) : ∑ p ∈ Icc 1 (2 * h), f p = ∑ q ∈ Icc 1 h, (f (2 * q - 1) + f (2 * q)) := by
  rw [sum_pairs, sum_Icc_eq_range]
  apply Finset.sum_congr rfl; intro k _
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [e1, e2]

lemma sum_halves (f : ℕ → ℤ) (h : ℕ) : ∑ p ∈ Icc 1 (2 * h), f p = ∑ q ∈ Icc 1 h, (f q + f (h + q)) := by
  rw [show 2 * h = h + h by ring, sum_Icc_add, Finset.sum_add_distrib]

lemma tele_Xb (s : ℕ → ℤ) (w : ℕ) : ∀ M, ∑ p ∈ Icc 1 M, Xb s w p = pre s (M * w)
  | 0 => by simp [pre_zero]
  | M + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), tele_Xb s w M]
    unfold Xb; simp only [Nat.add_sub_cancel]; ring

/-- column sums of `K4` for a lower block `q ≤ h` -/
lemma KS_lo (h q : ℕ) (X : ℕ → ℤ) (hq1 : 1 ≤ q) (hqh : q ≤ h) :
    ∑ p ∈ Icc 1 (2 * h), (K4 (2 * h) p q : ℤ) * X p
      = 4 * ∑ p ∈ Icc 1 (2 * q - 2), X p + 3 * X (2 * q - 1) + X (2 * q) := by
  have hK : ∀ p ∈ Icc 1 (2 * h), (K4 (2 * h) p q : ℤ) * X p
      = 4 * (if p ≤ 2 * q - 2 then X p else 0) + 3 * (if p = 2 * q - 1 then X p else 0)
        + (if p = 2 * q then X p else 0) := by
    intro p hp
    simp only [Finset.mem_Icc] at hp
    unfold K4
    split_ifs <;> push_cast <;> omega
  rw [Finset.sum_congr rfl hK, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.sum_filter]
  have hf : (Icc 1 (2 * h)).filter (fun p => p ≤ 2 * q - 2) = Icc 1 (2 * q - 2) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hf, if_pos (by simp only [Finset.mem_Icc]; omega), if_pos (by simp only [Finset.mem_Icc]; omega)]

/-- column sums of `K4` for an upper block `h + q`, `q ≤ h` -/
lemma KS_hi (h q : ℕ) (X : ℕ → ℤ) (hq1 : 1 ≤ q) (hqh : q ≤ h) :
    ∑ p ∈ Icc 1 (2 * h), (K4 (2 * h) p (h + q) : ℤ) * X p
      = 4 * (∑ p ∈ Icc 1 (2 * h), X p - ∑ p ∈ Icc 1 (2 * q), X p) + 3 * X (2 * q) + X (2 * q - 1) := by
  have hK : ∀ p ∈ Icc 1 (2 * h), (K4 (2 * h) p (h + q) : ℤ) * X p
      = 4 * X p - 4 * (if p ≤ 2 * q then X p else 0) + 3 * (if p = 2 * q then X p else 0)
        + (if p = 2 * q - 1 then X p else 0) := by
    intro p hp
    simp only [Finset.mem_Icc] at hp
    unfold K4
    split_ifs <;> push_cast <;> omega
  rw [Finset.sum_congr rfl hK, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.sum_ite_eq',
    ← Finset.sum_filter]
  have hf : (Icc 1 (2 * h)).filter (fun p => p ≤ 2 * q) = Icc 1 (2 * q) := by
    ext p; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
  rw [hf, if_pos (by simp only [Finset.mem_Icc]; omega), if_pos (by simp only [Finset.mem_Icc]; omega)]
  ring

lemma block_lo (s : ℕ → ℤ) (h w a : ℕ) (ha : a + w ≤ h * w) :
    ∑ j ∈ Icc 1 w, Gw s (2 * (h * w)) (a + j)
      = pre (fun j => s (a + j)) w * pre s (2 * a) + DCb (fun j => s (a + j)) (fun k => s (2 * a + k)) w := by
  unfold DCb
  rw [pre_eq_Icc (fun j => s (a + j)) w, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  unfold Gw
  have hD : Dm (2 * (h * w)) (a + j) = a + j - 1 := by unfold Dm; omega
  rw [hD]
  have e1 : a + j + (a + j - 1) = 2 * a + (2 * j - 1) := by omega
  have e2 : a + j - (a + j - 1) - 1 = 0 := by omega
  rw [e1, e2, pre_zero, sub_zero, pre_shift s (2 * a) (2 * j - 1)]
  ring

lemma block_hi (s : ℕ → ℤ) (h w a : ℕ) (ha : a + w ≤ h * w) :
    ∑ j ∈ Icc 1 w, Gw s (2 * (h * w)) (h * w + (a + j))
      = pre (fun j => s (h * w + (a + j))) w * (pre s (2 * (h * w)) - pre s (2 * a))
        - DCb (fun j => s (h * w + (a + j))) (fun k => s (2 * a + k)) w := by
  unfold DCb
  rw [pre_eq_Icc (fun j => s (h * w + (a + j))) w, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  unfold Gw
  have hD : Dm (2 * (h * w)) (h * w + (a + j)) = h * w - a - j := by unfold Dm; omega
  rw [hD]
  have e1 : h * w + (a + j) + (h * w - a - j) = 2 * (h * w) := by omega
  have e2 : h * w + (a + j) - (h * w - a - j) - 1 = 2 * a + (2 * j - 1) := by omega
  rw [e1, e2, pre_shift s (2 * a) (2 * j - 1)]
  ring

/-- **The cover inequality** (MODEL2 Theorem 1, first line, in integer form). -/
theorem W_lower (s : ℕ → ℤ) (hs : ∀ x, |s x| ≤ 1) (h N : ℕ) :
    2 * ∑ q ∈ Icc 1 (2 * h), Xb s (2 * N) q * ∑ p ∈ Icc 1 (2 * h), (K4 (2 * h) p q : ℤ) * Xb s (2 * N) p
      - 8 * ∑ p ∈ Icc 1 (2 * h), ((2 * (N : ℤ)) ^ 2 - (Xb s (2 * N) p) ^ 2)
      - (2 * (h : ℤ)) * (8 * (2 * (N : ℤ)) + 32)
      ≤ 8 * Wm s (2 * (h * (2 * N))) := by
  have hwz0 : (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) := by push_cast; ring
  rw [hwz0]
  set w := 2 * N with hw
  set X := Xb s w with hX
  -- the per-pair inequality
  have key : ∀ q ∈ Icc 1 h,
      2 * (X q * ∑ p ∈ Icc 1 (2 * h), (K4 (2 * h) p q : ℤ) * X p)
        + 2 * (X (h + q) * ∑ p ∈ Icc 1 (2 * h), (K4 (2 * h) p (h + q) : ℤ) * X p)
        - (2 * ((w : ℤ) ^ 2 - X (2 * q - 1) ^ 2) + 2 * ((w : ℤ) ^ 2 - X (2 * q) ^ 2)
          + 6 * ((w : ℤ) ^ 2 - X q ^ 2) + 6 * ((w : ℤ) ^ 2 - X (h + q) ^ 2))
        - 2 * (8 * (w : ℤ) + 32)
      ≤ 8 * (∑ j ∈ Icc 1 w, Gw s (2 * (h * w)) ((q - 1) * w + j)
          + ∑ j ∈ Icc 1 w, Gw s (2 * (h * w)) (h * w + ((q - 1) * w + j))) := by
    intro q hq
    simp only [Finset.mem_Icc] at hq
    obtain ⟨hq1, hqh⟩ := hq
    set a := (q - 1) * w with ha_def
    have hqa : q * w = a + w := by
      rw [ha_def]; obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    have ha : a + w ≤ h * w := by rw [← hqa]; exact Nat.mul_le_mul_right w hqh
    rw [block_lo s h w a ha, block_hi s h w a ha, KS_lo h q X hq1 hqh, KS_hi h q X hq1 hqh,
      tele_Xb, tele_Xb, tele_Xb]
    -- identify the block sums
    have e2a : (2 * q - 2) * w = 2 * a := by
      rw [ha_def, show 2 * q - 2 = 2 * (q - 1) by omega]; ring
    have e2a1 : (2 * q - 1) * w = 2 * a + w := by
      rw [ha_def, show 2 * q - 1 = 2 * (q - 1) + 1 by omega]; ring
    have e2a2 : (2 * q) * w = 2 * a + w + w := by
      rw [show 2 * q * w = 2 * (q * w) by ring, hqa]; ring
    have e2h : (2 * h) * w = 2 * (h * w) := by ring
    have hY : pre (fun j => s (a + j)) w = X q := by
      rw [pre_shift, hX]; unfold Xb; rw [hqa, ← ha_def]
    have hY' : pre (fun j => s (h * w + (a + j))) w = X (h + q) := by
      have hfun : (fun j => s (h * w + (a + j))) = (fun j => s ((h * w + a) + j)) := by
        funext j; rw [Nat.add_assoc]
      rw [hfun, pre_shift, hX]; unfold Xb
      rw [show (h + q) * w = h * w + a + w by rw [Nat.add_mul, hqa]; ring,
        show h + q - 1 = h + (q - 1) by omega, Nat.add_mul, ← ha_def]
    have hU1 : pre (fun k => s (2 * a + k)) w = X (2 * q - 1) := by
      rw [pre_shift, hX]; unfold Xb
      rw [e2a1, show 2 * q - 1 - 1 = 2 * q - 2 by omega, e2a]
    have hU2 : pre (fun k => s (2 * a + k)) (2 * w) - pre (fun k => s (2 * a + k)) w = X (2 * q) := by
      rw [pre_shift, pre_shift, hX]; unfold Xb
      rw [e2a2, show 2 * q - 1 = 2 * q - 1 from rfl, e2a1]; ring_nf
    have hlo := DC_lower (fun j => s (a + j)) (fun k => s (2 * a + k)) (fun x => hs _) (fun x => hs _) N
    have hhi := DC_upper (fun j => s (h * w + (a + j))) (fun k => s (2 * a + k)) (fun x => hs _) (fun x => hs _) N
    rw [← hw] at hlo hhi
    rw [hU2, hU1, hY] at hlo
    rw [hU2, hU1, hY'] at hhi
    rw [e2a, e2a2, e2h]
    have hP : pre s (2 * a + w + w) = pre s (2 * a) + X (2 * q - 1) + X (2 * q) := by
      rw [← hU1, ← hU2, pre_shift, pre_shift, show 2 * a + 2 * w = 2 * a + w + w by ring]; ring
    rw [hP, hY, hY']
    have hwz : (w : ℤ) = 2 * (N : ℤ) := by rw [hw]; push_cast; ring
    rw [hwz]
    linarith [hlo, hhi]
  -- sum over the pairs
  have hsum := Finset.sum_le_sum key
  rw [Wm_eq, show 2 * (h * w) = h * w + h * w by ring, sum_Icc_add, sum_blocks (Gw s (h * w + h * w)) w h,
    sum_blocks (fun y => Gw s (h * w + h * w) (h * w + y)) w h, ← Finset.sum_add_distrib]
  rw [show h * w + h * w = 2 * (h * w) by ring]
  have h1 : 2 * ∑ q ∈ Icc 1 (2 * h), X q * ∑ p ∈ Icc 1 (2 * h), (K4 (2 * h) p q : ℤ) * X p
      = ∑ q ∈ Icc 1 h, (2 * (X q * ∑ p ∈ Icc 1 (2 * h), (K4 (2 * h) p q : ℤ) * X p)
        + 2 * (X (h + q) * ∑ p ∈ Icc 1 (2 * h), (K4 (2 * h) p (h + q) : ℤ) * X p)) := by
    rw [sum_halves, Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
  have h2 : 8 * ∑ p ∈ Icc 1 (2 * h), ((w : ℤ) ^ 2 - X p ^ 2)
      = ∑ q ∈ Icc 1 h, (2 * ((w : ℤ) ^ 2 - X (2 * q - 1) ^ 2) + 2 * ((w : ℤ) ^ 2 - X (2 * q) ^ 2)
          + 6 * ((w : ℤ) ^ 2 - X q ^ 2) + 6 * ((w : ℤ) ^ 2 - X (h + q) ^ 2)) := by
    have a1 := sum_pairs' (fun p => (w : ℤ) ^ 2 - X p ^ 2) h
    have a2 := sum_halves (fun p => (w : ℤ) ^ 2 - X p ^ 2) h
    simp only at a1 a2
    have : 8 * ∑ p ∈ Icc 1 (2 * h), ((w : ℤ) ^ 2 - X p ^ 2)
        = 2 * ∑ p ∈ Icc 1 (2 * h), ((w : ℤ) ^ 2 - X p ^ 2) + 6 * ∑ p ∈ Icc 1 (2 * h), ((w : ℤ) ^ 2 - X p ^ 2) := by
      ring
    rw [this]
    nth_rewrite 1 [a1]
    rw [a2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro q _; ring
  have h3 : (2 * (h : ℤ)) * (8 * (w : ℤ) + 32) = ∑ q ∈ Icc 1 h, 2 * (8 * (w : ℤ) + 32) := by
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  rw [h1, h2, h3, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact hsum

end Erdos1186Night2M2
