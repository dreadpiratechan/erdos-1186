import Mathlib
import Erdos.Proofs.P1186LowA

/-!
# Erdos 1186 - MODEL2 lower bound, part A: the discrete cut-cell inequality (night 2, lane `lean1186c`)

`problems/1186/MODEL2.md` (lane sdp1186m) proves the cut-cell inequality (its Lemma 2 + Lemma 3) through a continuum
lemma on integrals.  Here is a DISCRETE proof with the same choice of the constant `c` and the same pointwise bounds on
the prefix sums `T k = pre t k` of the b-block, in integer arithmetic only.

* `lemA`: for `s, t : ℕ → ℤ` with values in `[-1,1]`, `w = 2N`, `X = Σ_{i ≤ w} s_i`, `Y = Σ_{j ≤ w} t_j`:
  `8 Σ_{i ≤ w} s_i T(⌊i/2⌋) - 2 X Y ≤ (w² - X²) + 3 (w² - Y²) + 4w + 16`.
  This is MODEL2's `E(φ,ψ) ≤ Γ(x,y)` (`E = Σ s_i (T(⌊i/2⌋) - Y/4)`, `w² Γ = (w²-X²)/8 + 3(w²-Y²)/8`) with an additive error
  `(4w+16)/8`.  Proof: WLOG `Y ≥ 0` (`(s,t) ↦ (-s,-t)`).  Case 1 `X ≥ 2Y - w`: `|T(k)| ≤ k`, `Σ_i ⌊i/2⌋ = w²/4`, and
  `(X-Y)² + 2Y² ≤ 2w²` on the triangle.  Case 2 `X < 2Y - w`: with `C = 4c = 2Y - w - X > 0`,
  `4 Σ s_i T = Σ s_i (4T - C) + C X ≤ Σ |4T - C| + C X`, and `|4T(k) - C|` is at most `C + 4k` (all `k`),
  `C - 4Y + 4w - 4k` (`4k ≤ w - X`), `4k - C` (`4k ≥ w - X`); summing these over `k ≤ N` split at
  `τ = ⌊(w-Y)/2⌋` and `K = ⌊(w-X)/4⌋` gives the bound, the slack being `(w-Y)(3w+2X-Y) + 4(1-e₁)(e₁+3) + (e₂-2)² ≥ 0`.
* `DC_two_sided`: the double cut cell.  For a b-block `t` (length `w`) and an a-double-block `u` (length `2w`),
  `|8 Σ_{j ≤ w} t_j U(2j-1) - 6 U₁ Y - 2 U₂ Y| ≤ (w² - U₁²) + (w² - U₂²) + 6 (w² - Y²) + 8w + 32`
  (`U` = prefix sums of `u`, `U₁ = U(w)`, `U₂ = U(2w) - U(w)`): cells A and B of MODEL2 Lemma 1 (the B part by the
  reflection `i ↦ w+1-i`), and the upper cells C, D by `t ↦ -t`.
-/

open Finset

namespace Erdos1186Night2M2

open Erdos1186Night2 (pre pre_zero pre_succ sum_Ioc_eq pre_lip)

lemma pre_eq_Icc (s : ℕ → ℤ) (n : ℕ) : pre s n = ∑ i ∈ Icc 1 n, s i := by
  unfold pre
  congr 1

lemma pre_abs (t : ℕ → ℤ) (ht : ∀ x, |t x| ≤ 1) (k : ℕ) : |pre t k| ≤ k := by
  have := pre_lip t ht (Nat.zero_le k)
  simpa [pre_zero] using this

lemma pre_tail (t : ℕ → ℤ) (ht : ∀ x, |t x| ≤ 1) {k w : ℕ} (h : k ≤ w) :
    |pre t w - pre t k| ≤ (w : ℤ) - k := by
  have := pre_lip t ht h
  have e : ((w - k : ℕ) : ℤ) = (w : ℤ) - k := by omega
  rwa [e] at this

lemma pre_neg (t : ℕ → ℤ) (k : ℕ) : pre (fun x => -t x) k = -pre t k := by
  unfold pre; rw [Finset.sum_neg_distrib]

lemma mul_le_of_abs {a b B : ℤ} (ha : |a| ≤ 1) (hb : |b| ≤ B) : a * b ≤ B :=
  calc a * b ≤ |a * b| := le_abs_self _
    _ = |a| * |b| := abs_mul a b
    _ ≤ 1 * B := mul_le_mul ha hb (abs_nonneg _) zero_le_one
    _ = B := one_mul B

lemma sum_pairs (F : ℕ → ℤ) : ∀ N, ∑ i ∈ Icc 1 (2 * N), F i = ∑ k ∈ range N, (F (2 * k + 1) + F (2 * k + 2))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by ring, Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega), sum_pairs F N, Finset.sum_range_succ]
    have e : 2 * N + 1 + 1 = 2 * N + 2 := by ring
    rw [e]; ring

lemma sum_odd (N : ℕ) : ∑ k ∈ range N, (2 * (k : ℤ) + 1) = (N : ℤ) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma gauss (a b : ℕ) (α β : ℤ) (h : a ≤ b) :
    2 * ∑ k ∈ Ico a b, (α + β * (k : ℤ)) = 2 * ((b : ℤ) - a) * α + β * ((b : ℤ) * (b - 1) - (a : ℤ) * (a - 1)) := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [Finset.sum_Ico_succ_top hab, mul_add, ih]; push_cast; ring

/-- `lemA` under `Y ≥ 0`. -/
theorem lemA0 (s t : ℕ → ℤ) (hs : ∀ x, |s x| ≤ 1) (ht : ∀ x, |t x| ≤ 1) (N : ℕ)
    (hY : 0 ≤ pre t (2 * N)) :
    8 * ∑ i ∈ Icc 1 (2 * N), s i * pre t (i / 2) - 2 * pre s (2 * N) * pre t (2 * N)
      ≤ 4 * (2 * (N : ℤ)) ^ 2 - (pre s (2 * N)) ^ 2 - 3 * (pre t (2 * N)) ^ 2 + 4 * (2 * (N : ℤ)) + 16 := by
  have hXa := pre_abs s hs (2 * N)
  have hYa := pre_abs t ht (2 * N)
  have hXs : pre s (2 * N) = ∑ k ∈ range N, (s (2 * k + 1) + s (2 * k + 2)) := by
    rw [pre_eq_Icc, sum_pairs]
  set X := pre s (2 * N) with hX
  set Y := pre t (2 * N) with hYd
  push_cast at hXa hYa
  rw [abs_le] at hXa hYa
  rw [sum_pairs (fun i => s i * pre t (i / 2)) N]
  have e1 : ∀ k, (2 * k + 1) / 2 = k := by intro k; omega
  have e2 : ∀ k, (2 * k + 2) / 2 = k + 1 := by intro k; omega
  simp only [e1, e2]
  by_cases hc : 2 * Y - 2 * N ≤ X
  · -- case 1: `c = 0`
    have hb : ∀ k ∈ range N, s (2 * k + 1) * pre t k + s (2 * k + 2) * pre t (k + 1) ≤ 2 * (k : ℤ) + 1 := by
      intro k _
      have a1 := mul_le_of_abs (hs (2 * k + 1)) (pre_abs t ht k)
      have a2 := mul_le_of_abs (hs (2 * k + 2)) (pre_abs t ht (k + 1))
      push_cast at a2
      linarith
    have hsum := Finset.sum_le_sum hb
    rw [sum_odd] at hsum
    have ha : 0 ≤ 2 * (N : ℤ) - X := by linarith
    have hb' : 0 ≤ 2 * (N : ℤ) + X - 2 * Y := by linarith
    nlinarith [mul_nonneg ha hb', mul_nonneg ha hY, mul_nonneg hb' hY, sq_nonneg (2 * (N : ℤ) - X),
      sq_nonneg (2 * (N : ℤ) + X - 2 * Y)]
  · -- case 2
    push_neg at hc
    set C := 2 * Y - 2 * N - X with hC
    have hC1 : 1 ≤ C := by omega
    obtain ⟨τ, hτ1, hτ2⟩ : ∃ τ : ℕ, 2 * (τ : ℤ) ≤ 2 * N - Y ∧ 2 * N - Y ≤ 2 * (τ : ℤ) + 1 := by
      refine ⟨((2 * (N : ℤ) - Y) / 2).toNat, ?_, ?_⟩ <;> omega
    obtain ⟨K, hK1, hK2⟩ : ∃ K : ℕ, 4 * (K : ℤ) ≤ 2 * N - X ∧ 2 * N - X ≤ 4 * (K : ℤ) + 3 := by
      refine ⟨((2 * (N : ℤ) - X) / 4).toNat, ?_, ?_⟩ <;> omega
    have hτK : τ ≤ K := by omega
    have hKN : K ≤ N := by omega
    set f : ℕ → ℤ := fun k => |4 * pre t k - C| with hf
    -- step a
    have ha : 4 * ∑ k ∈ range N, (s (2 * k + 1) * pre t k + s (2 * k + 2) * pre t (k + 1))
        ≤ ∑ k ∈ range N, (f k + f (k + 1)) + C * X := by
      rw [hXs, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k _
      have b1 := mul_le_of_abs (hs (2 * k + 1)) (le_refl |4 * pre t k - C|)
      have b2 := mul_le_of_abs (hs (2 * k + 2)) (le_refl |4 * pre t (k + 1) - C|)
      simp only [hf]
      nlinarith
    -- step b
    have hf0 : ∀ k, 0 ≤ f k := fun k => abs_nonneg _
    have hb : ∑ k ∈ range N, (f k + f (k + 1)) ≤ 2 * ∑ k ∈ range (N + 1), f k := by
      rw [Finset.sum_add_distrib]
      have h1 : ∑ k ∈ range N, f k ≤ ∑ k ∈ range (N + 1), f k := by
        rw [Finset.sum_range_succ]; linarith [hf0 N]
      have h2 : ∑ k ∈ range N, f (k + 1) ≤ ∑ k ∈ range (N + 1), f k := by
        rw [Finset.sum_range_succ']; linarith [hf0 0]
      linarith
    -- step c: split at τ and K+1
    have hsplit : ∑ k ∈ range (N + 1), f k
        = ∑ k ∈ Ico 0 τ, f k + ∑ k ∈ Ico τ (K + 1), f k + ∑ k ∈ Ico (K + 1) (N + 1), f k := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le τ) (by omega : τ ≤ K + 1),
        Finset.sum_Ico_consecutive _ (by omega : 0 ≤ K + 1) (by omega : K + 1 ≤ N + 1)]
    -- step d: the three pieces
    have hP1 : ∑ k ∈ Ico 0 τ, f k ≤ ∑ k ∈ Ico 0 τ, (C + 4 * (k : ℤ)) := by
      apply Finset.sum_le_sum; intro k _
      have h := abs_le.mp (pre_abs t ht k)
      simp only [hf]; rw [abs_le]; constructor <;> linarith
    have hP2 : ∑ k ∈ Ico τ (K + 1), f k ≤ ∑ k ∈ Ico τ (K + 1), ((C - 4 * Y + 8 * N) + (-4) * (k : ℤ)) := by
      apply Finset.sum_le_sum; intro k hk
      have hk' := Finset.mem_Ico.mp hk
      have hkK : 4 * (k : ℤ) ≤ 2 * N - X := by
        have : (k : ℤ) ≤ K := by exact_mod_cast (by omega : k ≤ K)
        linarith
      have h := abs_le.mp (pre_abs t ht k)
      have h' := abs_le.mp (pre_tail t ht (by omega : k ≤ 2 * N))
      push_cast at h'
      simp only [hf]; rw [abs_le]; constructor <;> linarith
    have hP3 : ∑ k ∈ Ico (K + 1) (N + 1), f k ≤ ∑ k ∈ Ico (K + 1) (N + 1), (-C + 4 * (k : ℤ)) := by
      apply Finset.sum_le_sum; intro k hk
      have hk' := Finset.mem_Ico.mp hk
      have hkK : 2 * N - X ≤ 4 * (k : ℤ) := by
        have : (K : ℤ) + 1 ≤ k := by exact_mod_cast (by omega : K + 1 ≤ k)
        linarith
      have h := abs_le.mp (pre_abs t ht k)
      have h' := abs_le.mp (pre_tail t ht (by omega : k ≤ 2 * N))
      push_cast at h'
      simp only [hf]; rw [abs_le]; constructor <;> linarith
    have g1 := gauss 0 τ C 4 (Nat.zero_le τ)
    have g2 := gauss τ (K + 1) (C - 4 * Y + 8 * N) (-4) (by omega)
    have g3 := gauss (K + 1) (N + 1) (-C) 4 (by omega)
    push_cast at g1 g2 g3
    -- step e: the polynomial inequality
    have q1 : 0 ≤ (2 * (N : ℤ) - Y) * (6 * N + 2 * X - Y) := by
      apply mul_nonneg <;> linarith
    have q2 : 0 ≤ (1 - (2 * (N : ℤ) - Y - 2 * τ)) * ((2 * (N : ℤ) - Y - 2 * τ) + 3) := by
      apply mul_nonneg <;> linarith
    have q3 : 0 ≤ ((2 * (N : ℤ) - X - 4 * K) - 2) ^ 2 := sq_nonneg _
    have hlin : 8 * (∑ k ∈ range N, (s (2 * k + 1) * pre t k + s (2 * k + 2) * pre t (k + 1)))
        ≤ 2 * (2 * (τ : ℤ) * C + 4 * ((τ : ℤ) * (τ - 1)))
          + 2 * (2 * ((K : ℤ) + 1 - τ) * (C - 4 * Y + 8 * N) - 4 * (((K : ℤ) + 1) * K - (τ : ℤ) * (τ - 1)))
          + 2 * (2 * ((N : ℤ) + 1 - (K + 1)) * (-C) + 4 * (((N : ℤ) + 1) * N - ((K : ℤ) + 1) * K))
          + 2 * C * X := by
      linarith [ha, hb, hsplit, hP1, hP2, hP3, g1, g2, g3]
    rw [hC] at hlin
    linarith [hlin, q1, q2, q3]

/-- **The discrete cut-cell inequality** (cell `A` of MODEL2 Lemma 1; MODEL2 Lemma 2 + 3 with error `(4w+16)/8`). -/
theorem lemA (s t : ℕ → ℤ) (hs : ∀ x, |s x| ≤ 1) (ht : ∀ x, |t x| ≤ 1) (N : ℕ) :
    8 * ∑ i ∈ Icc 1 (2 * N), s i * pre t (i / 2) - 2 * pre s (2 * N) * pre t (2 * N)
      ≤ 4 * (2 * (N : ℤ)) ^ 2 - (pre s (2 * N)) ^ 2 - 3 * (pre t (2 * N)) ^ 2 + 4 * (2 * (N : ℤ)) + 16 := by
  by_cases hY : 0 ≤ pre t (2 * N)
  · exact lemA0 s t hs ht N hY
  · have hs' : ∀ x, |(fun x => -s x) x| ≤ 1 := fun x => by simpa using hs x
    have ht' : ∀ x, |(fun x => -t x) x| ≤ 1 := fun x => by simpa using ht x
    have h := lemA0 (fun x => -s x) (fun x => -t x) hs' ht' N (by rw [pre_neg]; linarith)
    simp only [pre_neg] at h
    have e : ∑ i ∈ Icc 1 (2 * N), -s i * -pre t (i / 2) = ∑ i ∈ Icc 1 (2 * N), s i * pre t (i / 2) := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e] at h
    nlinarith [h]

/-! ## The double cut cell -/

lemma sum_Icc_add (G : ℕ → ℤ) (b : ℕ) : ∀ m, ∑ y ∈ Icc 1 (b + m), G y = ∑ y ∈ Icc 1 b, G y + ∑ j ∈ Icc 1 m, G (b + j)
  | 0 => by simp
  | m + 1 => by
    rw [show b + (m + 1) = (b + m) + 1 by ring, Finset.sum_Icc_succ_top (by omega), sum_Icc_add G b m,
      Finset.sum_Icc_succ_top (by omega)]
    have e : b + (m + 1) = b + m + 1 := by ring
    rw [e]; ring

lemma sum_reflect (g : ℕ → ℤ) (w : ℕ) : ∑ i ∈ Icc 1 w, g i = ∑ i ∈ Icc 1 w, g (w + 1 - i) := by
  apply Finset.sum_nbij' (fun i => w + 1 - i) (fun i => w + 1 - i)
  · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; omega
  · intro i hi; simp only [Finset.mem_Icc] at hi; omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    have e : w + 1 - (w + 1 - i) = i := by omega
    simp only [e]

/-- prefix sums of a shifted sequence -/
lemma pre_shift (s : ℕ → ℤ) (b : ℕ) : ∀ m, pre (fun k => s (b + k)) m = pre s (b + m) - pre s b
  | 0 => by simp [pre_zero]
  | m + 1 => by
    rw [pre_succ, pre_shift s b m, show b + (m + 1) = (b + m) + 1 by ring, pre_succ]
    ring

/-- prefix sums of the reversed block `t̃ j = t (w + 1 - j)` -/
lemma pre_rev (t : ℕ → ℤ) (w : ℕ) : ∀ m, m ≤ w → pre (fun j => t (w + 1 - j)) m = pre t w - pre t (w - m)
  | 0 => by intro _; simp [pre_zero]
  | m + 1 => by
    intro hm
    rw [pre_succ, pre_rev t w m (by omega)]
    have e : w - m = (w - (m + 1)) + 1 := by omega
    have e2 : w + 1 - (m + 1) = (w - (m + 1)) + 1 := by omega
    rw [e, pre_succ, e2]
    ring

/-- the double cut cell in b-view: `Σ_{j ≤ w} t_j U(2j-1)` -/
def DCb (t u : ℕ → ℤ) (w : ℕ) : ℤ := ∑ j ∈ Icc 1 w, t j * pre u (2 * j - 1)

lemma DCb_swap (t u : ℕ → ℤ) (w : ℕ) :
    DCb t u w = ∑ k ∈ Icc 1 (2 * w), u k * (pre t w - pre t (k / 2)) := by
  unfold DCb
  have h1 : ∀ j ∈ Icc 1 w, t j * pre u (2 * j - 1) = ∑ k ∈ Icc 1 (2 * j - 1), t j * u k := by
    intro j _; rw [pre_eq_Icc, Finset.mul_sum]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := Icc 1 (2 * w)) (s' := fun k => Ioc (k / 2) w)]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [← sum_Ioc_eq t (by omega : k / 2 ≤ w), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  · intro j k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega

/-- **The double cut cell, lower bound** (cells A and B of MODEL2 Lemma 1, w = 2N). -/
theorem DC_lower (t u : ℕ → ℤ) (ht : ∀ x, |t x| ≤ 1) (hu : ∀ x, |u x| ≤ 1) (N : ℕ) :
    -((4 * (2 * (N : ℤ)) ^ 2 - (pre u (2 * N)) ^ 2 - 3 * (pre t (2 * N)) ^ 2 + 4 * (2 * (N : ℤ)) + 16)
      + (4 * (2 * (N : ℤ)) ^ 2 - (pre u (2 * (2 * N)) - pre u (2 * N)) ^ 2 - 3 * (pre t (2 * N)) ^ 2
          + 4 * (2 * (N : ℤ)) + 16))
      ≤ 8 * DCb t u (2 * N) - 6 * pre u (2 * N) * pre t (2 * N)
          - 2 * (pre u (2 * (2 * N)) - pre u (2 * N)) * pre t (2 * N) := by
  set w := 2 * N with hw
  set Y := pre t w with hY
  rw [DCb_swap, show 2 * w = w + w by ring, sum_Icc_add]
  -- A part
  have hA := lemA u t hu ht N
  rw [← hw] at hA
  have eA : ∑ k ∈ Icc 1 w, u k * (Y - pre t (k / 2)) = pre u w * Y - ∑ k ∈ Icc 1 w, u k * pre t (k / 2) := by
    rw [pre_eq_Icc u w, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  -- B part, by reflection
  set ut : ℕ → ℤ := fun i => -u (2 * w + 1 - i) with hut
  set tt : ℕ → ℤ := fun j => t (w + 1 - j) with htt
  have hut' : ∀ x, |ut x| ≤ 1 := fun x => by simpa [hut] using hu (2 * w + 1 - x)
  have htt' : ∀ x, |tt x| ≤ 1 := fun x => by simpa [htt] using ht (w + 1 - x)
  have hB := lemA ut tt hut' htt' N
  rw [← hw] at hB
  have hYt : pre tt w = Y := by
    rw [htt, pre_rev t w w le_rfl, Nat.sub_self, pre_zero, sub_zero]
  have hUt : pre ut w = -(pre u (w + w) - pre u w) := by
    rw [pre_eq_Icc, sum_reflect]
    have e1 : ∀ i ∈ Icc 1 w, ut (w + 1 - i) = -u (w + i) := by
      intro i hi
      simp only [Finset.mem_Icc] at hi
      simp only [hut]
      congr 2; omega
    rw [Finset.sum_congr rfl e1, Finset.sum_neg_distrib]
    congr 1
    rw [← pre_shift u w w, pre_eq_Icc]
  have eB : ∑ j ∈ Icc 1 w, u (w + j) * (Y - pre t ((w + j) / 2)) = -∑ i ∈ Icc 1 w, ut i * pre tt (i / 2) := by
    have e1 : ∀ j ∈ Icc 1 w, u (w + j) * (Y - pre t ((w + j) / 2)) = u (w + j) * pre tt (N - j / 2) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      rw [htt, pre_rev t w (N - j / 2) (by omega)]
      have e : w - (N - j / 2) = (w + j) / 2 := by omega
      rw [e]
    rw [Finset.sum_congr rfl e1, sum_reflect, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have e2 : w + (w + 1 - i) = 2 * w + 1 - i := by omega
    have e3 : N - (w + 1 - i) / 2 = i / 2 := by omega
    rw [e2, e3, hut]
    ring
  rw [eA, eB]
  rw [hYt, hUt] at hB
  nlinarith [hA, hB]

/-- **The double cut cell, both directions** (the upper cells C, D of MODEL2 are `t ↦ -t`). -/
theorem DC_upper (t u : ℕ → ℤ) (ht : ∀ x, |t x| ≤ 1) (hu : ∀ x, |u x| ≤ 1) (N : ℕ) :
    8 * DCb t u (2 * N) - 6 * pre u (2 * N) * pre t (2 * N)
          - 2 * (pre u (2 * (2 * N)) - pre u (2 * N)) * pre t (2 * N)
      ≤ (4 * (2 * (N : ℤ)) ^ 2 - (pre u (2 * N)) ^ 2 - 3 * (pre t (2 * N)) ^ 2 + 4 * (2 * (N : ℤ)) + 16)
      + (4 * (2 * (N : ℤ)) ^ 2 - (pre u (2 * (2 * N)) - pre u (2 * N)) ^ 2 - 3 * (pre t (2 * N)) ^ 2
          + 4 * (2 * (N : ℤ)) + 16) := by
  have ht' : ∀ x, |(fun x => -t x) x| ≤ 1 := fun x => by simpa using ht x
  have h := DC_lower (fun x => -t x) u ht' hu N
  have e : DCb (fun x => -t x) u (2 * N) = -DCb t u (2 * N) := by
    unfold DCb; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  rw [e, pre_neg] at h
  nlinarith [h]

end Erdos1186Night2M2
