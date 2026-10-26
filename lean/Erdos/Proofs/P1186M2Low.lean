import Mathlib
import Erdos.Proofs.P1186
import Erdos.Proofs.P1186Low
import Erdos.Proofs.P1186M2
import Erdos.Proofs.P1186M2LowA
import Erdos.Proofs.P1186M2LowB

/-!
# Erdos 1186 - the MODEL2 lower-bound reduction, for every even `L ≥ 4` (night 2, lane `lean1186c`)

Main theorem:

```
theorem Erdos1186Night2M2.lower_of_cubeLB (L : ℕ) (hL : 4 ≤ L) (hev : Even L) (σ : ℚ)
    (h : CubeLB L σ) : bound2 L σ ≤ Erdos1186Day.δ 3
```

with `CubeLB`, `bound2` from the shared interface `P1186M2.lean` (`xᵀ C x ≥ -σ` on `[-1,1]^L`, `8C = K4 + K4ᵀ + 8I + 2J`,
`bound2 = 1/16 - (L + σ)/(4L²)`) and `δ` the verbatim upstream definition (`P1186.lean`, formal-conjectures c83a94d).

**Finite form** (`finite_bound2`): for `L = 2h`, `w = 2N ≥ 2`, `n = L w` and EVERY colouring `c`,
`bound2 L σ · n² - n - L ≤ monoCount 3 n c`.

**Proof** (MODEL2.md Sections 1-5, lane sdp1186m, with the cut-cell lemma proved discretely).  With `s = ±1`:
`4V = #APs + (W - n) + R` and `n + 2R = E² + O²` (`P1186Low.lean`, `P1186LowA.lean`), so, keeping the square
(MODEL2 (R)), `32 V ≥ 2n² - 16n + 8W + 2(Σ s)²` (`V_lower`).  The cover inequality `W_lower` (`P1186M2LowB.lean`)
gives `8W ≥ 2 Σ_q X_q Σ_p K4_pq X_p - 8 Σ_p (w² - X_p²) - L(8w+32)`, and `Σ C8 X X = 2 Σ K4 X X + 8 Σ X² + 2(Σ X)²`
(`C8_expand`), so `32 V ≥ 2n² - 16n - 8Lw² - L(8w+32) + 8 w² · xᵀCx` with `x = X/w ∈ [-1,1]^L`; `CubeLB` gives
`xᵀCx ≥ -σ`.  The passage to `δ` uses monotonicity of `n ↦ minMonoCount 3 n` and an `ε`-argument, as in `P1186Low.lean`.
-/

open Finset Filter

namespace Erdos1186Night2M2

open Erdos1186Day
open Erdos1186Night2 (pre pre_zero sg sg_abs sg_sq four_mono mid_expand Rm Rm_one mid_sum parity_sq
  sum_split_parity Dm Wm Xb Xb_abs minMono_mono)

/-- MODEL2 (R) in integer form: `32 V ≥ 2n² - 16n + 8W + 2(Σ s)²`. -/
lemma V_lower (n : ℕ) (c : ℕ → Bool) :
    2 * (n : ℤ) ^ 2 - 16 * n + 8 * Wm (sg c) n + 2 * (pre (sg c) n) ^ 2 ≤ 32 * (monoCount 3 n c : ℤ) := by
  set s := sg c with hs_def
  have hs2 : ∀ x, s x * s x = 1 := sg_sq c
  have h4 := four_mono n c
  rw [mid_expand s n] at h4
  have hA : ∑ y ∈ Icc 1 n, ∑ _d ∈ Icc 1 (Dm n y), (1 : ℤ) = Rm (fun _ => (1 : ℤ)) n := by
    unfold Rm; simp
  have hsum : ∑ y ∈ Icc 1 n, s y * s y = n := by
    rw [Finset.sum_congr rfl (fun y _ => hs2 y)]; simp
  have h5 := Rm_one n
  rw [← hA] at h5
  have hms := mid_sum s n
  rw [parity_sq, hsum] at hms
  have hsp := sum_split_parity s n
  rw [hsum] at h4
  rw [pre_eq_Icc, ← hsp]
  set E := ∑ x ∈ Icc 1 n, if x % 2 = 0 then s x else 0
  set O := ∑ x ∈ Icc 1 n, if x % 2 = 1 then s x else 0
  nlinarith [sq_nonneg (E - O)]

/-- `Σ_pq C8 X_p X_q = 2 Σ_q X_q Σ_p K4_pq X_p + 8 Σ X_p² + 2 (Σ X_p)²`. -/
lemma C8_expand (L : ℕ) (X : ℕ → ℤ) :
    ∑ p ∈ Icc 1 L, ∑ q ∈ Icc 1 L, C8 L p q * X p * X q
      = 2 * ∑ q ∈ Icc 1 L, X q * ∑ p ∈ Icc 1 L, (K4 L p q : ℤ) * X p
        + 8 * ∑ p ∈ Icc 1 L, X p ^ 2 + 2 * (∑ p ∈ Icc 1 L, X p) ^ 2 := by
  have e : ∀ p q, C8 L p q * X p * X q = (K4 L p q : ℤ) * X p * X q + (K4 L q p : ℤ) * X p * X q
      + (if p = q then 8 * X p * X q else 0) + 2 * (X p * X q) := by
    intro p q; unfold C8; split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib]
  have t1 : ∑ p ∈ Icc 1 L, ∑ q ∈ Icc 1 L, (K4 L p q : ℤ) * X p * X q
      = ∑ q ∈ Icc 1 L, X q * ∑ p ∈ Icc 1 L, (K4 L p q : ℤ) * X p := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro q _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  have t2 : ∑ p ∈ Icc 1 L, ∑ q ∈ Icc 1 L, (K4 L q p : ℤ) * X p * X q
      = ∑ q ∈ Icc 1 L, X q * ∑ p ∈ Icc 1 L, (K4 L p q : ℤ) * X p := by
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
  have t3 : ∑ p ∈ Icc 1 L, ∑ q ∈ Icc 1 L, (if p = q then 8 * X p * X q else 0) = 8 * ∑ p ∈ Icc 1 L, X p ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p hp
    rw [Finset.sum_ite_eq, if_pos hp]; ring
  have t4 : ∑ p ∈ Icc 1 L, ∑ q ∈ Icc 1 L, 2 * (X p * X q) = 2 * (∑ p ∈ Icc 1 L, X p) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
  rw [t1, t2, t3, t4]; ring

/-- the quadratic form at `x = X / w` -/
lemma cform_scale (L w : ℕ) (hw : 0 < w) (X : ℕ → ℤ) :
    cform L (fun p => (X p : ℝ) / w)
      = ((∑ p ∈ Icc 1 L, ∑ q ∈ Icc 1 L, C8 L p q * X p * X q : ℤ) : ℝ) / (8 * (w : ℝ) ^ 2) := by
  have hw' : (w : ℝ) ≠ 0 := by positivity
  unfold cform
  have e : ∀ p q, (C8 L p q : ℝ) * ((X p : ℝ) / w) * ((X q : ℝ) / w)
      = ((C8 L p q : ℝ) * X p * X q) / (w : ℝ) ^ 2 := by
    intro p q; field_simp
  simp only [e, ← Finset.sum_div]
  push_cast
  field_simp

/-- **Finite form.**  For `L = 2h`, `w = 2N ≥ 2`, `n = L w = 2 (h w)` and every colouring,
`bound2 L σ · n² - n - L ≤ monoCount 3 n c`. -/
theorem finite_bound2 (h N : ℕ) (hh : 1 ≤ h) (hN : 1 ≤ N) (σ : ℚ) (hσ : CubeLB (2 * h) σ) (c : ℕ → Bool) :
    bound2 (2 * h) σ * ((2 * (h * (2 * N)) : ℕ) : ℝ) ^ 2 - ((2 * (h * (2 * N)) : ℕ) : ℝ) - ((2 * h : ℕ) : ℝ)
      ≤ (monoCount 3 (2 * (h * (2 * N))) c : ℝ) := by
  set s := sg c with hs_def
  have hs : ∀ x, |s x| ≤ 1 := sg_abs c
  have hV := V_lower (2 * (h * (2 * N))) c
  have hW := W_lower s hs h N
  rw [← hs_def] at hV
  set w := 2 * N with hw
  set X := Xb s w with hX
  have hpre : pre s (2 * (h * w)) = ∑ p ∈ Icc 1 (2 * h), X p := by
    rw [tele_Xb, show 2 * h * w = 2 * (h * w) by ring]
  rw [hpre] at hV
  have hC8 := C8_expand (2 * h) X
  have hpen : ∑ p ∈ Icc 1 (2 * h), ((2 * (N : ℤ)) ^ 2 - X p ^ 2)
      = (2 * (h : ℤ)) * (2 * (N : ℤ)) ^ 2 - ∑ p ∈ Icc 1 (2 * h), X p ^ 2 := by
    rw [Finset.sum_sub_distrib]; simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    push_cast; ring
  rw [hpen] at hW
  set Z := ∑ p ∈ Icc 1 (2 * h), ∑ q ∈ Icc 1 (2 * h), C8 (2 * h) p q * X p * X q with hZ
  -- the integer inequality
  have hint : 2 * ((2 * (h * w) : ℕ) : ℤ) ^ 2 - 16 * ((2 * (h * w) : ℕ) : ℤ)
      - 8 * (2 * (h : ℤ)) * (2 * (N : ℤ)) ^ 2 - (2 * (h : ℤ)) * (8 * (2 * (N : ℤ)) + 32) + Z
      ≤ 32 * (monoCount 3 (2 * (h * w)) c : ℤ) := by
    rw [hC8]; linarith [hV, hW]
  -- the real part
  have hwpos : 0 < w := by omega
  have hcube := hσ (fun p => (X p : ℝ) / w) (by
    intro p hp
    have hp1 : 1 ≤ p := (Finset.mem_Icc.mp hp).1
    have hx := Xb_abs s hs w p hp1
    rw [abs_div, abs_of_pos (by exact_mod_cast hwpos : (0 : ℝ) < w), div_le_one (by exact_mod_cast hwpos)]
    exact_mod_cast hx)
  rw [cform_scale (2 * h) w hwpos X, ← hZ] at hcube
  have hw8 : (0 : ℝ) < 8 * (w : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hw8] at hcube
  have hintR : (2 * ((2 * (h * w) : ℕ) : ℤ) ^ 2 - 16 * ((2 * (h * w) : ℕ) : ℤ)
      - 8 * (2 * (h : ℤ)) * (2 * (N : ℤ)) ^ 2 - (2 * (h : ℤ)) * (8 * (2 * (N : ℤ)) + 32) + Z : ℤ)
      ≤ ((32 * (monoCount 3 (2 * (h * w)) c : ℤ) : ℤ) : ℝ) := by exact_mod_cast hint
  push_cast at hintR
  have hwR : (w : ℝ) = 2 * (N : ℝ) := by rw [hw]; push_cast; ring
  rw [hwR] at hcube
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold bound2
  push_cast
  rw [hwR] at hintR ⊢
  have hL : (2 * (h : ℝ)) ≠ 0 := by positivity
  have key : (1 / 16 - (2 * (h : ℝ) + (σ : ℝ)) / (4 * (2 * (h : ℝ)) ^ 2)) * (2 * ((h : ℝ) * (2 * (N : ℝ)))) ^ 2
      = (h : ℝ) ^ 2 * (N : ℝ) ^ 2 - 2 * (h : ℝ) * (N : ℝ) ^ 2 - (σ : ℝ) * (N : ℝ) ^ 2 := by
    field_simp; ring
  rw [key]
  nlinarith [hintR, hcube, mul_nonneg (by linarith : (0 : ℝ) ≤ h) (by linarith : (0 : ℝ) ≤ N)]

/-! ## From the finite inequality to the `liminf` -/

/-- For `b = bound2 ≥ 0`, every `n` satisfies `b n² - (8 b h + 1) n - 2h ≤ minMonoCount 3 n`. -/
lemma key_bound2 (h : ℕ) (hh : 1 ≤ h) (σ : ℚ) (hσ : CubeLB (2 * h) σ) (hb : 0 ≤ bound2 (2 * h) σ) (n : ℕ) :
    bound2 (2 * h) σ * (n : ℝ) ^ 2 - (8 * bound2 (2 * h) σ * h + 1) * n - 2 * h ≤ (minMonoCount 3 n : ℝ) := by
  set b := bound2 (2 * h) σ with hbdef
  have hM : 0 < 4 * h := by omega
  set m := n / (4 * h) with hm
  have hdm : 4 * h * m + n % (4 * h) = n := Nat.div_add_mod n (4 * h)
  have hml := Nat.mod_lt n hM
  have hn0 : (0 : ℝ) ≤ (minMonoCount 3 n : ℝ) := by positivity
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hh0 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  by_cases hm0 : m = 0
  · have hnL : n < 4 * h := by rw [hm0, mul_zero, zero_add] at hdm; omega
    have hnLR : (n : ℝ) < 4 * h := by exact_mod_cast hnL
    nlinarith [mul_nonneg (mul_nonneg hb hnn) (by linarith : (0 : ℝ) ≤ 8 * h - n)]
  · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
    set q := 2 * (h * (2 * m)) with hq
    have hq' : q = 4 * h * m := by rw [hq]; ring
    have hq1 : q ≤ n := by omega
    have hq2 : n < q + 4 * h := by omega
    obtain ⟨c, hc⟩ := exists_min_colouring 3 q
    have hmain := finite_bound2 h m hh hm1 σ hσ c
    rw [← hq, hc] at hmain
    have hmono : (minMonoCount 3 q : ℝ) ≤ minMonoCount 3 n := by
      exact_mod_cast minMono_mono 3 hq1
    have hq1R : (q : ℝ) ≤ n := by exact_mod_cast hq1
    have hq2R : (n : ℝ) < q + 4 * h := by exact_mod_cast hq2
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hL : (((2 * h : ℕ)) : ℝ) = 2 * h := by push_cast; ring
    rw [hL] at hmain
    have hq4 : 4 * h ≤ q := by rw [hq']; exact Nat.le_mul_of_pos_right _ hm1
    by_cases hnL : n < 4 * h
    · omega
    · have hnLR : (4 * h : ℝ) ≤ n := by exact_mod_cast (not_lt.mp hnL)
      have h1 : ((n : ℝ) - 4 * h) ^ 2 ≤ (q : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h2 := mul_le_mul_of_nonneg_left h1 hb
      nlinarith [h2, hmain, hmono, hq1R, mul_nonneg hb (sq_nonneg (h : ℝ))]

/-- **The MODEL2 reduction.**  For every even `L ≥ 4` and every `σ` with `xᵀ C x ≥ -σ` on the cube `[-1,1]^L`,
`bound2 L σ = 1/16 - (L + σ)/(4L²) ≤ δ 3`. -/
theorem lower_of_cubeLB (L : ℕ) (hL : 4 ≤ L) (hev : Even L) (σ : ℚ)
    (h : CubeLB L σ) : bound2 L σ ≤ δ 3 := by
  obtain ⟨h0, rfl⟩ : ∃ h0, L = 2 * h0 := by
    obtain ⟨r, hr⟩ := hev; exact ⟨r, by omega⟩
  have hh1 : 1 ≤ h0 := by omega
  rcases le_or_gt (bound2 (2 * h0) σ) 0 with hb0 | hb0
  · have : 0 ≤ δ 3 :=
      le_delta_of_eventually 3 0 (Filter.Eventually.of_forall (fun n => by
        simpa using quot_nonneg 3 n))
    linarith
  · have hb : 0 ≤ bound2 (2 * h0) σ := hb0.le
    set b := bound2 (2 * h0) σ with hbdef
    apply le_of_forall_pos_le_add
    intro ε hε
    set K := 8 * b * h0 + 1 + 2 * h0 with hKdef
    have hK : 0 < K := by positivity
    have hev : ∀ᶠ n : ℕ in atTop, b - ε ≤ (minMonoCount 3 n : ℝ) / (n : ℝ) ^ 2 := by
      rw [Filter.eventually_atTop]
      refine ⟨⌈K / ε⌉₊ + 1, fun n hn => ?_⟩
      have hnpos' : 0 < n := by omega
      have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hnpos'
      have hKn : K ≤ ε * n := by
        have h1 := Nat.le_ceil (K / ε)
        have h2 : (⌈K / ε⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈K / ε⌉₊ ≤ n)
        have h3 : K / ε ≤ n := h1.trans h2
        rwa [div_le_iff₀ hε, mul_comm] at h3
      rw [le_div_iff₀ (by positivity)]
      have := key_bound2 h0 hh1 σ h hb n
      have hh0 : (0 : ℝ) ≤ h0 := Nat.cast_nonneg h0
      nlinarith
    have := le_delta_of_eventually 3 (b - ε) hev
    linarith

/-- Gluing form for lane `lean1186d`'s `cubeLB64 : CubeLB 64 (183671 / 2048)`:
`1782409/33554432 = 0.0531199... ≤ δ 3`. -/
theorem lower_of_cubeLB64 (h : CubeLB 64 (183671 / 2048)) : (1782409 / 33554432 : ℝ) ≤ δ 3 := by
  have hb := lower_of_cubeLB 64 (by norm_num) (by decide) _ h
  have e : bound2 64 (183671 / 2048) = 1782409 / 33554432 := by unfold bound2; push_cast; norm_num
  rwa [e] at hb

/-- Gluing form for `cubeLB128 : CubeLB 128 (242779 / 512)`: `1788837/33554432 = 0.0533114... ≤ δ 3`. -/
theorem lower_of_cubeLB128 (h : CubeLB 128 (242779 / 512)) : (1788837 / 33554432 : ℝ) ≤ δ 3 := by
  have hb := lower_of_cubeLB 128 (by norm_num) (by decide) _ h
  have e : bound2 128 (242779 / 512) = 1788837 / 33554432 := by unfold bound2; push_cast; norm_num
  rwa [e] at hb

/-- Gluing form for the stretch certificate `CubeLB 256 (2190937 / 1024)`: `14324135/268435456 = 0.0533615... ≤ δ 3`. -/
theorem lower_of_cubeLB256 (h : CubeLB 256 (2190937 / 1024)) : (14324135 / 268435456 : ℝ) ≤ δ 3 := by
  have hb := lower_of_cubeLB 256 (by norm_num) (by decide) _ h
  have e : bound2 256 (2190937 / 1024) = 14324135 / 268435456 := by unfold bound2; push_cast; norm_num
  rwa [e] at hb

end Erdos1186Night2M2

#print axioms Erdos1186Night2M2.lower_of_cubeLB
#print axioms Erdos1186Night2M2.finite_bound2
#print axioms Erdos1186Night2M2.lower_of_cubeLB64
#print axioms Erdos1186Night2M2.lower_of_cubeLB128
#print axioms Erdos1186Night2M2.lower_of_cubeLB256
