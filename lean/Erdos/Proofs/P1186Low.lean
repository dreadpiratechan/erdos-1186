import Erdos.Proofs.P1186
import Erdos.Proofs.P1186Prs
import Erdos.Proofs.P1186LowA

/-!
# Erdos 1186 - the lower-bound reduction of Parrilo-Robertson-Saracino (2008), for every even `L`

Main theorem (night 2, lane `lean1186a`):

```
theorem Erdos1186Night2.lower_of_cert (L : ℕ) (hL : 2 ≤ L) (hev : Even L) (d : ℕ → ℚ)
    (h : DiagCert L d) : prsBound L d ≤ Erdos1186Day.δ 3
```

where `DiagCert`, `prsBound` are the definitions of `P1186Prs.lean` (PRS08, J. Combin. Theory Ser. A 115 (2008)
185-192, Section 3) and `δ` is the verbatim upstream definition of `P1186.lean`.  So any diagonal PSD certificate
`A_L + diag d ⪰ 0, d ≥ 0` gives `δ 3 ≥ ½ (3/8 - 1/(4L) - 1/4 - (Σ d)/(4L²))`.

**Finite form** (`finite_bound`): for `L = 2h`, `n = L m` and EVERY colouring `c`,
`monoCount 3 n c ≥ prsBound L d · n² - n/2`.

**Proof (own derivation, ±1 form of PRS08 Sections 2-3; no Fourier analysis).**  Write `s = ±1` for the colouring.
For a 3-AP `(y-d, y, y+d)`, `4 [monochromatic] = 1 + s_{y-d}s_y + s_y s_{y+d} + s_{y-d}s_{y+d}` (`mono_ind`), and the
APs are indexed by midpoint `y` and `1 ≤ d ≤ min (y-1) (n-y)` (`four_mono`).  Summing,
`4 V = A + (W - n) + R` with `A = #APs`, `W = Σ_y s_y Σ_{|x - y| ≤ D_y} s_x` and `R = Σ_{x<z, x≡z (2)} s_x s_z`
(`mid_expand`).  Now `R ≥ -n/2` and `4 A ≥ n² - 2n` since `n + 2R = E² + O²` (`mid_sum`; applied to `s` and to `s ≡ 1`).
For `W`, split `[1, n]` into `L` blocks of length `m`; strip `i` (the `y` of block `i`) sees the window
`[y - D_y, y + D_y]`, which differs from PRS's cell union (`Bprs L i j = 1` cells) by at most `|2β - 1 - m|`
positions (`T_err`), so `W ≥ Σ_i X_i C_i - L Σ_β |2β-1-m| ≥ Σ_i X_i C_i - L m²/2` (`Wm_lower`, `gsum_le`).
Finally `2 Σ_i X_i C_i = X^T A X ≥ -Σ d_i X_i² ≥ -m² Σ d` from the certificate (`cert_apply`, `|X_i| ≤ m`).
Everything combines to `16 V ≥ n² - 8n - 2 m² Σ d - 2 L m²` (`main_ineq`), i.e. `V ≥ prsBound · n² - n/2`.
The passage to `δ` uses monotonicity of `n ↦ minMonoCount 3 n` (`minMono_mono`) and an `ε`-argument
(`key_bound`, `lower_of_cert`).  Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

open Finset Filter

namespace Erdos1186Night2

open Erdos1186Day

/-- The `±1` sign of a colouring. -/
def sg (c : ℕ → Bool) (x : ℕ) : ℤ := if c x then 1 else -1

lemma sg_abs (c : ℕ → Bool) (x : ℕ) : |sg c x| ≤ 1 := by
  unfold sg; split_ifs <;> simp

lemma sg_sq (c : ℕ → Bool) (x : ℕ) : sg c x * sg c x = 1 := by
  unfold sg; split_ifs <;> simp

/-- Pointwise: `4 [mono] = 1 + s_a s_b + s_b s_e + s_a s_e`. -/
lemma mono_ind (c : ℕ → Bool) (a d : ℕ) :
    (4 : ℤ) * (if (∀ i : ℕ, i < 3 → c (a + i * d) = c a) then (1 : ℤ) else 0)
      = 1 + sg c a * sg c (a + d) + sg c (a + d) * sg c (a + 2 * d) + sg c a * sg c (a + 2 * d) := by
  have hiff : (∀ i : ℕ, i < 3 → c (a + i * d) = c a) ↔ (c (a + d) = c a ∧ c (a + 2 * d) = c a) := by
    constructor
    · intro h
      have h1 := h 1 (by norm_num)
      have h2 := h 2 (by norm_num)
      simp only [one_mul] at h1
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩ i hi
      interval_cases i
      · simp
      · simpa using h1
      · exact h2
  rw [if_congr hiff rfl rfl]
  unfold sg
  cases h1 : c a <;> cases h2 : c (a + d) <;> cases h3 : c (a + 2 * d) <;> simp

lemma four_mono (n : ℕ) (c : ℕ → Bool) :
    (4 : ℤ) * (monoCount 3 n c : ℤ) = ∑ y ∈ Icc 1 n, ∑ d ∈ Icc 1 (Dm n y),
      (1 + sg c (y - d) * sg c y + sg c y * sg c (y + d) + sg c (y - d) * sg c (y + d)) := by
  rw [monoCount_eq, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  simp only [mono_ind]
  rw [← Finset.sum_sigma (Icc 1 n) (fun y => Icc 1 (Dm n y))
    (fun q => 1 + sg c (q.1 - q.2) * sg c q.1 + sg c q.1 * sg c (q.1 + q.2)
      + sg c (q.1 - q.2) * sg c (q.1 + q.2))]
  apply Finset.sum_nbij' (fun p => (⟨p.1 + p.2, p.2⟩ : Σ _ : ℕ, ℕ))
    (fun q => (q.1 - q.2, q.2))
  · rintro ⟨a, d⟩ hp
    simp only [aps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_sigma,
      Dm, Nat.reduceSub] at hp ⊢
    omega
  · rintro ⟨y, d⟩ hq
    simp only [aps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_sigma,
      Dm, Nat.reduceSub] at hq ⊢
    omega
  · rintro ⟨a, d⟩ hp
    simp
  · rintro ⟨y, d⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Dm] at hq
    have e : y - d + d = y := by omega
    simp [e]
  · rintro ⟨a, d⟩ hp
    simp only [aps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Nat.reduceSub] at hp
    have e1 : a + d - d = a := by omega
    have e2 : a + d + d = a + 2 * d := by ring
    simp only [e1, e2]


/-- The finite inequality: for `L = 2h` and `n = L m`, every colouring has at least
`prsBound L d * n^2 - n / 2` monochromatic 3-APs. -/
theorem main_ineq (h m : ℕ) (hh1 : 1 ≤ h) (d : ℕ → ℚ) (hd : DiagCert (2 * h) d) (c : ℕ → Bool) :
    prsBound (2 * h) d * ((2 * (h * m) : ℕ) : ℝ) ^ 2 - ((2 * (h * m) : ℕ) : ℝ) / 2
      ≤ (monoCount 3 (2 * (h * m)) c : ℝ) := by
  set n := 2 * (h * m) with hn
  set s := sg c with hs_def
  have hs : ∀ x, |s x| ≤ 1 := sg_abs c
  have hs2 : ∀ x, s x * s x = 1 := sg_sq c
  have h4 := four_mono n c
  rw [mid_expand s n] at h4
  have hA : ∑ y ∈ Icc 1 n, ∑ _d ∈ Icc 1 (Dm n y), (1 : ℤ) = Rm (fun _ => (1 : ℤ)) n := by
    unfold Rm; simp
  have hsum : ∑ y ∈ Icc 1 n, s y * s y = n := by
    rw [Finset.sum_congr rfl (fun y _ => hs2 y)]; simp
  have h5 := Rm_one n
  have h6 := Rm_nonneg s n
  rw [hsum] at h6 h4
  rw [← hA] at h5
  have h7 := Wm_lower s hs h m
  have h8 := gsum_le m
  have h9 := cert_apply (2 * h) m d hd s hs
  have hhz : (0 : ℤ) ≤ (h : ℤ) := by positivity
  have h10 : (h : ℤ) * (2 * gsum m) ≤ h * (m : ℤ) ^ 2 := mul_le_mul_of_nonneg_left h8 hhz
  generalize (∑ i ∈ Icc 1 (2 * h), Xb s m i * Cb s (2 * h) m i) = XC at h7 h9
  have hZ : (n : ℤ) ^ 2 - 8 * n + 4 * XC - 4 * h * (m : ℤ) ^ 2 ≤ 16 * (monoCount 3 n c : ℤ) := by
    push_cast at h7
    nlinarith
  have hZR : ((n : ℤ) : ℝ) ^ 2 - 8 * ((n : ℤ) : ℝ) + 4 * (XC : ℝ) - 4 * (h : ℝ) * (m : ℝ) ^ 2
      ≤ 16 * (monoCount 3 n c : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this ⊢
    exact this
  have hhR : (h : ℝ) ≠ 0 := by positivity
  generalize hSd : (∑ i ∈ Icc 1 (2 * h), (d i : ℝ)) = Sd at h9
  have hP : prsBound (2 * h) d * ((n : ℕ) : ℝ) ^ 2 = (h : ℝ) ^ 2 * (m : ℝ) ^ 2 / 4
      - (h : ℝ) * (m : ℝ) ^ 2 / 4 - (m : ℝ) ^ 2 * Sd / 8 := by
    unfold prsBound
    rw [hSd, hn]
    push_cast
    field_simp
    ring
  have hnR : ((n : ℕ) : ℝ) = 2 * ((h : ℝ) * (m : ℝ)) := by rw [hn]; push_cast; ring
  rw [hP, hnR]
  push_cast at hZR
  rw [hnR] at hZR
  nlinarith [hZR, h9]


/-! ## From the finite inequality to the `liminf` -/

lemma monoCount_succ_le (k n : ℕ) (c : ℕ → Bool) : monoCount k n c ≤ monoCount k (n + 1) c := by
  unfold monoCount
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
  obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5, h6⟩ := hp
  exact ⟨⟨⟨h1, by omega⟩, ⟨h3, by omega⟩⟩, by omega, h6⟩

lemma minMono_succ (k n : ℕ) : minMonoCount k n ≤ minMonoCount k (n + 1) := by
  obtain ⟨c, hc⟩ := exists_min_colouring k (n + 1)
  rw [← hc]
  exact (minMonoCount_le k n c).trans (monoCount_succ_le k n c)

lemma minMono_mono (k : ℕ) : Monotone (minMonoCount k) :=
  monotone_nat_of_le_succ (minMono_succ k)

/-- For `b ≥ 0` (a bound valid along `n = L m`), every `n` satisfies `b n² - (2 b L + 1/2) n ≤ min`. -/
lemma key_bound (h0 : ℕ) (hh1 : 1 ≤ h0) (d : ℕ → ℚ) (hd : DiagCert (2 * h0) d)
    (hb : 0 ≤ prsBound (2 * h0) d) (n : ℕ) :
    prsBound (2 * h0) d * (n : ℝ) ^ 2 - (2 * prsBound (2 * h0) d * ((2 * h0 : ℕ) : ℝ) + 1 / 2) * n
      ≤ (minMonoCount 3 n : ℝ) := by
  set b := prsBound (2 * h0) d with hbdef
  have hLpos : 0 < 2 * h0 := by omega
  set m := n / (2 * h0) with hm
  set q := 2 * (h0 * m) with hq
  have hdm : 2 * h0 * m + n % (2 * h0) = n := Nat.div_add_mod n (2 * h0)
  have hml := Nat.mod_lt n hLpos
  have hq' : q = 2 * h0 * m := by rw [hq]; ring
  have hq1 : q ≤ n := by omega
  have hq2 : n < q + 2 * h0 := by omega
  obtain ⟨c, hc⟩ := exists_min_colouring 3 q
  have hmain := main_ineq h0 m hh1 d hd c
  rw [hc] at hmain
  have hmono : (minMonoCount 3 q : ℝ) ≤ minMonoCount 3 n := by
    exact_mod_cast minMono_mono 3 hq1
  have hq1R : (q : ℝ) ≤ n := by exact_mod_cast hq1
  have hq2R : (n : ℝ) < q + 2 * h0 := by exact_mod_cast hq2
  have hn0 : (0 : ℝ) ≤ (minMonoCount 3 n : ℝ) := by positivity
  have hL : (((2 * h0 : ℕ)) : ℝ) = 2 * h0 := by push_cast; ring
  rw [hL]
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hnL : n < 2 * h0
  · have hnLR : (n : ℝ) < 2 * h0 := by exact_mod_cast hnL
    have hh0 : (0 : ℝ) ≤ h0 := Nat.cast_nonneg h0
    nlinarith [mul_nonneg (mul_nonneg hb hnn) (by linarith : (0 : ℝ) ≤ 4 * h0 - n)]
  · have hnLR : (2 * h0 : ℝ) ≤ n := by exact_mod_cast (not_lt.mp hnL)
    have h1 : ((n : ℝ) - 2 * h0) ^ 2 ≤ (q : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 := mul_le_mul_of_nonneg_left h1 hb
    have h3 : 0 ≤ b * (2 * (h0 : ℝ)) ^ 2 := by positivity
    nlinarith

/-- **The reduction.**  For every even `L ≥ 2` and every diagonal certificate `d` of PRS08
(`d ≥ 0` and `A_L + diag d ⪰ 0`), `prsBound L d ≤ δ 3`. -/
theorem lower_of_cert (L : ℕ) (hL : 2 ≤ L) (hev : Even L) (d : ℕ → ℚ)
    (h : DiagCert L d) : prsBound L d ≤ δ 3 := by
  obtain ⟨h0, rfl⟩ : ∃ h0, L = 2 * h0 := by
    obtain ⟨r, hr⟩ := hev; exact ⟨r, by omega⟩
  have hh1 : 1 ≤ h0 := by omega
  rcases le_or_gt (prsBound (2 * h0) d) 0 with hb0 | hb0
  · have : 0 ≤ δ 3 :=
      le_delta_of_eventually 3 0 (Filter.Eventually.of_forall (fun n => by
        simpa using quot_nonneg 3 n))
    linarith
  · have hb : 0 ≤ prsBound (2 * h0) d := hb0.le
    set b := prsBound (2 * h0) d with hbdef
    apply le_of_forall_pos_le_add
    intro ε hε
    set K := 2 * b * ((2 * h0 : ℕ) : ℝ) + 1 / 2 with hKdef
    have hK : 0 < K := by positivity
    have hev : ∀ᶠ n : ℕ in atTop, b - ε ≤ (minMonoCount 3 n : ℝ) / (n : ℝ) ^ 2 := by
      rw [Filter.eventually_atTop]
      refine ⟨⌈K / ε⌉₊ + 1, fun n hn => ?_⟩
      have hnpos' : 0 < n := by omega
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hnpos'
      have hKn : K ≤ ε * n := by
        have h1 := Nat.le_ceil (K / ε)
        have h2 : (⌈K / ε⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈K / ε⌉₊ ≤ n)
        have h3 : K / ε ≤ n := h1.trans h2
        rwa [div_le_iff₀ hε, mul_comm] at h3
      rw [le_div_iff₀ (by positivity)]
      have := key_bound h0 hh1 d h hb n
      nlinarith
    have := le_delta_of_eventually 3 (b - ε) hev
    linarith


/-- Finite form of the PRS08 bound for every even `L` and every colouring (`n = L m`). -/
theorem finite_bound (L m : ℕ) (hL : 2 ≤ L) (hev : Even L) (d : ℕ → ℚ) (hd : DiagCert L d)
    (c : ℕ → Bool) :
    prsBound L d * ((L * m : ℕ) : ℝ) ^ 2 - ((L * m : ℕ) : ℝ) / 2
      ≤ (monoCount 3 (L * m) c : ℝ) := by
  obtain ⟨h0, rfl⟩ : ∃ h0, L = 2 * h0 := by
    obtain ⟨r, hr⟩ := hev; exact ⟨r, by omega⟩
  have e : 2 * h0 * m = 2 * (h0 * m) := by ring
  rw [e]
  exact main_ineq h0 m (by omega) d hd c

/-- Convenience form for gluing: only `Σ d` matters. -/
theorem lower_of_cert_of_sum (L : ℕ) (hL : 2 ≤ L) (hev : Even L) (d : ℕ → ℚ) (h : DiagCert L d)
    (s : ℚ) (hs : ∑ i ∈ Icc 1 L, d i = s) (b : ℝ)
    (hb : b ≤ (1 / 2 : ℝ) * (3 / 8 - (1 / (4 * (L : ℝ)) + 1 / 4 + (s : ℝ) / (4 * (L : ℝ) ^ 2)))) :
    b ≤ δ 3 := by
  rw [← prsBound_of_sum L d s hs] at hb
  exact hb.trans (lower_of_cert L hL hev d h)

/-- The published bound `1675/32768 ≤ δ 3` from ANY `L = 128` diagonal certificate with `Σ d = 697849/512`
(lane `lean1186b` supplies `DiagCert 128 d128` and the sum; `3430919/67108864 ≥ 1675/32768`). -/
theorem lower_of_cert128 (d : ℕ → ℚ) (h : DiagCert 128 d) (hs : ∑ i ∈ Icc 1 128, d i = 697849 / 512) :
    (1675 / 32768 : ℝ) ≤ δ 3 :=
  lower_of_cert_of_sum 128 (by norm_num) (by decide) d h (697849 / 512) hs (1675 / 32768) (by norm_num)

end Erdos1186Night2

#print axioms Erdos1186Night2.lower_of_cert
#print axioms Erdos1186Night2.finite_bound
#print axioms Erdos1186Night2.lower_of_cert_of_sum
#print axioms Erdos1186Night2.lower_of_cert128
