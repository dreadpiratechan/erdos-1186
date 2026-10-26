import Mathlib

/-!
# Erdos 1186 - bathtub library for `BathOK` (generic lemmas, no numbers)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's.  This module holds the number-free tools for Lemma 2 (the bathtub inequality): a discrete layer-cake lemma, an
arithmetic-progression counting lemma, and an interpolation lemma for the piecewise-linear level-count function.
-/

namespace Erdos1186Ex

open Finset

/-- Discrete bathtub (layer cake): if `#{x ∈ I : g x < t} ≤ ρ t + κ` for all `t ≥ 0` and `g ≥ 0` on `I`, then every
`S ⊆ I` has `∑_S g ≥ (|S| - κ)₊² / (2ρ)`. -/
theorem bathtub {ι : Type*} [DecidableEq ι] (I : Finset ι) (g : ι → ℝ) (hg : ∀ x ∈ I, 0 ≤ g x)
    (ρ κ : ℝ) (hρ : 0 < ρ) (hκ : 0 ≤ κ)
    (hcount : ∀ t : ℝ, 0 ≤ t → ((I.filter fun x => g x < t).card : ℝ) ≤ ρ * t + κ) :
    ∀ S : Finset ι, S ⊆ I → (max ((S.card : ℝ) - κ) 0) ^ 2 / (2 * ρ) ≤ ∑ x ∈ S, g x := by
  intro S
  induction' hk : S.card with k ih generalizing S
  · intro _
    have hS : S = ∅ := Finset.card_eq_zero.mp hk
    subst hS
    simp only [Nat.cast_zero, zero_sub, Finset.sum_empty]
    have : max (-κ) 0 = 0 := max_eq_right (by linarith)
    rw [this]; simp
  · intro hSI
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, hk]; exact Nat.succ_pos k
    obtain ⟨xs, hxs, hmax⟩ := Finset.exists_max_image S g hne
    have hcard' : (S.erase xs).card = k := by
      rw [Finset.card_erase_of_mem hxs, hk]; rfl
    have hsub' : S.erase xs ⊆ I := (Finset.erase_subset _ _).trans hSI
    have ih' := ih (S.erase xs) hcard' hsub'
    have hgx : 0 ≤ g xs := hg xs (hSI hxs)
    -- ρ g(xs) + κ ≥ k + 1
    have hlow : ((k + 1 : ℕ) : ℝ) ≤ ρ * g xs + κ := by
      by_contra hcon
      push_neg at hcon
      set η : ℝ := (((k + 1 : ℕ) : ℝ) - (ρ * g xs + κ)) / (2 * ρ) with hη
      have hηpos : 0 < η := by
        rw [hη]; apply div_pos; linarith; linarith
      have ht0 : 0 ≤ g xs + η := by linarith
      have hc := hcount (g xs + η) ht0
      have hsubf : S ⊆ I.filter fun x => g x < g xs + η := by
        intro x hx
        rw [Finset.mem_filter]
        exact ⟨hSI hx, by have := hmax x hx; linarith⟩
      have h1 : ((S.card : ℕ) : ℝ) ≤ ((I.filter fun x => g x < g xs + η).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubf
      rw [hk] at h1
      have h2 : ρ * (g xs + η) + κ < ((k + 1 : ℕ) : ℝ) := by
        have : ρ * η = (((k + 1 : ℕ) : ℝ) - (ρ * g xs + κ)) / 2 := by
          rw [hη]; field_simp
        nlinarith
      linarith
    rw [← Finset.add_sum_erase S g hxs]
    set A := max (((k + 1 : ℕ) : ℝ) - κ) 0 with hA
    set B := max ((k : ℝ) - κ) 0 with hB
    have hAle : A ≤ ρ * g xs := by
      rw [hA]; apply max_le; linarith; positivity
    have hAB : A ^ 2 ≤ B ^ 2 + 2 * A := by
      rcases le_total ((k : ℝ) - κ) 0 with h | h
      · have hB0 : B = 0 := by rw [hB]; exact max_eq_right h
        rw [hB0]
        rcases le_total ((k : ℝ) + 1 - κ) 0 with h' | h'
        · have : A = 0 := by rw [hA]; push_cast; exact max_eq_right h'
          rw [this]; norm_num
        · have : A = (k : ℝ) + 1 - κ := by rw [hA]; push_cast; exact max_eq_left h'
          rw [this]; nlinarith
      · have hB' : B = (k : ℝ) - κ := by rw [hB]; exact max_eq_left h
        have hA' : A = (k : ℝ) + 1 - κ := by rw [hA]; push_cast; exact max_eq_left (by linarith)
        rw [hB', hA']; nlinarith
    have hfin : A ^ 2 / (2 * ρ) ≤ B ^ 2 / (2 * ρ) + g xs := by
      have h3 : A ^ 2 / (2 * ρ) ≤ (B ^ 2 + 2 * A) / (2 * ρ) :=
        div_le_div_of_nonneg_right hAB (by positivity)
      have h4 : (B ^ 2 + 2 * A) / (2 * ρ) = B ^ 2 / (2 * ρ) + A / ρ := by field_simp
      have h5 : A / ρ ≤ g xs := by rw [div_le_iff₀ hρ]; linarith
      linarith
    linarith

/-- Counting the points of an arithmetic progression `j ↦ u j` (`|u j - u j'| = s |j - j'|`) in a window `[lo, hi)`. -/
theorem card_ap_le (w : ℕ) (u : ℕ → ℝ) (s lo hi : ℝ) (hs : 0 < s)
    (hu : ∀ j j', |u j - u j'| = s * |(j : ℝ) - j'|) :
    (((Icc 1 w).filter (fun j => lo ≤ u j ∧ u j < hi)).card : ℝ) ≤ max 0 ((hi - lo) / s) + 1 := by
  set T := (Icc 1 w).filter (fun j => lo ≤ u j ∧ u j < hi) with hT
  rcases T.eq_empty_or_nonempty with h | h
  · rw [h]; simp only [Finset.card_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ max 0 ((hi - lo) / s) := le_max_left _ _
    linarith
  · have ha := T.min'_mem h
    have hb := T.max'_mem h
    set a := T.min' h with ha_def
    set b := T.max' h with hb_def
    have hab : a ≤ b := T.min'_le _ hb
    have hsub : T ⊆ Icc a b := fun x hx => mem_Icc.2 ⟨T.min'_le x hx, T.le_max' x hx⟩
    have hcard : T.card ≤ b + 1 - a := by
      have := Finset.card_le_card hsub
      simpa using this
    have hcardR : (T.card : ℝ) ≤ (b : ℝ) + 1 - a := by
      have : ((b + 1 - a : ℕ) : ℝ) = (b : ℝ) + 1 - a := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← this]; exact_mod_cast hcard
    have hmb := (Finset.mem_filter.mp hb).2
    have hma := (Finset.mem_filter.mp ha).2
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hd : s * ((b : ℝ) - a) = |u b - u a| := by
      rw [hu b a, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b : ℝ) - a)]
    have hlt : |u b - u a| < hi - lo := by
      rw [abs_lt]; constructor <;> linarith [hmb.1, hmb.2, hma.1, hma.2]
    have hpos : 0 < hi - lo := by
      have := abs_nonneg (u b - u a); linarith
    have : ((b : ℝ) - a) < (hi - lo) / s := by
      rw [lt_div_iff₀ hs]; linarith
    have h2 : (hi - lo) / s ≤ max 0 ((hi - lo) / s) := le_max_right _ _
    linarith

/-- The clamp `min 1 (max 0 ((z - d) / s))`. -/
noncomputable def ramp (d s z : ℝ) : ℝ := min 1 (max 0 ((z - d) / s))

/-- `ramp` with integer break-points is affine between consecutive integers. -/
theorem ramp_interp (d s : ℤ) (hs : 0 < s) (c : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ramp d s ((c : ℝ) + θ) = (1 - θ) * ramp d s (c : ℝ) + θ * ramp d s ((c : ℝ) + 1) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  unfold ramp
  by_cases ha : (c : ℤ) + 1 ≤ d
  · have haR : (c : ℝ) + 1 ≤ d := by exact_mod_cast ha
    have e1 : max 0 (((c : ℝ) + θ - d) / s) = 0 := by
      apply max_eq_left; apply div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le
    have e2 : max 0 (((c : ℝ) - d) / s) = 0 := by
      apply max_eq_left; apply div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le
    have e3 : max 0 (((c : ℝ) + 1 - d) / s) = 0 := by
      apply max_eq_left; apply div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le
    rw [e1, e2, e3]; simp
  · by_cases hb : d + s ≤ (c : ℤ)
    · have hbR : (d : ℝ) + s ≤ c := by exact_mod_cast hb
      have e1 : min 1 (max 0 (((c : ℝ) + θ - d) / s)) = 1 := by
        apply min_eq_left
        apply le_max_of_le_right
        rw [le_div_iff₀ hsR]; linarith
      have e2 : min 1 (max 0 (((c : ℝ) - d) / s)) = 1 := by
        apply min_eq_left
        apply le_max_of_le_right
        rw [le_div_iff₀ hsR]; linarith
      have e3 : min 1 (max 0 (((c : ℝ) + 1 - d) / s)) = 1 := by
        apply min_eq_left
        apply le_max_of_le_right
        rw [le_div_iff₀ hsR]; linarith
      rw [e1, e2, e3]; ring
    · have hd : d ≤ (c : ℤ) := by omega
      have hcs : (c : ℤ) + 1 ≤ d + s := by omega
      have hdR : (d : ℝ) ≤ c := by exact_mod_cast hd
      have hcsR : (c : ℝ) + 1 ≤ d + s := by exact_mod_cast hcs
      have key : ∀ z : ℝ, (c : ℝ) ≤ z → z ≤ (c : ℝ) + 1 →
          min 1 (max 0 ((z - d) / s)) = (z - d) / s := by
        intro z hz1 hz2
        have hnn : 0 ≤ (z - d) / s := div_nonneg (by linarith) hsR.le
        have hle : (z - d) / s ≤ 1 := by rw [div_le_iff₀ hsR]; linarith
        rw [max_eq_right hnn, min_eq_right hle]
      rw [key _ (by linarith) (by linarith), key _ le_rfl (by linarith), key _ (by linarith) le_rfl]
      field_simp
      ring

/-- Level-count inequality between integers extends to all reals `τ ≥ 0`. -/
theorem ramp_sum_le {ι : Type*} (I : Finset ι) (d s : ι → ℤ) (hs : ∀ p ∈ I, 0 < s p) (ρ : ℝ)
    (h : ∀ c : ℕ, ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) ≤ ρ * c) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∑ p ∈ I, ramp (d p) (s p) τ ≤ ρ * τ := by
  set c := ⌊τ⌋₊ with hc
  set θ := τ - c with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; have := Nat.floor_le hτ; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; have := Nat.lt_floor_add_one τ; linarith
  have hτ' : τ = (c : ℝ) + θ := by rw [hθ]; ring
  have e : ∑ p ∈ I, ramp (d p) (s p) τ
      = (1 - θ) * ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) + θ * ∑ p ∈ I, ramp (d p) (s p) ((c : ℝ) + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hτ']; exact ramp_interp (d p) (s p) (hs p hp) c θ hθ0 hθ1
  rw [e]
  have h1 := h c
  have h2 := h (c + 1)
  push_cast at h2
  nlinarith

theorem ramp_nonneg (d s z : ℝ) : 0 ≤ ramp d s z := by
  unfold ramp; exact le_min zero_le_one (le_max_left _ _)

theorem ramp_le_one (d s z : ℝ) : ramp d s z ≤ 1 := by
  unfold ramp; exact min_le_left _ _

theorem ramp_zero_of (d s : ℤ) (hs : 0 < s) (hd : 0 ≤ d) : ramp d s 0 = 0 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
  unfold ramp
  have : max 0 (((0 : ℝ) - d) / s) = 0 :=
    max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le)
  rw [this]; norm_num

theorem ramp_one_of (d s : ℤ) (hs : 0 < s) (z : ℝ) (h : (d : ℝ) + s ≤ z) : ramp d s z = 1 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  unfold ramp
  apply min_eq_left
  apply le_max_of_le_right
  rw [le_div_iff₀ hsR]; linarith

/-- one step of the level-count function: it rises by `1/s` while the level is inside the ramp. -/
theorem ramp_succ (d s : ℤ) (hs : 0 < s) (c : ℕ) :
    ramp d s ((c : ℝ) + 1) = ramp d s (c : ℝ) + (if d ≤ (c : ℤ) ∧ (c : ℤ) < d + s then 1 / (s : ℝ) else 0) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  by_cases ha : (c : ℤ) + 1 ≤ d
  · have haR : (c : ℝ) + 1 ≤ d := by exact_mod_cast ha
    have e1 : ramp d s ((c : ℝ) + 1) = 0 := by
      unfold ramp
      have : max 0 ((((c : ℝ) + 1) - d) / s) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le)
      rw [this]; norm_num
    have e2 : ramp d s (c : ℝ) = 0 := by
      unfold ramp
      have : max 0 (((c : ℝ) - d) / s) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le)
      rw [this]; norm_num
    have e3 : ¬ (d ≤ (c : ℤ) ∧ (c : ℤ) < d + s) := by omega
    rw [e1, e2, if_neg e3]; ring
  · by_cases hb : d + s ≤ (c : ℤ)
    · have hbR : (d : ℝ) + s ≤ c := by exact_mod_cast hb
      rw [ramp_one_of d s hs _ (by linarith), ramp_one_of d s hs _ hbR]
      have e3 : ¬ (d ≤ (c : ℤ) ∧ (c : ℤ) < d + s) := by omega
      rw [if_neg e3]; ring
    · have hd : d ≤ (c : ℤ) := by omega
      have hcs : (c : ℤ) + 1 ≤ d + s := by omega
      have hdR : (d : ℝ) ≤ c := by exact_mod_cast hd
      have hcsR : (c : ℝ) + 1 ≤ d + s := by exact_mod_cast hcs
      have key : ∀ z : ℝ, (c : ℝ) ≤ z → z ≤ (c : ℝ) + 1 →
          ramp d s z = (z - d) / s := by
        intro z hz1 hz2
        unfold ramp
        have hnn : 0 ≤ (z - d) / s := div_nonneg (by linarith) hsR.le
        have hle : (z - d) / s ≤ 1 := by rw [div_le_iff₀ hsR]; linarith
        rw [max_eq_right hnn, min_eq_right hle]
      rw [key _ (by linarith) le_rfl, key _ le_rfl (by linarith), if_pos ⟨hd, by omega⟩]
      field_simp
      ring

/-- the slope bound at integer levels gives the level-count bound `∑ ramp ≤ ρ c` at every integer `c`. -/
theorem level_count {ι : Type*} (I : Finset ι) (d s : ι → ℤ) (hs : ∀ p ∈ I, 0 < s p) (hd : ∀ p ∈ I, 0 ≤ d p)
    (K : ℕ) (hK : ∀ p ∈ I, d p + s p ≤ (K : ℤ)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hinc : ∀ c : ℕ, c < K →
      ∑ p ∈ I, (if d p ≤ (c : ℤ) ∧ (c : ℤ) < d p + s p then 1 / (s p : ℝ) else 0) ≤ ρ) :
    ∀ c : ℕ, ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) ≤ ρ * c := by
  have step : ∀ c : ℕ, c ≤ K → ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) ≤ ρ * c := by
    intro c
    induction c with
    | zero =>
      intro _
      have : ∑ p ∈ I, ramp (d p) (s p) ((0 : ℕ) : ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        push_cast
        exact ramp_zero_of _ _ (hs p hp) (hd p hp)
      rw [this]; simp
    | succ c ih =>
      intro hc
      have h1 := ih (by omega)
      have h2 := hinc c (by omega)
      have e : ∑ p ∈ I, ramp (d p) (s p) (((c + 1 : ℕ)) : ℝ)
          = ∑ p ∈ I, ramp (d p) (s p) (c : ℝ)
            + ∑ p ∈ I, (if d p ≤ (c : ℤ) ∧ (c : ℤ) < d p + s p then 1 / (s p : ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        push_cast
        exact ramp_succ (d p) (s p) (hs p hp) c
      rw [e]; push_cast; nlinarith
  intro c
  by_cases hc : c ≤ K
  · exact step c hc
  · push_neg at hc
    have hall : ∀ c' : ℕ, K ≤ c' → ∑ p ∈ I, ramp (d p) (s p) (c' : ℝ) = (I.card : ℝ) := by
      intro c' hc'
      have : ∀ p ∈ I, ramp (d p) (s p) (c' : ℝ) = 1 := by
        intro p hp
        apply ramp_one_of _ _ (hs p hp)
        have h1 := hK p hp
        have h2 : ((d p + s p : ℤ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h1
        have h3 : (K : ℝ) ≤ c' := by exact_mod_cast hc'
        push_cast at h2
        linarith
      rw [Finset.sum_congr rfl this]; simp
    rw [hall c hc.le]
    have := step K le_rfl
    rw [hall K le_rfl] at this
    have hKc : (K : ℝ) ≤ c := by exact_mod_cast hc.le
    nlinarith

/-- number of points of an arithmetic progression below `t`, compared with the ramp. -/
theorem piece_count (w : ℕ) (hw : 1 ≤ w) (u : ℕ → ℝ) (d s : ℤ) (hs : 0 < s)
    (hu : ∀ j j', |u j - u j'| = (s : ℝ) * |(j : ℝ) - j'|)
    (hlo : ∀ j ∈ Icc 1 w, (d : ℝ) * w ≤ u j) (t : ℝ) :
    (((Icc 1 w).filter (fun j => u j < t)).card : ℝ) ≤ (w : ℝ) * ramp d s (t / w) + 1 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  set F := (Icc 1 w).filter (fun j => u j < t) with hF
  have h1 : (F.card : ℝ) ≤ w := by
    have : F.card ≤ (Icc 1 w).card := Finset.card_filter_le _ _
    have h' : F.card ≤ w := by simpa using this
    exact_mod_cast h'
  have h2 : (F.card : ℝ) ≤ max 0 ((t - d * w) / s) + 1 := by
    have hsub : F ⊆ (Icc 1 w).filter (fun j => (d : ℝ) * w ≤ u j ∧ u j < t) := by
      intro j hj
      rw [hF, Finset.mem_filter] at hj
      rw [Finset.mem_filter]
      exact ⟨hj.1, hlo j hj.1, hj.2⟩
    have hc : (F.card : ℝ) ≤ (((Icc 1 w).filter (fun j => (d : ℝ) * w ≤ u j ∧ u j < t)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have := card_ap_le w u (s : ℝ) ((d : ℝ) * w) t hsR hu
    linarith
  have hr0 : 0 ≤ ramp d s (t / w) := ramp_nonneg _ _ _
  have hY : ((t / w) - d) / s = ((t - d * w) / s) / w := by field_simp
  rcases le_or_gt ((t - d * w) / s) 0 with hY0 | hY0
  · have : max 0 ((t - d * w) / s) = 0 := max_eq_left hY0
    rw [this] at h2
    nlinarith
  · rw [max_eq_right hY0.le] at h2
    by_cases hYw : (t - d * w) / s ≤ w
    · have hr : ramp d s (t / w) = ((t - d * w) / s) / w := by
        unfold ramp
        rw [hY]
        have hnn : 0 ≤ ((t - d * w) / s) / w := div_nonneg hY0.le hwR.le
        have hle : ((t - d * w) / s) / w ≤ 1 := by rw [div_le_iff₀ hwR]; linarith
        rw [max_eq_right hnn, min_eq_right hle]
      rw [hr]
      have : (w : ℝ) * (((t - d * w) / s) / w) = (t - d * w) / s := by field_simp
      rw [this]; exact h2
    · push_neg at hYw
      have hr : ramp d s (t / w) = 1 := by
        unfold ramp
        rw [hY]
        have : 1 ≤ ((t - d * w) / s) / w := by rw [le_div_iff₀ hwR]; linarith
        rw [max_eq_right (by linarith)]
        exact min_eq_left this
      rw [hr]; linarith

end Erdos1186Ex
