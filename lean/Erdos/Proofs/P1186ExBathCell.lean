import Mathlib
import Erdos.Proofs.P1186ExBathLib
import Erdos.Proofs.P1186ExBathChk

/-!
# Erdos 1186 - soundness of the per-cell certificate: the bathtub bound on one grid cell

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's.  `cell_core` is the discrete Lemma 2 for one cell: if the integer data (`ν`, `T`) satisfy the checks of
`cellChk`, then for every 0/1 indicator `σ` with support `S` in the cell,
`Σ_{x ∈ cell} H2 x σ_x ≥ ν w |S| + 3 |S|² / T - (6 L² + 2 L) w`.
-/

namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

/-- the linear model of `H2` at the point `x` (unit cell `(x-1)/w`, offset `(x-1)%w + 1`). -/
noncomputable def linX (w x : ℕ) : ℝ :=
  (alphaF ((x - 1) / w) : ℝ) * w + (betaF ((x - 1) / w) : ℝ) * (((x - 1) % w + 1 : ℕ) : ℝ)

lemma split_pt (w : ℕ) (hw : 1 ≤ w) (x : ℕ) (hx : 1 ≤ x) :
    x = ((x - 1) / w) * w + ((x - 1) % w + 1) ∧ (x - 1) % w + 1 ≤ w := by
  have h1 := Nat.div_add_mod (x - 1) w
  have h2 : (x - 1) % w < w := Nat.mod_lt _ (by omega)
  have h3 : (x - 1) / w * w = w * ((x - 1) / w) := Nat.mul_comm _ _
  constructor <;> omega

lemma H2_linX (w : ℕ) (hw : 1 ≤ w) (x : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 1096 * w) :
    |(H2 w x : ℝ) - linX w x| ≤ 2 := by
  obtain ⟨hxe, hj⟩ := split_pt w hw x hx1
  have hp : (x - 1) / w ≤ 1095 := by
    have : (x - 1) / w < 1096 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    omega
  have h := H2_lin w hw ((x - 1) / w) ((x - 1) % w + 1) hp (by omega) hj
  rw [← hxe] at h
  unfold linX
  have h2 : |((H2 w x : ℤ) : ℝ) - ((alphaF ((x - 1) / w) * w
      + betaF ((x - 1) / w) * (((x - 1) % w + 1 : ℕ) : ℤ) : ℤ) : ℝ)| ≤ 2 := by exact_mod_cast h
  push_cast at h2 ⊢
  exact h2

/-- the profile of the unit cell `p'` above the level `ν w`, as a function of the offset `j`. -/
noncomputable def uP (w : ℕ) (ν : ℤ) (p' : ℕ) (j : ℕ) : ℝ :=
  (alphaF p' : ℝ) * w + (betaF p' : ℝ) * j - (ν : ℝ) * w

lemma ss_cast (p' : ℕ) : (((ss p' : ℕ) : ℤ) : ℝ) = |(betaF p' : ℝ)| := by
  unfold ss; rw [Int.natCast_natAbs, Int.cast_abs]

lemma uP_dist (w : ℕ) (ν : ℤ) (p' j j' : ℕ) :
    |uP w ν p' j - uP w ν p' j'| = (((ss p' : ℕ) : ℤ) : ℝ) * |(j : ℝ) - j'| := by
  unfold uP
  have : (alphaF p' : ℝ) * w + betaF p' * j - ν * w - ((alphaF p' : ℝ) * w + betaF p' * j' - ν * w)
      = (betaF p' : ℝ) * ((j : ℝ) - j') := by ring
  rw [this, abs_mul, ss_cast]

lemma uP_lo (w : ℕ) (ν : ℤ) (p' j : ℕ) (hj2 : j ≤ w) :
    (((dd p' - ν : ℤ)) : ℝ) * w ≤ uP w ν p' j := by
  unfold uP dd
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hjw : (j : ℝ) ≤ w := by exact_mod_cast hj2
  split_ifs with h
  · have hb : (0 : ℝ) ≤ betaF p' := by
      have : 0 ≤ betaF p' := by omega
      exact_mod_cast this
    push_cast
    nlinarith
  · have hb : (betaF p' : ℝ) < 0 := by
      have : betaF p' < 0 := by omega
      exact_mod_cast this
    push_cast
    nlinarith

lemma piece_count' (w : ℕ) (hw : 1 ≤ w) (ν : ℤ) (p' : ℕ) (hs : 0 < ss p') (t : ℝ) :
    (((Icc 1 w).filter (fun j => uP w ν p' j < t)).card : ℝ)
      ≤ (w : ℝ) * ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w) + 1 :=
  piece_count w hw (uP w ν p') (dd p' - ν) ((ss p' : ℕ) : ℤ) (by exact_mod_cast hs) (uP_dist w ν p')
    (fun j hj => uP_lo w ν p' j (Finset.mem_Icc.1 hj).2) t

/-- a point of the cell lies in a unit cell of the cell. -/
lemma mem_piece (w : ℕ) (hw : 1 ≤ w) (lo L x : ℕ) (hx : x ∈ Ioc (lo * w) ((lo + L) * w)) :
    (x - 1) / w ∈ Ico lo (lo + L) := by
  rw [Finset.mem_Ioc] at hx
  obtain ⟨h1, h2⟩ := hx
  rw [Finset.mem_Ico]
  constructor
  · rw [Nat.le_div_iff_mul_le (by omega)]; omega
  · rw [Nat.div_lt_iff_lt_mul (by omega)]; omega

lemma inc_eq (p' : ℕ) (ν : ℤ) (hnu : ν ≤ dd p') (hs : 0 < ss p') (h6 : 6 % ss p' = 0) (c : ℕ) :
    (if dd p' - ν ≤ (c : ℤ) ∧ (c : ℤ) < (dd p' - ν) + ((ss p' : ℕ) : ℤ)
        then 1 / (((ss p' : ℕ) : ℤ) : ℝ) else 0)
      = (((if (dd p' - ν).toNat ≤ c ∧ c < (dd p' - ν).toNat + ss p' then 6 / ss p' else 0 : ℕ)) : ℝ) / 6 := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = dd p' - ν := ⟨(dd p' - ν).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hte : (dd p' - ν).toNat = e := by omega
  rw [hte, ← he]
  have hcond : ((e : ℤ) ≤ (c : ℤ) ∧ (c : ℤ) < (e : ℤ) + ((ss p' : ℕ) : ℤ)) ↔ (e ≤ c ∧ c < e + ss p') := by
    constructor <;> (intro h; omega)
  by_cases h : e ≤ c ∧ c < e + ss p'
  · rw [if_pos (hcond.2 h), if_pos h]
    have hdvd : ss p' ∣ 6 := Nat.dvd_of_mod_eq_zero h6
    have hsR : (ss p' : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [Nat.cast_div hdvd hsR, Int.cast_natCast]
    push_cast
    field_simp
  · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h]
    simp

lemma cell_count (w : ℕ) (hw : 1 ≤ w) (lo L : ℕ) (ν : ℤ) (T : ℕ)
    (hnu : ∀ p' ∈ Ico lo (lo + L), ν ≤ dd p')
    (hpc : ∀ p' ∈ Ico lo (lo + L), 0 < ss p' ∧ 6 % ss p' = 0 ∧ (dd p' - ν).toNat + ss p' ≤ 3 * L)
    (hlev : ∀ c < 3 * L, ∑ p' ∈ Ico lo (lo + L),
        (if (dd p' - ν).toNat ≤ c ∧ c < (dd p' - ν).toNat + ss p' then 6 / ss p' else 0) ≤ T)
    (t : ℝ) (ht : 0 ≤ t) :
    (((Ioc (lo * w) ((lo + L) * w)).filter (fun x => linX w x - ν * w < t)).card : ℝ)
      ≤ (T / 6 : ℝ) * t + L := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hsub : (Ioc (lo * w) ((lo + L) * w)).filter (fun x => linX w x - ν * w < t) ⊆
      (Ico lo (lo + L)).biUnion (fun p' =>
        ((Icc 1 w).filter (fun j => uP w ν p' j < t)).image (fun j => p' * w + j)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxI, h3⟩ := hx
    have hxI' := Finset.mem_Ioc.1 hxI
    obtain ⟨hxe, hj⟩ := split_pt w hw x (by omega)
    rw [Finset.mem_biUnion]
    refine ⟨(x - 1) / w, mem_piece w hw lo L x hxI, ?_⟩
    rw [Finset.mem_image]
    refine ⟨(x - 1) % w + 1, ?_, hxe.symm⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, hj⟩, ?_⟩
    have : uP w ν ((x - 1) / w) ((x - 1) % w + 1) = linX w x - ν * w := by unfold uP linX; ring
    rw [this]; exact h3
  have hcardN : ((Ioc (lo * w) ((lo + L) * w)).filter (fun x => linX w x - ν * w < t)).card
      ≤ ∑ p' ∈ Ico lo (lo + L), ((Icc 1 w).filter (fun j => uP w ν p' j < t)).card :=
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun p' _ => Finset.card_image_le)
  have hcardR : (((Ioc (lo * w) ((lo + L) * w)).filter (fun x => linX w x - ν * w < t)).card : ℝ)
      ≤ ∑ p' ∈ Ico lo (lo + L), (((Icc 1 w).filter (fun j => uP w ν p' j < t)).card : ℝ) := by
    exact_mod_cast hcardN
  have hpiece : ∀ p' ∈ Ico lo (lo + L), (((Icc 1 w).filter (fun j => uP w ν p' j < t)).card : ℝ)
      ≤ (w : ℝ) * ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w) + 1 :=
    fun p' hp => piece_count' w hw ν p' (hpc p' hp).1 t
  have hsum := Finset.sum_le_sum hpiece
  have hinc : ∀ c : ℕ, c < 3 * L → ∑ p' ∈ Ico lo (lo + L),
      (if dd p' - ν ≤ (c : ℤ) ∧ (c : ℤ) < (dd p' - ν) + ((ss p' : ℕ) : ℤ)
        then 1 / (((ss p' : ℕ) : ℤ) : ℝ) else 0) ≤ (T : ℝ) / 6 := by
    intro c hc
    have e : ∑ p' ∈ Ico lo (lo + L),
        (if dd p' - ν ≤ (c : ℤ) ∧ (c : ℤ) < (dd p' - ν) + ((ss p' : ℕ) : ℤ)
          then 1 / (((ss p' : ℕ) : ℤ) : ℝ) else 0)
        = ((∑ p' ∈ Ico lo (lo + L),
            (if (dd p' - ν).toNat ≤ c ∧ c < (dd p' - ν).toNat + ss p' then 6 / ss p' else 0) : ℕ) : ℝ) / 6 := by
      rw [Nat.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p' hp
      exact inc_eq p' ν (hnu p' hp) (hpc p' hp).1 (hpc p' hp).2.1 c
    rw [e]
    have h1 := hlev c hc
    have h2 : ((∑ p' ∈ Ico lo (lo + L),
            (if (dd p' - ν).toNat ≤ c ∧ c < (dd p' - ν).toNat + ss p' then 6 / ss p' else 0) : ℕ) : ℝ)
        ≤ T := by exact_mod_cast h1
    linarith
  have hramp : ∑ p' ∈ Ico lo (lo + L), ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w)
      ≤ ((T : ℝ) / 6) * (t / w) := by
    apply ramp_sum_le (Ico lo (lo + L)) (fun p' => dd p' - ν) (fun p' => ((ss p' : ℕ) : ℤ))
      (fun p' hp => by show (0 : ℤ) < ((ss p' : ℕ) : ℤ); exact_mod_cast (hpc p' hp).1) ((T : ℝ) / 6)
      (level_count (Ico lo (lo + L)) (fun p' => dd p' - ν) (fun p' => ((ss p' : ℕ) : ℤ))
        (fun p' hp => by show (0 : ℤ) < ((ss p' : ℕ) : ℤ); exact_mod_cast (hpc p' hp).1)
        (fun p' hp => by have := hnu p' hp; simp only; omega)
        (3 * L)
        (fun p' hp => by have := (hpc p' hp).2.2; have := hnu p' hp; simp only; omega)
        ((T : ℝ) / 6) (by positivity) hinc)
      (t / w) (div_nonneg ht hwR.le)
  have hconst : ∑ p' ∈ Ico lo (lo + L), (1 : ℝ) = L := by simp
  have hexp : ∑ p' ∈ Ico lo (lo + L),
      ((w : ℝ) * ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w) + 1)
      = (w : ℝ) * ∑ p' ∈ Ico lo (lo + L), ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w) + L := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hconst]
  have hmul : (w : ℝ) * ∑ p' ∈ Ico lo (lo + L), ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w)
      ≤ (T / 6 : ℝ) * t := by
    have h1 := mul_le_mul_of_nonneg_left hramp hwR.le
    have h2 : (w : ℝ) * (((T : ℝ) / 6) * (t / w)) = (T / 6 : ℝ) * t := by field_simp
    linarith
  linarith

/-- **Lemma 2 (bathtub) on one cell, discrete.**  `S` is the support of the indicator `σ` in the cell
`(lo w, (lo+L) w]`. -/
lemma cell_core (w : ℕ) (hw : 1 ≤ w) (lo L : ℕ) (hL : lo + L ≤ 1096) (ν : ℤ) (T : ℕ) (hT : 0 < T)
    (hnu : ∀ p' ∈ Ico lo (lo + L), ν ≤ dd p')
    (hpc : ∀ p' ∈ Ico lo (lo + L), 0 < ss p' ∧ 6 % ss p' = 0 ∧ (dd p' - ν).toNat + ss p' ≤ 3 * L)
    (hlev : ∀ c < 3 * L, ∑ p' ∈ Ico lo (lo + L),
        (if (dd p' - ν).toNat ≤ c ∧ c < (dd p' - ν).toNat + ss p' then 6 / ss p' else 0) ≤ T)
    (σ : ℕ → ℤ) (hσ : IsInd σ) :
    (ν : ℝ) * w * (((Ioc (lo * w) ((lo + L) * w)).filter (fun x => σ x = 1)).card : ℝ)
      + 3 * (((Ioc (lo * w) ((lo + L) * w)).filter (fun x => σ x = 1)).card : ℝ) ^ 2 / T
      - (6 * (L : ℝ) ^ 2 + 2 * L) * w
      ≤ ((∑ x ∈ Ioc (lo * w) ((lo + L) * w), H2 w x * σ x : ℤ) : ℝ) := by
  set I := Ioc (lo * w) ((lo + L) * w) with hI
  set S := I.filter (fun x => σ x = 1) with hS
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hSI : S ⊆ I := Finset.filter_subset _ _
  have hsum : ∑ x ∈ I, H2 w x * σ x = ∑ x ∈ S, H2 w x := by
    rw [hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    rcases hσ x with h | h <;> simp [h]
  have hpt : ∀ x ∈ I, 1 ≤ x ∧ x ≤ 1096 * w := by
    intro x hx
    have hx' := Finset.mem_Ioc.1 hx
    refine ⟨by omega, ?_⟩
    calc x ≤ (lo + L) * w := hx'.2
      _ ≤ 1096 * w := Nat.mul_le_mul_right w hL
  have hg : ∀ x ∈ I, 0 ≤ linX w x - ν * w := by
    intro x hx
    have hx' := Finset.mem_Ioc.1 hx
    obtain ⟨hxe, hj⟩ := split_pt w hw x (by omega)
    have hp := mem_piece w hw lo L x hx
    have h1 := uP_lo w ν ((x - 1) / w) ((x - 1) % w + 1) hj
    have h2 : uP w ν ((x - 1) / w) ((x - 1) % w + 1) = linX w x - ν * w := by unfold uP linX; ring
    have h3 : (0 : ℝ) ≤ ((dd ((x - 1) / w) - ν : ℤ) : ℝ) := by
      have := hnu _ hp
      have : (0 : ℤ) ≤ dd ((x - 1) / w) - ν := by omega
      exact_mod_cast this
    have : 0 ≤ ((dd ((x - 1) / w) - ν : ℤ) : ℝ) * w := mul_nonneg h3 hwR.le
    linarith
  have hb := bathtub I (fun x => linX w x - ν * w) hg ((T : ℝ) / 6) (L : ℝ) (by positivity)
    (Nat.cast_nonneg L)
    (fun t ht => cell_count w hw lo L ν T hnu hpc hlev t ht) S hSI
  -- pointwise lower bound for `H2` on `S`
  have hpoint : ∀ x ∈ S, (linX w x - ν * w) + ((ν : ℝ) * w - 2) ≤ (H2 w x : ℝ) := by
    intro x hx
    have hxI := hSI hx
    obtain ⟨h1, h2⟩ := hpt x hxI
    have := H2_linX w hw x h1 h2
    rw [abs_le] at this
    linarith [this.1]
  have hS1 : ∑ x ∈ S, ((linX w x - ν * w) + ((ν : ℝ) * w - 2)) ≤ ∑ x ∈ S, (H2 w x : ℝ) :=
    Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hS1
  have hcast : ((∑ x ∈ I, H2 w x * σ x : ℤ) : ℝ) = ∑ x ∈ S, (H2 w x : ℝ) := by
    rw [hsum]; push_cast; rfl
  rw [hcast]
  -- cardinality bound
  have hcard : (S.card : ℝ) ≤ L * w := by
    have h1 : S.card ≤ I.card := Finset.card_le_card hSI
    have h2 : I.card = L * w := by
      rw [hI, Nat.card_Ioc, Nat.add_mul]; omega
    have : S.card ≤ L * w := by omega
    exact_mod_cast this
  set m : ℝ := (S.card : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  -- (max (m - L) 0)^2 >= m^2 - 2 L m
  have hMx : m ^ 2 - 2 * L * m ≤ (max (m - L) 0) ^ 2 := by
    rcases le_total (m - L) 0 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have hA : (max (m - L) 0) ^ 2 / (2 * ((T : ℝ) / 6)) = 3 * (max (m - L) 0) ^ 2 / T := by
    field_simp; ring
  rw [hA] at hb
  have hq : 0 < (1 : ℝ) / T := by positivity
  have hq1 : (1 : ℝ) / T ≤ 1 := by rw [div_le_one (by positivity)]; exact hTR
  have e1 : 3 * (max (m - L) 0) ^ 2 / T = 3 * (max (m - L) 0) ^ 2 * (1 / T) := by ring
  have e2 : 3 * m ^ 2 / T = 3 * m ^ 2 * (1 / T) := by ring
  have h5 : 3 * (m ^ 2 - 2 * L * m) * (1 / T) ≤ 3 * (max (m - L) 0) ^ 2 * (1 / T) := by
    apply mul_le_mul_of_nonneg_right _ hq.le
    linarith
  have h6 : 6 * L * m * (1 / T) ≤ 6 * L * m := by
    have : 0 ≤ 6 * L * m := by positivity
    nlinarith
  have h7 : 6 * L * m ≤ 6 * L * (L * w) := by
    apply mul_le_mul_of_nonneg_left hcard; positivity
  rw [e1] at hb
  rw [e2]
  nlinarith

/-! ### From the Boolean check to the hypotheses of `cell_core` -/

lemma allBelow_iff (P : ℕ → Bool) (n : ℕ) : allBelow P n = true ↔ ∀ c < n, P c = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ c hc
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h | h
      · exact h1 c h
      · rw [h]; exact h2
    · intro h; exact ⟨fun c hc => h c (by omega), h n (by omega)⟩

lemma S6_cons (q : ℕ × ℕ) (l : List (ℕ × ℕ)) (c : ℕ) :
    S6 (q :: l) c = (if q.1 ≤ c ∧ c < q.1 + q.2 then 6 / q.2 else 0) + S6 l c := by
  unfold S6
  rw [List.map_cons, List.sum_cons]
  congr 1
  by_cases h : q.1 ≤ c ∧ c < q.1 + q.2
  · have : (Nat.ble q.1 c && Nat.blt c (q.1 + q.2)) = true := by
      simp [Nat.ble_eq, Nat.blt_eq, h.1, h.2]
    simp [this, h]
  · have : (Nat.ble q.1 c && Nat.blt c (q.1 + q.2)) = false := by
      by_contra hc
      apply h
      have hc' : (Nat.ble q.1 c && Nat.blt c (q.1 + q.2)) = true := by simpa using hc
      simpa [Nat.ble_eq, Nat.blt_eq] using hc'
    simp [this, h]

lemma S6_pcsL (ν : ℤ) (c : ℕ) : ∀ (n lo : ℕ), S6 (pcsL ν lo n) c
    = ∑ k ∈ range n, (if (dd (lo + k) - ν).toNat ≤ c ∧ c < (dd (lo + k) - ν).toNat + ss (lo + k)
        then 6 / ss (lo + k) else 0)
  | 0, lo => by simp [S6, pcsL]
  | n + 1, lo => by
    have ih := S6_pcsL ν c n (lo + 1)
    rw [pcsL, S6_cons, ih, Finset.sum_range_succ', add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show lo + (k + 1) = lo + 1 + k by omega]

lemma cellChk_spec (G : Grid) (nuT : List ℤ) (tT : List ℕ) (i : ℕ) (h : cellChk G nuT tT i = true) :
    0 < G.len i ∧ G.hi i ≤ 1096 ∧ 0 < tT.getD i 0 ∧
    G.ai i * (1096 * 2192) ≤ ((G.len i : ℕ) : ℚ) * (nuT.getD i 0) ∧
    G.bi i * (4 * 1096 ^ 2) * ((tT.getD i 0 : ℕ) : ℚ) ≤ 6 * ((G.len i : ℕ) : ℚ) ^ 2 ∧
    (∀ p' ∈ Ico (G.lo i) (G.lo i + G.len i), nuT.getD i 0 ≤ dd p') ∧
    (∀ p' ∈ Ico (G.lo i) (G.lo i + G.len i), 0 < ss p' ∧ 6 % ss p' = 0 ∧
        (dd p' - nuT.getD i 0).toNat + ss p' ≤ 3 * G.len i) ∧
    (∀ c < 3 * G.len i, ∑ p' ∈ Ico (G.lo i) (G.lo i + G.len i),
        (if (dd p' - nuT.getD i 0).toNat ≤ c ∧ c < (dd p' - nuT.getD i 0).toNat + ss p'
          then 6 / ss p' else 0) ≤ tT.getD i 0) := by
  unfold cellChk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  simp only [decide_eq_true_eq] at h1 h2 h3 h4 h5
  rw [List.all_eq_true] at h6
  rw [allBelow_iff] at h7
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
  · intro p' hp
    have hp' : p' ∈ List.range' (G.lo i) (G.len i) := by
      rw [List.mem_range'_1]; rw [Finset.mem_Ico] at hp; omega
    have := h6 p' hp'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1
  · intro p' hp
    have hp' : p' ∈ List.range' (G.lo i) (G.len i) := by
      rw [List.mem_range'_1]; rw [Finset.mem_Ico] at hp; omega
    have := h6 p' hp'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.ble_eq] at this
    exact ⟨this.1.1.2, this.1.2, this.2⟩
  · intro c hc
    have := h7 c hc
    rw [Nat.ble_eq, S6_pcsL] at this
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    exact this

/-- `Grid.cell` is the point set `((lo) w, (lo + L) w]` of `cell_core`. -/
lemma cell_eq (G : Grid) (i w : ℕ) (hL : 0 < G.len i) :
    G.cell w i = Ioc (G.lo i * w) ((G.lo i + G.len i) * w) := by
  have hhi' : G.hi i = G.lo i + G.len i := by unfold Grid.len at hL ⊢; omega
  unfold Grid.cell; rw [hhi']

/-- **Lemma 2 (bathtub) on one grid cell**, from a passing `cellChk`. -/
theorem cell_sound (G : Grid) (nuT : List ℤ) (tT : List ℕ) (i : ℕ) (h : cellChk G nuT tT i = true)
    (w : ℕ) (hw : 1 ≤ w) (σ : ℕ → ℤ) (hσ : IsInd σ) :
    2 * (nn w : ℝ) ^ 2 * ((G.ai i : ℝ) * G.yv w σ i + (G.bi i : ℝ) * G.yv w σ i ^ 2)
      - (6 * (G.len i : ℝ) ^ 2 + 2 * (G.len i : ℝ)) * w
      ≤ ((∑ x ∈ G.cell w i, H2 w x * σ x : ℤ) : ℝ) := by
  obtain ⟨hL, hhi, hT, ha, hb, hnu, hpc, hlev⟩ := cellChk_spec G nuT tT i h
  have hhi' : G.hi i = G.lo i + G.len i := by unfold Grid.len at hL ⊢; omega
  have hL1096 : G.lo i + G.len i ≤ 1096 := by rw [← hhi']; exact hhi
  have core := cell_core w hw (G.lo i) (G.len i) hL1096 (nuT.getD i 0) (tT.getD i 0) hT hnu hpc hlev σ hσ
  have hcell := cell_eq G i w hL
  rw [hcell]
  set S := (Ioc (G.lo i * w) ((G.lo i + G.len i) * w)).filter (fun x => σ x = 1) with hS
  have hsumσ : (∑ x ∈ Ioc (G.lo i * w) ((G.lo i + G.len i) * w), σ x) = (S.card : ℤ) := by
    rw [hS, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    rcases hσ x with h | h <;> simp [h]
  have hy : G.yv w σ i = (S.card : ℝ) / ((G.len i : ℝ) * w) := by
    unfold Grid.yv
    rw [hcell, hsumσ]
    push_cast
    rfl
  rw [hy]
  have haR : (G.ai i : ℝ) * (1096 * 2192) ≤ (G.len i : ℝ) * (nuT.getD i 0 : ℤ) := by exact_mod_cast ha
  have hbR : (G.bi i : ℝ) * (4 * 1096 ^ 2) * (tT.getD i 0 : ℕ) ≤ 6 * (G.len i : ℝ) ^ 2 := by
    exact_mod_cast hb
  have hLR : (0 : ℝ) < G.len i := by exact_mod_cast hL
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hTR : (0 : ℝ) < (tT.getD i 0 : ℕ) := by exact_mod_cast hT
  have hnn : (nn w : ℝ) = 1096 * w := by unfold nn; push_cast; ring
  rw [hnn]
  set m : ℝ := (S.card : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set a : ℝ := (G.ai i : ℝ)
  set b : ℝ := (G.bi i : ℝ)
  set Lr : ℝ := (G.len i : ℝ)
  set ν : ℝ := ((nuT.getD i 0 : ℤ) : ℝ)
  set T : ℝ := ((tT.getD i 0 : ℕ) : ℝ)
  have key1 : 2 * (1096 * (w : ℝ)) ^ 2 * (a * (m / (Lr * w))) ≤ ν * w * m := by
    have e : 2 * (1096 * (w : ℝ)) ^ 2 * (a * (m / (Lr * w))) = (a * (1096 * 2192)) * (w * m / Lr) := by
      field_simp; ring
    rw [e]
    have h1 : (a * (1096 * 2192)) * (w * m / Lr) ≤ (Lr * ν) * (w * m / Lr) :=
      mul_le_mul_of_nonneg_right haR (by positivity)
    have h2 : (Lr * ν) * (w * m / Lr) = ν * w * m := by field_simp
    linarith
  have key2 : 2 * (1096 * (w : ℝ)) ^ 2 * (b * (m / (Lr * w)) ^ 2) ≤ 3 * m ^ 2 / T := by
    have e : 2 * (1096 * (w : ℝ)) ^ 2 * (b * (m / (Lr * w)) ^ 2)
        = (b * (4 * 1096 ^ 2) * T) * (m ^ 2 / (2 * Lr ^ 2 * T)) := by
      field_simp; ring
    rw [e]
    have h1 : (b * (4 * 1096 ^ 2) * T) * (m ^ 2 / (2 * Lr ^ 2 * T))
        ≤ (6 * Lr ^ 2) * (m ^ 2 / (2 * Lr ^ 2 * T)) :=
      mul_le_mul_of_nonneg_right hbR (by positivity)
    have h2 : (6 * Lr ^ 2) * (m ^ 2 / (2 * Lr ^ 2 * T)) = 3 * m ^ 2 / T := by field_simp; ring
    linarith
  have hcore : ν * w * m + 3 * m ^ 2 / T - (6 * Lr ^ 2 + 2 * Lr) * w
      ≤ ((∑ x ∈ Ioc (G.lo i * w) ((G.lo i + G.len i) * w), H2 w x * σ x : ℤ) : ℝ) := core
  nlinarith

/-- **The bathtub inequality for a grid**, from a passing check on every cell. -/
theorem bathOK_of_chk (G : Grid) (nuT : List ℤ) (tT : List ℕ)
    (h : ∀ i < G.N, cellChk G nuT tT i = true) : BathOK G := by
  refine ⟨∑ i ∈ range G.N, (6 * (G.len i : ℝ) ^ 2 + 2 * (G.len i : ℝ)), ?_⟩
  intro w hw σ hσ i hi
  have h1 := cell_sound G nuT tT i (h i hi) w hw σ hσ
  have h2 : (6 * (G.len i : ℝ) ^ 2 + 2 * (G.len i : ℝ))
      ≤ ∑ i ∈ range G.N, (6 * (G.len i : ℝ) ^ 2 + 2 * (G.len i : ℝ)) :=
    Finset.single_le_sum (f := fun i => (6 * (G.len i : ℝ) ^ 2 + 2 * (G.len i : ℝ)))
      (fun i _ => by positivity) (Finset.mem_range.2 hi)
  have hwR : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  nlinarith

end Erdos1186Ex
