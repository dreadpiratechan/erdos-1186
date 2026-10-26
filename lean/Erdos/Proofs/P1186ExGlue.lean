import Mathlib
import Erdos.Proofs.P1186
import Erdos.Proofs.P1186Low
import Erdos.Proofs.P1186M2
import Erdos.Proofs.P1186M2Low
import Erdos.Proofs.P1186ExData
import Erdos.Proofs.P1186Ex

/-!
# Erdos 1186 - the glue of the claimed proof of `δ 3 = 117/2192` (lane `exglue`)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's.  This module assembles the pieces fixed by the interface `P1186Ex.lean`; it proves none of the pieces.

Main theorem: `Erdos1186Ex.lower_of_parts` (statement as in the shared interface: `StarOK`, `BathOK`/`PairOK` on the
two grids, the five `RegionLB`), giving `117/2192 ≤ δ 3`.

Contents.
* `Wm_eq_Qd`: the window correlation is the quadratic form `Qd` of the interface.
* `expansion`: for `s = s* (1 - 2σ)`, `Qd s = Qd s* + 2 Σ H2 σ + 4 Qd (s* σ)`.
* Grid lemmas for a well-formed grid: the cells `(lo_i w, hi_i w]` partition `[1, 1096 w]`; the cell densities
  `y_i` lie in `[0, 1]` and `Σ w_i y_i = (Σ σ) / n`.
* `combine`: per grid, `Qd s ≥ -(5/137) n² + 4 n² L(y) - C w`.
* `wm_lower`: for every colouring `c`, `Wm (sg c) n ≥ -(5/137) n² - C w` (case split on `m`, symmetry `σ ↦ 1 - σ`).
* `lower_of_parts`: `V_lower` and the `liminf` argument (as in `key_bound2` / `lower_of_cubeLB`).
-/

open Finset Filter

namespace Erdos1186Ex

open Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

/-! ## `Wm` is `Qd` -/

lemma rdI_sum (s : ℕ → ℤ) (n y : ℕ) (hy : y ∈ Icc 1 n) :
    ∑ x ∈ Icc 1 n, rdI n x y * s x = pre s (y + Dm n y) - pre s (y - Dm n y - 1) := by
  have h1 : ∀ x ∈ Icc 1 n, rdI n x y * s x
      = if (1 ≤ 2 * (y : ℤ) - x ∧ 2 * (y : ℤ) - x ≤ n) then s x else 0 := by
    intro x _; unfold rdI; split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have h2 : (Icc 1 n).filter (fun x : ℕ => 1 ≤ 2 * (y : ℤ) - x ∧ 2 * (y : ℤ) - x ≤ n)
      = Ioc (y - Dm n y - 1) (y + Dm n y) := by
    ext x
    simp only [Finset.mem_filter, mem_Icc, mem_Ioc, Dm]
    simp only [mem_Icc] at hy
    omega
  rw [h2, sum_Ioc_eq s (by unfold Dm; omega)]

lemma Wm_eq_Qd (s : ℕ → ℤ) (n : ℕ) : Wm s n = Qd n s := by
  unfold Wm Qd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← rdI_sum s n y hy, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _; ring

lemma Qd_neg (n : ℕ) (u : ℕ → ℤ) : Qd n (fun x => - u x) = Qd n u := by
  unfold Qd
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  ring

/-! ## The expansion identity -/

/-- the two cross terms -/
def crossA (n : ℕ) (s σ : ℕ → ℤ) : ℤ := ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n, rdI n x y * (s x * σ x) * s y
def crossB (n : ℕ) (s σ : ℕ → ℤ) : ℤ := ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n, rdI n x y * s x * (s y * σ y)

lemma expansion_gen (n : ℕ) (s σ : ℕ → ℤ) :
    Qd n (fun x => s x * (1 - 2 * σ x))
      = Qd n s - 2 * (crossA n s σ + crossB n s σ) + 4 * Qd n (fun x => s x * σ x) := by
  unfold Qd crossA crossB
  have e : ∀ x y : ℕ, rdI n x y * (s x * (1 - 2 * σ x)) * (s y * (1 - 2 * σ y))
      = rdI n x y * s x * s y - 2 * (rdI n x y * (s x * σ x) * s y + rdI n x y * s x * (s y * σ y))
        + 4 * (rdI n x y * (s x * σ x) * (s y * σ y)) := by
    intro x y; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma H2_sum (n : ℕ) (s σ : ℕ → ℤ) :
    ∑ x ∈ Icc 1 n, (-s x * (∑ y ∈ Icc 1 n, rdI n x y * s y + ∑ e ∈ Icc 1 n, rdI n e x * s e)) * σ x
      = -(crossA n s σ + crossB n s σ) := by
  have hA : crossA n s σ = ∑ x ∈ Icc 1 n, (s x * σ x) * ∑ y ∈ Icc 1 n, rdI n x y * s y := by
    unfold crossA
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
  have hB : crossB n s σ = ∑ x ∈ Icc 1 n, (s x * σ x) * ∑ e ∈ Icc 1 n, rdI n e x * s e := by
    unfold crossB
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
  rw [hA, hB, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro x _
  ring

lemma expansion (w : ℕ) (σ : ℕ → ℤ) :
    Qd (nn w) (fun x => sstar w x * (1 - 2 * σ x))
      = Qd (nn w) (sstar w) + 2 * ∑ x ∈ Icc 1 (nn w), H2 w x * σ x
        + 4 * Qd (nn w) (fun x => sstar w x * σ x) := by
  have h1 := expansion_gen (nn w) (sstar w) σ
  have h2 := H2_sum (nn w) (sstar w) σ
  have h3 : ∑ x ∈ Icc 1 (nn w), H2 w x * σ x
      = -(crossA (nn w) (sstar w) σ + crossB (nn w) (sstar w) σ) := by
    unfold H2; exact h2
  rw [h1, h3]; ring

/-! ## Well-formed grids -/

namespace Grid

lemma length_eq (G : Grid) (hG : G.WF) : G.pts.length = G.N + 1 := by
  obtain ⟨h0, _⟩ := hG
  unfold N
  rcases h : G.pts with _ | ⟨a, t⟩
  · simp [h] at h0
  · simp

lemma lo_zero (G : Grid) (hG : G.WF) : G.lo 0 = 0 := by
  obtain ⟨h0, _⟩ := hG
  unfold lo
  rcases h : G.pts with _ | ⟨a, t⟩
  · simp [h] at h0
  · simp [h] at h0 ⊢; exact h0

lemma lo_N (G : Grid) (hG : G.WF) : G.lo G.N = 1096 := by
  have hlen := length_eq G hG
  obtain ⟨_, h1, _⟩ := hG
  unfold lo
  rw [List.getLast?_eq_getElem?] at h1
  rw [List.getD_eq_getElem?_getD]
  simp only [hlen, Nat.add_sub_cancel] at h1
  rw [h1]; rfl

lemma lo_lt_hi (G : Grid) (hG : G.WF) {i : ℕ} (hiN : i < G.N) : G.lo i < G.hi i := by
  have hlen := length_eq G hG
  obtain ⟨_, _, hp, _⟩ := hG
  unfold lo hi
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact List.pairwise_iff_getElem.mp hp i (i + 1) (by omega) (by omega) (by omega)

/-- the cells `(lo_i w, hi_i w]` of a well-formed grid partition `[1, 1096 w]` -/
lemma cells_sum (G : Grid) (hG : G.WF) (w : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ range G.N, ∑ x ∈ G.cell w i, f x = ∑ x ∈ Icc 1 (nn w), f x := by
  have e1 : ∀ i ∈ range G.N,
      ∑ x ∈ G.cell w i, f x = pre f (G.lo (i + 1) * w) - pre f (G.lo i * w) := by
    intro i hi
    have h := (G.lo_lt_hi hG (mem_range.mp hi)).le
    unfold cell
    exact sum_Ioc_eq f (Nat.mul_le_mul_right w h)
  rw [Finset.sum_congr rfl e1, Finset.sum_range_sub (fun i => pre f (G.lo i * w)), G.lo_N hG, G.lo_zero hG]
  unfold pre nn
  have : Ioc 0 (1096 * w) = Icc 1 (1096 * w) := by
    ext x; simp only [mem_Ioc, mem_Icc]; omega
  rw [this]; simp

lemma cell_card (G : Grid) (w i : ℕ) : (G.cell w i).card = G.len i * w := by
  unfold cell len; rw [Nat.card_Ioc, Nat.sub_mul]

lemma yv_mem (G : Grid) (hG : G.WF) (w : ℕ) (hw : 1 ≤ w) (σ : ℕ → ℤ) (hσ : IsInd σ) {i : ℕ}
    (hiN : i < G.N) : 0 ≤ G.yv w σ i ∧ G.yv w σ i ≤ 1 := by
  have hlen : 0 < G.len i := by have := G.lo_lt_hi hG hiN; unfold len; omega
  have hpos : (0 : ℝ) < ((G.len i * w : ℕ) : ℝ) := by
    have : 0 < G.len i * w := Nat.mul_pos hlen (by omega)
    exact_mod_cast this
  have h0 : 0 ≤ ∑ x ∈ G.cell w i, σ x :=
    Finset.sum_nonneg (fun x _ => by rcases hσ x with h | h <;> simp [h])
  have h1 : ∑ x ∈ G.cell w i, σ x ≤ ((G.len i * w : ℕ) : ℤ) := by
    have : ∑ x ∈ G.cell w i, σ x ≤ ∑ _x ∈ G.cell w i, (1 : ℤ) :=
      Finset.sum_le_sum (fun x _ => by rcases hσ x with h | h <;> simp [h])
    simpa [cell_card] using this
  unfold yv
  constructor
  · exact div_nonneg (by exact_mod_cast h0) hpos.le
  · rw [div_le_one hpos]; exact_mod_cast h1

lemma mval_yv (G : Grid) (hG : G.WF) (w : ℕ) (hw : 1 ≤ w) (σ : ℕ → ℤ) :
    G.mval (G.yv w σ) = ((∑ x ∈ Icc 1 (nn w), σ x : ℤ) : ℝ) / (nn w : ℝ) := by
  have hn : (0 : ℝ) < (nn w : ℝ) := by
    have : 0 < nn w := by unfold nn; omega
    exact_mod_cast this
  have e : ∀ i ∈ range G.N, (G.wt i : ℝ) * G.yv w σ i
      = ((∑ x ∈ G.cell w i, σ x : ℤ) : ℝ) / (nn w : ℝ) := by
    intro i hi
    have hlen : 0 < G.len i := by have := G.lo_lt_hi hG (mem_range.mp hi); unfold len; omega
    have hlenR : (0 : ℝ) < (G.len i : ℝ) := by exact_mod_cast hlen
    have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (by omega : 0 < w)
    unfold wt yv nn
    push_cast
    field_simp
  unfold mval
  rw [Finset.sum_congr rfl e, ← Finset.sum_div]
  congr 1
  rw [← cells_sum G hG w σ]
  push_cast
  rfl

end Grid

/-! ## The combination for one grid -/

/-- For a well-formed grid with the three parts: `Qd s ≥ -(5/137) n² + 4 n² L(y) - C w`, `s = s* (1 - 2σ)`. -/
theorem combine (G : Grid) (hG : G.WF) (hS : StarOK) (hB : BathOK G) (hP : PairOK G) :
    ∃ C : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ σ : ℕ → ℤ, IsInd σ →
      -(5 / 137 : ℝ) * (nn w : ℝ) ^ 2 + 4 * (nn w : ℝ) ^ 2 * G.Lval (G.yv w σ) - C * w
        ≤ (Qd (nn w) (fun x => sstar w x * (1 - 2 * σ x)) : ℤ) := by
  obtain ⟨CS, hCS⟩ := hS
  obtain ⟨CB, hCB⟩ := hB
  obtain ⟨CP, hCP⟩ := hP
  refine ⟨CS + 2 * G.N * CB + 4 * CP, fun w hw σ hσ => ?_⟩
  have hexp := expansion w σ
  have hexpR : ((Qd (nn w) (fun x => sstar w x * (1 - 2 * σ x)) : ℤ) : ℝ)
      = ((Qd (nn w) (sstar w) : ℤ) : ℝ) + 2 * ((∑ x ∈ Icc 1 (nn w), H2 w x * σ x : ℤ) : ℝ)
        + 4 * ((Qd (nn w) (fun x => sstar w x * σ x) : ℤ) : ℝ) := by exact_mod_cast hexp
  have h1 := hCS w hw
  rw [Wm_eq_Qd] at h1
  have h3 := hCP w hw σ hσ
  have h2 : ∑ i ∈ range G.N, (2 * (nn w : ℝ) ^ 2 * ((G.ai i : ℝ) * G.yv w σ i + (G.bi i : ℝ) * G.yv w σ i ^ 2)
      - CB * w) ≤ ((∑ x ∈ Icc 1 (nn w), H2 w x * σ x : ℤ) : ℝ) := by
    rw [← Grid.cells_sum G hG w (fun x => H2 w x * σ x), Int.cast_sum]
    exact Finset.sum_le_sum (fun i hi => hCB w hw σ hσ i (mem_range.mp hi))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, card_range, nsmul_eq_mul] at h2
  unfold Grid.Lval
  rw [hexpR]
  nlinarith [h1, h2, h3]

/-! ## Regions, symmetry -/

/-- the density `m = (Σ σ) / n` -/
noncomputable def msum (w : ℕ) (σ : ℕ → ℤ) : ℝ := ((∑ x ∈ Icc 1 (nn w), σ x : ℤ) : ℝ) / (nn w : ℝ)

lemma lval_nonneg (G : Grid) (hG : G.WF) (lo hi : ℚ) (r : RegionLB G lo hi) (w : ℕ) (hw : 1 ≤ w)
    (σ : ℕ → ℤ) (hσ : IsInd σ) (hlo : (lo : ℝ) ≤ msum w σ) (hhi : msum w σ ≤ hi) :
    0 ≤ G.Lval (G.yv w σ) :=
  r (G.yv w σ) (fun i hi => Grid.yv_mem G hG w hw σ hσ hi)
    (by rw [Grid.mval_yv G hG w hw σ]; exact hlo) (by rw [Grid.mval_yv G hG w hw σ]; exact hhi)

lemma msum_bounds (w : ℕ) (hw : 1 ≤ w) (σ : ℕ → ℤ) (hσ : IsInd σ)
    (h2 : 2 * ∑ x ∈ Icc 1 (nn w), σ x ≤ (nn w : ℤ)) : 0 ≤ msum w σ ∧ msum w σ ≤ 1 / 2 := by
  have hn : (0 : ℝ) < (nn w : ℝ) := by
    have : 0 < nn w := by unfold nn; omega
    exact_mod_cast this
  have h0 : 0 ≤ ∑ x ∈ Icc 1 (nn w), σ x :=
    Finset.sum_nonneg (fun x _ => by rcases hσ x with h | h <;> simp [h])
  have h2R : 2 * ((∑ x ∈ Icc 1 (nn w), σ x : ℤ) : ℝ) ≤ (nn w : ℝ) := by exact_mod_cast h2
  have h0R : (0 : ℝ) ≤ ((∑ x ∈ Icc 1 (nn w), σ x : ℤ) : ℝ) := by exact_mod_cast h0
  unfold msum
  constructor
  · exact div_nonneg h0R hn.le
  · rw [div_le_iff₀ hn]; linarith

/-- The core: for `σ` with `Σ σ ≤ n / 2`, `Qd (s* (1 - 2σ)) ≥ -(5/137) n² - C w`. -/
theorem core (hS : StarOK) (hB24 : BathOK G24) (hB8 : BathOK G8) (hP24 : PairOK G24) (hP8 : PairOK G8)
    (hW24 : G24.WF) (hW8 : G8.WF)
    (r1 : RegionLB G24 0 (1 / 5)) (r2 : RegionLB G24 (1 / 5) (3 / 10)) (r3 : RegionLB G24 (3 / 10) (2 / 5))
    (r4 : RegionLB G8 (2 / 5) (9 / 20)) (r5 : RegionLB G8 (9 / 20) (1 / 2)) :
    ∃ C : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ σ : ℕ → ℤ, IsInd σ → 2 * ∑ x ∈ Icc 1 (nn w), σ x ≤ (nn w : ℤ) →
      -(5 / 137 : ℝ) * (nn w : ℝ) ^ 2 - C * w
        ≤ (Qd (nn w) (fun x => sstar w x * (1 - 2 * σ x)) : ℤ) := by
  obtain ⟨C1, h1⟩ := combine G24 hW24 hS hB24 hP24
  obtain ⟨C2, h2⟩ := combine G8 hW8 hS hB8 hP8
  refine ⟨max C1 C2, fun w hw σ hσ hsum => ?_⟩
  obtain ⟨hm0, hm1⟩ := msum_bounds w hw σ hσ hsum
  have hn2 : (0 : ℝ) ≤ (nn w : ℝ) ^ 2 := sq_nonneg _
  have hwR : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
  by_cases hA : msum w σ ≤ 2 / 5
  · have hL : 0 ≤ G24.Lval (G24.yv w σ) := by
      rcases le_or_gt (msum w σ) (1 / 5) with h | h
      · exact lval_nonneg G24 hW24 0 (1 / 5) r1 w hw σ hσ (by push_cast; linarith) (by push_cast; linarith)
      · rcases le_or_gt (msum w σ) (3 / 10) with h' | h'
        · exact lval_nonneg G24 hW24 (1 / 5) (3 / 10) r2 w hw σ hσ (by push_cast; linarith)
            (by push_cast; linarith)
        · exact lval_nonneg G24 hW24 (3 / 10) (2 / 5) r3 w hw σ hσ (by push_cast; linarith)
            (by push_cast; linarith)
    have := h1 w hw σ hσ
    nlinarith [mul_nonneg hn2 hL, mul_nonneg (sub_nonneg.mpr (le_max_left C1 C2)) hwR]
  · have hL : 0 ≤ G8.Lval (G8.yv w σ) := by
      rcases le_or_gt (msum w σ) (9 / 20) with h | h
      · exact lval_nonneg G8 hW8 (2 / 5) (9 / 20) r4 w hw σ hσ (by push_cast; linarith)
          (by push_cast; linarith)
      · exact lval_nonneg G8 hW8 (9 / 20) (1 / 2) r5 w hw σ hσ (by push_cast; linarith)
          (by push_cast; linarith)
    have := h2 w hw σ hσ
    nlinarith [mul_nonneg hn2 hL, mul_nonneg (sub_nonneg.mpr (le_max_right C1 C2)) hwR]

/-- `sg c = s* (1 - 2σ)` for the disagreement indicator `σ` -/
def disagree (w : ℕ) (c : ℕ → Bool) (x : ℕ) : ℤ := if c x = ck (2 * w) x then 0 else 1

lemma disagree_ind (w : ℕ) (c : ℕ → Bool) : IsInd (disagree w c) := by
  intro x; unfold disagree; split_ifs <;> simp

lemma sg_eq (w : ℕ) (c : ℕ → Bool) (x : ℕ) : sg c x = sstar w x * (1 - 2 * disagree w c x) := by
  unfold sstar sg disagree
  cases h1 : c x <;> cases h2 : ck (2 * w) x <;> simp

/-- Window correlation lower bound for every colouring of `[1, 1096 w]`. -/
theorem wm_lower (hS : StarOK) (hB24 : BathOK G24) (hB8 : BathOK G8) (hP24 : PairOK G24) (hP8 : PairOK G8)
    (hW24 : G24.WF) (hW8 : G8.WF)
    (r1 : RegionLB G24 0 (1 / 5)) (r2 : RegionLB G24 (1 / 5) (3 / 10)) (r3 : RegionLB G24 (3 / 10) (2 / 5))
    (r4 : RegionLB G8 (2 / 5) (9 / 20)) (r5 : RegionLB G8 (9 / 20) (1 / 2)) :
    ∃ C : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ c : ℕ → Bool,
      -(5 / 137 : ℝ) * (nn w : ℝ) ^ 2 - C * w ≤ (Wm (sg c) (nn w) : ℤ) := by
  obtain ⟨C, hC⟩ := core hS hB24 hB8 hP24 hP8 hW24 hW8 r1 r2 r3 r4 r5
  refine ⟨C, fun w hw c => ?_⟩
  rw [Wm_eq_Qd]
  by_cases hsum : 2 * ∑ x ∈ Icc 1 (nn w), disagree w c x ≤ (nn w : ℤ)
  · have e : sg c = fun x => sstar w x * (1 - 2 * disagree w c x) := funext (sg_eq w c)
    rw [e]
    exact hC w hw _ (disagree_ind w c) hsum
  · have hind : IsInd (fun x => 1 - disagree w c x) := by
      intro x; rcases disagree_ind w c x with h | h <;> simp [h]
    have hs' : 2 * ∑ x ∈ Icc 1 (nn w), (1 - disagree w c x) ≤ (nn w : ℤ) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, nn]
      unfold nn at hsum
      push_cast at hsum ⊢
      omega
    have e : sg c = fun x => -(sstar w x * (1 - 2 * (1 - disagree w c x))) := by
      funext x; rw [sg_eq w c x]; ring
    rw [e, Qd_neg]
    exact hC w hw _ hind hs'

/-! ## From the window bound to `δ 3` -/

/-- `n = 1096 w`: `b n² - K n ≤ monoCount` for every colouring, with `b = 117/2192`. -/
lemma finite_bound (C : ℝ)
    (hC : ∀ w : ℕ, 1 ≤ w → ∀ c : ℕ → Bool,
      -(5 / 137 : ℝ) * (nn w : ℝ) ^ 2 - C * w ≤ (Wm (sg c) (nn w) : ℤ))
    (w : ℕ) (hw : 1 ≤ w) (c : ℕ → Bool) :
    (117 / 2192 : ℝ) * (nn w : ℝ) ^ 2 - (1 / 2 + C / 4384) * (nn w : ℝ) ≤ (monoCount 3 (nn w) c : ℝ) := by
  have hV := V_lower (nn w) c
  have hVR : ((2 * (nn w : ℤ) ^ 2 - 16 * (nn w : ℤ) + 8 * Wm (sg c) (nn w) + 2 * (pre (sg c) (nn w)) ^ 2 : ℤ) : ℝ)
      ≤ ((32 * (monoCount 3 (nn w) c : ℤ) : ℤ) : ℝ) := by exact_mod_cast hV
  push_cast at hVR
  have hc := hC w hw c
  have hpre : (0 : ℝ) ≤ ((pre (sg c) (nn w) : ℤ) : ℝ) ^ 2 := sq_nonneg _
  have hnw : (nn w : ℝ) = 1096 * (w : ℝ) := by unfold nn; push_cast; ring
  have hwn : (w : ℝ) = (nn w : ℝ) / 1096 := by rw [hnw]; ring
  rw [hwn] at hc
  have e : (C / 4384) * (nn w : ℝ) = C * ((nn w : ℝ) / 1096) / 4 := by ring
  nlinarith [hVR, hc, hpre]

/-- every `N` satisfies `b N² - (2192 b + K) N ≤ minMonoCount 3 N`. -/
lemma key_bound (K : ℝ) (hK0 : 0 ≤ K)
    (hfin : ∀ w : ℕ, 1 ≤ w → ∀ c : ℕ → Bool,
      (117 / 2192 : ℝ) * (nn w : ℝ) ^ 2 - K * (nn w : ℝ) ≤ (monoCount 3 (nn w) c : ℝ)) (N : ℕ) :
    (117 / 2192 : ℝ) * (N : ℝ) ^ 2 - (2192 * (117 / 2192 : ℝ) + K) * N ≤ (minMonoCount 3 N : ℝ) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hm0 : (0 : ℝ) ≤ (minMonoCount 3 N : ℝ) := Nat.cast_nonneg _
  by_cases hN : N < 1096
  · have hNR : (N : ℝ) ≤ 1096 := by exact_mod_cast hN.le
    nlinarith [mul_nonneg hN0 (by linarith : (0 : ℝ) ≤ 1096 - N), mul_nonneg hK0 hN0]
  · have hN1 : 1096 ≤ N := not_lt.mp hN
    set w := N / 1096 with hw
    have hw1 : 1 ≤ w := by omega
    have hq1 : nn w ≤ N := by unfold nn; omega
    have hq2 : N < nn w + 1096 := by unfold nn; omega
    obtain ⟨c, hc⟩ := exists_min_colouring 3 (nn w)
    have hmain := hfin w hw1 c
    rw [hc] at hmain
    have hmono : (minMonoCount 3 (nn w) : ℝ) ≤ minMonoCount 3 N := by
      exact_mod_cast minMono_mono 3 hq1
    have hq1R : ((nn w : ℕ) : ℝ) ≤ N := by exact_mod_cast hq1
    have hq2R : (N : ℝ) < (nn w : ℝ) + 1096 := by exact_mod_cast hq2
    have hq0 : (0 : ℝ) ≤ (nn w : ℝ) := Nat.cast_nonneg _
    have hN1R : (1096 : ℝ) ≤ N := by exact_mod_cast hN1
    have h1 : ((N : ℝ) - 1096) ^ 2 ≤ (nn w : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith [mul_le_mul_of_nonneg_left hq1R hK0, h1]

/-- **The glue.**  The five parts of the claimed proof (the star colouring's window correlation, the bathtub bound
and the cell-pair bound on each of the two grids, and the five finite certificates) give `δ 3 ≥ 117/2192`. -/
theorem lower_of_parts (hS : StarOK) (hB24 : BathOK G24) (hB8 : BathOK G8) (hP24 : PairOK G24) (hP8 : PairOK G8)
    (r1 : RegionLB G24 0 (1 / 5)) (r2 : RegionLB G24 (1 / 5) (3 / 10)) (r3 : RegionLB G24 (3 / 10) (2 / 5))
    (r4 : RegionLB G8 (2 / 5) (9 / 20)) (r5 : RegionLB G8 (9 / 20) (1 / 2)) :
    (117 / 2192 : ℝ) ≤ δ 3 := by
  have hW24 : G24.WF := (by decide +kernel : G24.WF ∧ G8.WF).1
  have hW8 : G8.WF := (by decide +kernel : G24.WF ∧ G8.WF).2
  obtain ⟨C, hC⟩ := wm_lower hS hB24 hB8 hP24 hP8 hW24 hW8 r1 r2 r3 r4 r5
  set C0 := max C 0 with hC0def
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hC' : ∀ w : ℕ, 1 ≤ w → ∀ c : ℕ → Bool,
      -(5 / 137 : ℝ) * (nn w : ℝ) ^ 2 - C0 * w ≤ (Wm (sg c) (nn w) : ℤ) := by
    intro w hw c
    have := hC w hw c
    have hwR : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_left C 0)) hwR]
  set K := 1 / 2 + C0 / 4384 with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hfin := finite_bound C0 hC'
  have hkey := key_bound K hK0 hfin
  set b : ℝ := 117 / 2192 with hb
  apply le_of_forall_pos_le_add
  intro ε hε
  set K' := 2192 * b + K with hK'
  have hK'0 : 0 < K' := by positivity
  have hev : ∀ᶠ n : ℕ in atTop, b - ε ≤ (minMonoCount 3 n : ℝ) / (n : ℝ) ^ 2 := by
    rw [Filter.eventually_atTop]
    refine ⟨⌈K' / ε⌉₊ + 1, fun n hn => ?_⟩
    have hnpos' : 0 < n := by omega
    have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hnpos'
    have hKn : K' ≤ ε * n := by
      have h1 := Nat.le_ceil (K' / ε)
      have h2 : (⌈K' / ε⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈K' / ε⌉₊ ≤ n)
      have h3 : K' / ε ≤ n := h1.trans h2
      rwa [div_le_iff₀ hε, mul_comm] at h3
    rw [le_div_iff₀ (by positivity)]
    have := hkey n
    nlinarith
  have := le_delta_of_eventually 3 (b - ε) hev
  linarith

/-- **`δ 3 = 117/2192` from the five parts** (the upper half is day 1's `prs_bounds_upper`).  This is the upstream
statement `erdos_1186.variants.prs_conjecture` once the parts (`StarOK`, `BathOK`, `PairOK` on both grids, the five
`RegionLB`) are proved. -/
theorem delta3_eq_of_parts (hS : StarOK) (hB24 : BathOK G24) (hB8 : BathOK G8) (hP24 : PairOK G24)
    (hP8 : PairOK G8)
    (r1 : RegionLB G24 0 (1 / 5)) (r2 : RegionLB G24 (1 / 5) (3 / 10)) (r3 : RegionLB G24 (3 / 10) (2 / 5))
    (r4 : RegionLB G8 (2 / 5) (9 / 20)) (r5 : RegionLB G8 (9 / 20) (1 / 2)) :
    δ 3 = 117 / 2192 :=
  le_antisymm Erdos1186Day.erdos_1186.variants.prs_bounds_upper
    (lower_of_parts hS hB24 hB8 hP24 hP8 r1 r2 r3 r4 r5)

end Erdos1186Ex

#print axioms Erdos1186Ex.Wm_eq_Qd
#print axioms Erdos1186Ex.expansion
#print axioms Erdos1186Ex.combine
#print axioms Erdos1186Ex.wm_lower
#print axioms Erdos1186Ex.lower_of_parts
#print axioms Erdos1186Ex.delta3_eq_of_parts
