import Mathlib
import Erdos.Proofs.P1186Ex

/-!
# Erdos 1186 - lane `expair`: `PairOK G` for every well-formed grid `G`

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is
its author's.  This module proves the discrete form of that proof's cell-pair lemma ("Lemma 3") against the shared
interface `Erdos.Proofs.P1186Ex`:

* `pairOK_of_WF : G.WF → PairOK G` (and `pairOK24`, `pairOK8` for the two grids `G24`, `G8` of `P1186ExData`).

**Proof.**  Write `n = 1096 w`, `J_p = ((p-1) w, p w]` for the unit cells and `N_pq = #{(x,y) ∈ J_p × J_q : (x,y) ∈ R_d}`.

1. *Unit-cell counts* (`Npq_bound`): for all `p, q ≥ 1`, `|4 N_pq - w² K4 1096 p q| ≤ 3`.  Indeed, with `m = 2q - p - 1`
   the condition `1 ≤ 2y - x ≤ n` reads `1 ≤ m w + 2b - a + 1 ≤ n` for `x = (p-1) w + a + 1`, `y = (q-1) w + b + 1`,
   `a, b ∈ [0, w)`: it holds for all `w²` pairs if `1 ≤ m ≤ 1094`, for none if `m ≤ -2` or `m ≥ 1097`, and for the four
   remaining values `m ∈ {-1, 0, 1095, 1096}` it cuts the square along a line, leaving `Q(w) = ⌊w²/4⌋` or `w² - Q(w)`
   points (`Qc`, `Qc_eq`; the two lines are exchanged by the point reflection of the square, `Rc_eq`).
2. *Cells* (`sum_cells`): for a well-formed grid the cells `(lo_i w, hi_i w]` partition `[1, n]`, and `φ*` (`sstar w`)
   equals `G.sgn i` on cell `i` (`sstar_cell`), so `Qd (s* σ) = Σ_{i,j} sgn_i sgn_j T_ij` with
   `T_ij = #{(x, y) ∈ S_i × S_j : (x, y) ∈ R_d}`, `S_i` the support of `σ` in cell `i`.
3. *Pair bound* (`pair_term`): with `k_i = |S_i|`, `N_ij = #(R_d ∩ cell_i × cell_j)`, one has `0 ≤ T_ij ≤ min(k_i k_j, N_ij)` and
   `T_ij ≥ k_i k_j - (|cell_i||cell_j| - N_ij)`; summing step 1 over the unit cells of the two cells gives
   `|4 N_ij - w² A4_ij| ≤ 3 len_i len_j`.  This is exactly the claim's max/min bound up to an error `3 len_i len_j / 4`.
4. Summing the errors over all pairs gives `(3/4) · 1096²`, a constant, so `PairOK` holds with `C = 3 · 1096² / 4`.

Nothing here is specific to `G24` or `G8` beyond `G.WF`.
-/

namespace Erdos1186Ex
namespace Pair

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

/-! ## 1. The half-square lattice count `Q(w) = ⌊w²/4⌋` -/

/-- `#{(a, b) ∈ [0, w)² : 2 b + 1 ≤ a}`. -/
def Qc (w : ℕ) : ℕ := ((range w ×ˢ range w).filter fun ab : ℕ × ℕ => 2 * ab.2 + 1 ≤ ab.1).card

/-- `#{(a, b) ∈ [0, w)² : w + a ≤ 2 b}`. -/
def Rc (w : ℕ) : ℕ := ((range w ×ˢ range w).filter fun ab : ℕ × ℕ => w + ab.1 ≤ 2 * ab.2).card

theorem Qc_succ (w : ℕ) : Qc (w + 1) = Qc w + (w + 1) / 2 := by
  unfold Qc
  have h : (range (w + 1) ×ˢ range (w + 1)).filter (fun ab : ℕ × ℕ => 2 * ab.2 + 1 ≤ ab.1) =
      (range w ×ˢ range w).filter (fun ab : ℕ × ℕ => 2 * ab.2 + 1 ≤ ab.1) ∪
        (range ((w + 1) / 2)).image (fun b => (w, b)) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_range, mem_union, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, hb⟩, h⟩
      by_cases haw : a < w
      · left; exact ⟨⟨haw, by omega⟩, h⟩
      · right; exact ⟨b, by omega, by omega, rfl⟩
    · rintro (⟨⟨ha, hb⟩, h⟩ | ⟨b', hb', h1, h2⟩)
      · exact ⟨⟨by omega, by omega⟩, h⟩
      · subst h2; subst h1
        exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [h, card_union_of_disjoint, card_image_of_injective _ (fun b b' hbb => by simpa using hbb), card_range]
  rw [disjoint_left]
  rintro ⟨a, b⟩ h1 h2
  simp only [mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq] at h1 h2
  obtain ⟨b', _, h3, _⟩ := h2
  omega

theorem Qc_eq (w : ℕ) : 4 * Qc w + w % 2 = w * w := by
  induction w with
  | zero => simp [Qc]
  | succ w ih =>
    rw [Qc_succ]
    have h : (w + 1) * (w + 1) = w * w + 2 * w + 1 := by ring
    rw [h]
    generalize w * w = s at *
    omega

theorem Rc_eq (w : ℕ) : Rc w = Qc w := by
  unfold Rc Qc
  refine card_nbij' (fun ab => (w - 1 - ab.1, w - 1 - ab.2)) (fun ab => (w - 1 - ab.1, w - 1 - ab.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    omega
  · rintro ⟨a, b⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    omega
  · rintro ⟨a, b⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    ext <;> simp <;> omega
  · rintro ⟨a, b⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at h ⊢
    ext <;> simp <;> omega


/-! ## 2. Unit-cell pair counts -/

theorem sum_Ioc_shift {M : Type*} [AddCommMonoid M] (c w : ℕ) (f : ℕ → M) :
    ∑ x ∈ Ioc c (c + w), f x = ∑ a ∈ range w, f (c + a + 1) := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [← Nat.add_assoc, Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- `N_pq = #{(x, y) ∈ J_p × J_q : (x, y) ∈ R_d}`, `J_p = ((p-1) w, p w]`. -/
def Npq (w p q : ℕ) : ℤ :=
  ∑ x ∈ Ioc ((p - 1) * w) (p * w), ∑ y ∈ Ioc ((q - 1) * w) (q * w), rdI (nn w) x y

theorem unit_mul (w p : ℕ) (hp : 1 ≤ p) : p * w = (p - 1) * w + w := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  simp [Nat.add_mul]

theorem Npq_eq (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Npq w p q = (((range w ×ˢ range w).filter fun ab : ℕ × ℕ =>
      0 ≤ ((2 * (q : ℤ) - p - 1) * w) + 2 * ab.2 - ab.1 ∧
        ((2 * (q : ℤ) - p - 1) * w) + 2 * ab.2 - ab.1 + 1 ≤ 1096 * w).card : ℤ) := by
  unfold Npq
  rw [unit_mul w p hp, unit_mul w q hq]
  simp_rw [sum_Ioc_shift]
  rw [← sum_product']
  simp only [rdI]
  rw [sum_boole]
  congr 2
  apply filter_congr
  intro ab _
  simp only [nn]
  push_cast [Nat.cast_sub hp, Nat.cast_sub hq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

theorem Npq_full (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (h1 : 1 ≤ 2 * (q : ℤ) - p - 1)
    (h2 : 2 * (q : ℤ) - p - 1 ≤ 1094) : Npq w p q = (w : ℤ) * w := by
  rw [Npq_eq w p q hp hq]
  have e1 : (2 * (q : ℤ) - p - 1) * w ≥ w := by nlinarith [(Nat.cast_nonneg w : (0 : ℤ) ≤ w)]
  have e2 : (2 * (q : ℤ) - p - 1) * w ≤ 1094 * w := by nlinarith [(Nat.cast_nonneg w : (0 : ℤ) ≤ w)]
  generalize (2 * (q : ℤ) - p - 1) * w = D at *
  rw [filter_true_of_mem, card_product, card_range]
  · push_cast; ring
  · rintro ⟨a, b⟩ hab
    simp only [mem_product, mem_range] at hab
    constructor <;> omega

theorem Npq_zero (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (h : 2 * (q : ℤ) - p - 1 ≤ -2 ∨ 1097 ≤ 2 * (q : ℤ) - p - 1) : Npq w p q = 0 := by
  rw [Npq_eq w p q hp hq]
  have hw : (0 : ℤ) ≤ w := Nat.cast_nonneg w
  have e : (2 * (q : ℤ) - p - 1) * w ≤ -2 * w ∨ 1097 * w ≤ (2 * (q : ℤ) - p - 1) * w := by
    rcases h with h | h
    · left; nlinarith
    · right; nlinarith
  generalize (2 * (q : ℤ) - p - 1) * w = D at *
  rw [filter_false_of_mem]
  · simp
  · rintro ⟨a, b⟩ hab
    simp only [mem_product, mem_range] at hab
    omega

/-- `m = 0`: the condition is `a ≤ 2 b`, the complement of `2 b + 1 ≤ a`. -/
theorem Npq_m0 (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 2 * (q : ℤ) - p - 1 = 0) :
    Npq w p q = (w : ℤ) * w - Qc w := by
  rw [Npq_eq w p q hp hq, hm]
  have h := card_filter_add_card_filter_not (s := range w ×ˢ range w)
    (fun ab : ℕ × ℕ => 2 * ab.2 + 1 ≤ ab.1)
  rw [card_product, card_range] at h
  have e : (range w ×ˢ range w).filter (fun ab : ℕ × ℕ =>
      0 ≤ (0 : ℤ) * w + 2 * ab.2 - ab.1 ∧ (0 : ℤ) * w + 2 * ab.2 - ab.1 + 1 ≤ 1096 * w) =
      (range w ×ˢ range w).filter (fun ab : ℕ × ℕ => ¬ (2 * ab.2 + 1 ≤ ab.1)) := by
    apply filter_congr
    rintro ⟨a, b⟩ hab
    simp only [mem_product, mem_range] at hab
    omega
  rw [e]
  unfold Qc
  have h' : ((filter (fun ab : ℕ × ℕ => 2 * ab.2 + 1 ≤ ab.1) (range w ×ˢ range w)).card : ℤ) +
      ((filter (fun ab : ℕ × ℕ => ¬ (2 * ab.2 + 1 ≤ ab.1)) (range w ×ˢ range w)).card : ℤ) = (w : ℤ) * w := by
    exact_mod_cast h
  linarith

/-- `m = 1096`: the condition is `2 b + 1 ≤ a`. -/
theorem Npq_m1096 (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 2 * (q : ℤ) - p - 1 = 1096) :
    Npq w p q = Qc w := by
  rw [Npq_eq w p q hp hq, hm]
  unfold Qc
  congr 2
  apply filter_congr
  rintro ⟨a, b⟩ hab
  simp only [mem_product, mem_range] at hab
  omega

/-- `m = -1`: the condition is `w + a ≤ 2 b`. -/
theorem Npq_mm1 (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 2 * (q : ℤ) - p - 1 = -1) :
    Npq w p q = Qc w := by
  rw [Npq_eq w p q hp hq, hm, ← Rc_eq]
  unfold Rc
  congr 2
  apply filter_congr
  rintro ⟨a, b⟩ hab
  simp only [mem_product, mem_range] at hab
  omega

/-- `m = 1095`: the condition is `2 b + 1 ≤ w + a`, the complement of `w + a ≤ 2 b`. -/
theorem Npq_m1095 (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 2 * (q : ℤ) - p - 1 = 1095) :
    Npq w p q = (w : ℤ) * w - Qc w := by
  rw [Npq_eq w p q hp hq, hm, ← Rc_eq]
  have h := card_filter_add_card_filter_not (s := range w ×ˢ range w)
    (fun ab : ℕ × ℕ => w + ab.1 ≤ 2 * ab.2)
  rw [card_product, card_range] at h
  have e : (range w ×ˢ range w).filter (fun ab : ℕ × ℕ =>
      0 ≤ (1095 : ℤ) * w + 2 * ab.2 - ab.1 ∧ (1095 : ℤ) * w + 2 * ab.2 - ab.1 + 1 ≤ 1096 * w) =
      (range w ×ˢ range w).filter (fun ab : ℕ × ℕ => ¬ (w + ab.1 ≤ 2 * ab.2)) := by
    apply filter_congr
    rintro ⟨a, b⟩ hab
    simp only [mem_product, mem_range] at hab
    omega
  rw [e]
  unfold Rc
  have h' : ((filter (fun ab : ℕ × ℕ => w + ab.1 ≤ 2 * ab.2) (range w ×ˢ range w)).card : ℤ) +
      ((filter (fun ab : ℕ × ℕ => ¬ (w + ab.1 ≤ 2 * ab.2)) (range w ×ˢ range w)).card : ℤ) = (w : ℤ) * w := by
    exact_mod_cast h
  linarith

/-- The unit-cell lattice count against the exact kernel: `|4 N_pq - w² K4 1096 p q| ≤ 3`. -/
theorem Npq_bound (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    |4 * Npq w p q - (w : ℤ) ^ 2 * (K4 1096 p q : ℤ)| ≤ 3 := by
  have hQ := Qc_eq w
  have hQ' : 4 * (Qc w : ℤ) + ((w % 2 : ℕ) : ℤ) = (w : ℤ) * w := by exact_mod_cast hQ
  have hw2 : ((w % 2 : ℕ) : ℤ) ≤ 1 := by have := Nat.mod_lt w (show 2 > 0 by norm_num); omega
  have hw0 : (0 : ℤ) ≤ ((w % 2 : ℕ) : ℤ) := Nat.cast_nonneg _
  by_cases hA : 1 ≤ 2 * (q : ℤ) - p - 1 ∧ 2 * (q : ℤ) - p - 1 ≤ 1094
  · have hK : K4 1096 p q = 4 := by unfold K4; split_ifs <;> omega
    rw [Npq_full w p q hp hq hA.1 hA.2, hK]
    have : 4 * ((w : ℤ) * w) - (w : ℤ) ^ 2 * ((4 : ℕ) : ℤ) = 0 := by push_cast; ring
    rw [this]; norm_num
  by_cases hB : 2 * (q : ℤ) - p - 1 = 0 ∨ 2 * (q : ℤ) - p - 1 = 1095
  · have hK : K4 1096 p q = 3 := by unfold K4; split_ifs <;> omega
    have hN : Npq w p q = (w : ℤ) * w - Qc w := by
      rcases hB with hB | hB
      · exact Npq_m0 w p q hp hq hB
      · exact Npq_m1095 w p q hp hq hB
    rw [hN, hK, abs_le]
    push_cast
    constructor <;> nlinarith
  by_cases hC : 2 * (q : ℤ) - p - 1 = -1 ∨ 2 * (q : ℤ) - p - 1 = 1096
  · have hK : K4 1096 p q = 1 := by unfold K4; split_ifs <;> omega
    have hN : Npq w p q = Qc w := by
      rcases hC with hC | hC
      · exact Npq_mm1 w p q hp hq hC
      · exact Npq_m1096 w p q hp hq hC
    rw [hN, hK, abs_le]
    push_cast
    constructor <;> nlinarith
  · have hK : K4 1096 p q = 0 := by unfold K4; split_ifs <;> omega
    have hN : Npq w p q = 0 := Npq_zero w p q hp hq (by omega)
    rw [hN, hK]
    simp

/-! ## 3. Well-formed grids: the cells partition `[1, n]` and `φ*` is constant on each cell -/

section GridFacts

variable (G : Grid)

theorem lo_zero (hG : G.WF) : G.lo 0 = 0 := by
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.1 hG.1
  simp [Grid.lo, hys]

theorem lo_N (hG : G.WF) : G.lo G.N = 1096 := by
  unfold Grid.lo Grid.N
  rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hG.2.1]
  rfl

theorem pts_pos (hG : G.WF) : 0 < G.pts.length := by
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.1 hG.1
  simp [hys]

theorem lo_lt (hG : G.WF) {i j : ℕ} (hij : i < j) (hj : j ≤ G.N) : G.lo i < G.lo j := by
  have hl := pts_pos G hG
  have hjl : j < G.pts.length := by unfold Grid.N at hj; omega
  have hil : i < G.pts.length := by omega
  unfold Grid.lo
  rw [List.getD_eq_getElem _ _ hil, List.getD_eq_getElem _ _ hjl]
  exact List.pairwise_iff_getElem.1 hG.2.2.1 i j hil hjl hij

theorem lo_mono (hG : G.WF) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ G.N) : G.lo i ≤ G.lo j := by
  rcases Nat.eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (lo_lt G hG h hj).le

theorem hi_eq (i : ℕ) : G.hi i = G.lo (i + 1) := rfl

theorem len_pos (hG : G.WF) {i : ℕ} (hi : i < G.N) : 0 < G.len i := by
  have := lo_lt G hG (show i < i + 1 by omega) hi
  unfold Grid.len
  rw [hi_eq]
  omega

theorem cell_card (i w : ℕ) : (G.cell w i).card = G.len i * w := by
  unfold Grid.cell Grid.len
  rw [Nat.card_Ioc, Nat.sub_mul]

/-- the cells partition `Ioc 0 (lo_m w)`, for `m ≤ N` -/
theorem sum_cells_aux {M : Type*} [AddCommMonoid M] (hG : G.WF) (w : ℕ) (f : ℕ → M) (m : ℕ) (hm : m ≤ G.N) :
    ∑ i ∈ range m, ∑ x ∈ G.cell w i, f x = ∑ x ∈ Ioc 0 (G.lo m * w), f x := by
  induction m with
  | zero => simp [lo_zero G hG]
  | succ m ih =>
    rw [sum_range_succ, ih (by omega)]
    unfold Grid.cell
    rw [hi_eq]
    exact sum_Ioc_consecutive f (Nat.zero_le _) (Nat.mul_le_mul_right w (lo_mono G hG (Nat.le_succ m) hm))

theorem sum_cells {M : Type*} [AddCommMonoid M] (hG : G.WF) (w : ℕ) (f : ℕ → M) :
    ∑ x ∈ Icc 1 (nn w), f x = ∑ i ∈ range G.N, ∑ x ∈ G.cell w i, f x := by
  rw [sum_cells_aux G hG w f G.N le_rfl, lo_N G hG]
  have : Icc 1 (nn w) = Ioc 0 (1096 * w) := by
    ext x; simp only [mem_Icc, mem_Ioc, nn]; omega
  rw [this]

theorem sum_len (hG : G.WF) : ∑ i ∈ range G.N, G.len i = 1096 := by
  have h := sum_cells G hG 1 (fun _ => (1 : ℕ))
  simp only [sum_const, smul_eq_mul, mul_one, Nat.card_Icc] at h
  have h2 : ∀ i ∈ range G.N, (G.cell 1 i).card = G.len i := by
    intro i _
    rw [cell_card G i 1, mul_one]
  rw [sum_congr rfl h2] at h
  simpa [nn] using h.symm

theorem sg_pm (c : ℕ → Bool) (x : ℕ) : sg c x = 1 ∨ sg c x = -1 := by
  unfold sg; split_ifs <;> simp

theorem sgn_pm (i : ℕ) : G.sgn i = 1 ∨ G.sgn i = -1 := sg_pm _ _

/-- `φ*` is the constant `sgn_i` on cell `i`. -/
theorem sstar_cell (hG : G.WF) (w : ℕ) (hw : 1 ≤ w) {i : ℕ} (hi : i < G.N) {x : ℕ} (hx : x ∈ G.cell w i) :
    sstar w x = G.sgn i := by
  unfold Grid.cell at hx
  rw [mem_Ioc, hi_eq] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hlo : G.lo i ≤ (x - 1) / w := by
    rw [Nat.le_div_iff_mul_le (by omega)]; omega
  have hhi : (x - 1) / w < G.lo (i + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  have hc := hG.2.2.2.2.2 i hi ((x - 1) / w) (mem_Ico.2 ⟨hlo, hhi⟩)
  have hck : ck (2 * w) x = c1 (G.lo i / 2 + 1) := by
    rw [← hc]
    unfold ck
    have e1 : x + (2 * w - 1) = (x - 1) + 2 * w := by omega
    rw [e1, Nat.add_div_right _ (by omega : 0 < 2 * w), Nat.div_div_eq_div_mul, mul_comm w 2]
  unfold sstar Grid.sgn sg
  rw [hck]

/-- `Qd (s* σ)` as a sum over ordered pairs of cells. -/
theorem Qd_cells (hG : G.WF) (w : ℕ) (hw : 1 ≤ w) (σ : ℕ → ℤ) :
    Qd (nn w) (fun x => sstar w x * σ x) =
      ∑ i ∈ range G.N, ∑ j ∈ range G.N, G.sgn i * G.sgn j *
        ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y := by
  unfold Qd
  rw [sum_cells G hG w]
  have step : ∀ i ∈ range G.N,
      ∑ x ∈ G.cell w i, ∑ y ∈ Icc 1 (nn w), rdI (nn w) x y * (sstar w x * σ x) * (sstar w y * σ y)
      = ∑ j ∈ range G.N, G.sgn i * G.sgn j *
          ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y := by
    intro i hi
    rw [mem_range] at hi
    calc ∑ x ∈ G.cell w i, ∑ y ∈ Icc 1 (nn w), rdI (nn w) x y * (sstar w x * σ x) * (sstar w y * σ y)
        = ∑ x ∈ G.cell w i, ∑ j ∈ range G.N, ∑ y ∈ G.cell w j,
            rdI (nn w) x y * (sstar w x * σ x) * (sstar w y * σ y) := by
          apply sum_congr rfl; intro x _; exact sum_cells G hG w _
      _ = ∑ x ∈ G.cell w i, ∑ j ∈ range G.N, ∑ y ∈ G.cell w j,
            G.sgn i * G.sgn j * (rdI (nn w) x y * σ x * σ y) := by
          apply sum_congr rfl; intro x hx
          apply sum_congr rfl; intro j hj
          rw [mem_range] at hj
          apply sum_congr rfl; intro y hy
          rw [sstar_cell G hG w hw hi hx, sstar_cell G hG w hw hj hy]; ring
      _ = ∑ j ∈ range G.N, ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j,
            G.sgn i * G.sgn j * (rdI (nn w) x y * σ x * σ y) := sum_comm
      _ = _ := by
          apply sum_congr rfl; intro j _
          simp only [mul_sum]
  rw [sum_congr rfl step]

end GridFacts

/-! ## 4. The max/min counting bound on one cell pair -/

theorem rdI_01 (n x y : ℕ) : rdI n x y = 0 ∨ rdI n x y = 1 := by
  unfold rdI; split_ifs <;> simp

theorem ind_aux (r a b : ℤ) (hr : r = 0 ∨ r = 1) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    0 ≤ r * a * b ∧ r * a * b ≤ a * b ∧ r * a * b ≤ r ∧ a * b - 1 + r ≤ r * a * b := by
  rcases hr with rfl | rfl <;> rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

/-- For `0/1` indicators: `0 ≤ T ≤ min(k_A k_B, N)` and `T ≥ k_A k_B - (|A||B| - N)`. -/
theorem pair_int (A B : Finset ℕ) (σ : ℕ → ℤ) (hσ : IsInd σ) (n : ℕ) :
    0 ≤ ∑ x ∈ A, ∑ y ∈ B, rdI n x y * σ x * σ y ∧
    ∑ x ∈ A, ∑ y ∈ B, rdI n x y * σ x * σ y ≤ (∑ x ∈ A, σ x) * (∑ y ∈ B, σ y) ∧
    ∑ x ∈ A, ∑ y ∈ B, rdI n x y * σ x * σ y ≤ ∑ x ∈ A, ∑ y ∈ B, rdI n x y ∧
    (∑ x ∈ A, σ x) * (∑ y ∈ B, σ y) - (A.card : ℤ) * B.card + ∑ x ∈ A, ∑ y ∈ B, rdI n x y
      ≤ ∑ x ∈ A, ∑ y ∈ B, rdI n x y * σ x * σ y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply sum_nonneg; intro x _; apply sum_nonneg; intro y _
    exact (ind_aux _ _ _ (rdI_01 n x y) (hσ x) (hσ y)).1
  · rw [sum_mul_sum]
    apply sum_le_sum; intro x _; apply sum_le_sum; intro y _
    exact (ind_aux _ _ _ (rdI_01 n x y) (hσ x) (hσ y)).2.1
  · apply sum_le_sum; intro x _; apply sum_le_sum; intro y _
    exact (ind_aux _ _ _ (rdI_01 n x y) (hσ x) (hσ y)).2.2.1
  · have h1 : ∑ x ∈ A, ∑ y ∈ B, (σ x * σ y - 1 + rdI n x y) ≤ ∑ x ∈ A, ∑ y ∈ B, rdI n x y * σ x * σ y := by
      apply sum_le_sum; intro x _; apply sum_le_sum; intro y _
      exact (ind_aux _ _ _ (rdI_01 n x y) (hσ x) (hσ y)).2.2.2
    have h2 : ∑ x ∈ A, ∑ y ∈ B, (σ x * σ y - 1 + rdI n x y) =
        (∑ x ∈ A, σ x) * (∑ y ∈ B, σ y) - (A.card : ℤ) * B.card + ∑ x ∈ A, ∑ y ∈ B, rdI n x y := by
      simp only [sum_add_distrib, sum_sub_distrib, sum_mul_sum, sum_const]
      simp
    linarith

/-! ## 5. Unit cells inside a cell: `N_ij` against `A4_ij` -/

theorem sum_cell_units {M : Type*} [AddCommMonoid M] (f : ℕ → M) (lo hi w : ℕ) (h : lo ≤ hi) :
    ∑ x ∈ Ioc (lo * w) (hi * w), f x = ∑ p ∈ Ioc lo hi, ∑ x ∈ Ioc ((p - 1) * w) (p * w), f x := by
  induction hi, h using Nat.le_induction with
  | base => simp
  | succ hi h ih =>
    rw [sum_Ioc_succ_top h, ← ih,
      ← sum_Ioc_consecutive f (Nat.mul_le_mul_right w h) (Nat.mul_le_mul_right w (Nat.le_succ hi))]
    simp

section CellPair

variable (G : Grid)

theorem Nc_unit (hG : G.WF) (w : ℕ) {i j : ℕ} (hi : i < G.N) (hj : j < G.N) :
    ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y =
      ∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j), Npq w p q := by
  have hi' : G.lo i ≤ G.hi i := by
    have := len_pos G hG hi; unfold Grid.len at this; omega
  have hj' : G.lo j ≤ G.hi j := by
    have := len_pos G hG hj; unfold Grid.len at this; omega
  unfold Grid.cell
  rw [sum_cell_units _ _ _ _ hi']
  apply sum_congr rfl
  intro p _
  have : ∀ x ∈ Ioc ((p - 1) * w) (p * w), ∑ y ∈ Ioc (G.lo j * w) (G.hi j * w), rdI (nn w) x y =
      ∑ q ∈ Ioc (G.lo j) (G.hi j), ∑ y ∈ Ioc ((q - 1) * w) (q * w), rdI (nn w) x y := by
    intro x _
    exact sum_cell_units _ _ _ _ hj'
  rw [sum_congr rfl this, sum_comm]
  rfl

theorem Nc_bound (hG : G.WF) (w : ℕ) {i j : ℕ} (hi : i < G.N) (hj : j < G.N) :
    |4 * (∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y) - (w : ℤ) ^ 2 * (G.A4 i j : ℤ)|
      ≤ 3 * ((G.len i : ℤ) * G.len j) := by
  have e : 4 * (∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y) - (w : ℤ) ^ 2 * (G.A4 i j : ℤ) =
      ∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j),
        (4 * Npq w p q - (w : ℤ) ^ 2 * (K4 1096 p q : ℤ)) := by
    rw [Nc_unit G hG w hi hj]
    unfold Grid.A4
    push_cast
    simp only [mul_sum, ← sum_sub_distrib]
  rw [e]
  calc |∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j),
          (4 * Npq w p q - (w : ℤ) ^ 2 * (K4 1096 p q : ℤ))|
      ≤ ∑ p ∈ Ioc (G.lo i) (G.hi i), |∑ q ∈ Ioc (G.lo j) (G.hi j),
          (4 * Npq w p q - (w : ℤ) ^ 2 * (K4 1096 p q : ℤ))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j),
          |(4 * Npq w p q - (w : ℤ) ^ 2 * (K4 1096 p q : ℤ))| := by
        apply sum_le_sum; intro p _; exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j), (3 : ℤ) := by
        apply sum_le_sum; intro p hp
        apply sum_le_sum; intro q hq
        rw [mem_Ioc] at hp hq
        exact Npq_bound w p q (by omega) (by omega)
    _ = 3 * ((G.len i : ℤ) * G.len j) := by
        simp only [sum_const, Nat.card_Ioc]
        unfold Grid.len
        simp
        ring

end CellPair

/-! ## 6. One ordered pair of cells, then the sum -/

section Final

variable (G : Grid)

theorem pair_term (hG : G.WF) (w : ℕ) (hw : 1 ≤ w) (σ : ℕ → ℤ) (hσ : IsInd σ) {i j : ℕ}
    (hi : i < G.N) (hj : j < G.N) :
    (nn w : ℝ) ^ 2 * G.pterm i j (G.yv w σ i) (G.yv w σ j) ≤
      ((G.sgn i * G.sgn j * ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y : ℤ) : ℝ)
        + (3 / 4 : ℝ) * ((G.len i : ℝ) * G.len j) := by
  obtain ⟨hTa, hTb, hTc, hTd⟩ := pair_int (G.cell w i) (G.cell w j) σ hσ (nn w)
  have hNb := Nc_bound G hG w hi hj
  rw [cell_card, cell_card] at hTd
  have hLi : (0 : ℝ) < G.len i := by exact_mod_cast len_pos G hG hi
  have hLj : (0 : ℝ) < G.len j := by exact_mod_cast len_pos G hG hj
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hyi : G.yv w σ i = ((∑ x ∈ G.cell w i, σ x : ℤ) : ℝ) / ((G.len i * w : ℕ) : ℝ) := rfl
  have hyj : G.yv w σ j = ((∑ y ∈ G.cell w j, σ y : ℤ) : ℝ) / ((G.len j * w : ℕ) : ℝ) := rfl
  have hnn : (nn w : ℝ) = 1096 * w := by simp [nn]
  have hwi : ((G.wt i : ℚ) : ℝ) = (G.len i : ℝ) / 1096 := by simp [Grid.wt]
  have hwj : ((G.wt j : ℚ) : ℝ) = (G.len j : ℝ) / 1096 := by simp [Grid.wt]
  unfold Grid.pterm
  dsimp only
  rw [hyi, hyj]
  generalize ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y = T at *
  generalize ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y = Nc at *
  generalize ∑ x ∈ G.cell w i, σ x = ki at *
  generalize ∑ y ∈ G.cell w j, σ y = kj at *
  have hU : (nn w : ℝ) ^ 2 * (((G.wt i : ℚ) : ℝ) * ((G.wt j : ℚ) : ℝ) *
      ((ki : ℝ) / ((G.len i * w : ℕ) : ℝ)) * ((kj : ℝ) / ((G.len j * w : ℕ) : ℝ))) = (ki : ℝ) * kj := by
    rw [hnn, hwi, hwj]; push_cast; field_simp
  have hV : (nn w : ℝ) ^ 2 * ((G.A4 i j : ℝ) / (4 * 1096 ^ 2)) = (w : ℝ) ^ 2 * (G.A4 i j : ℝ) / 4 := by
    rw [hnn]; field_simp
  have hZ : (nn w : ℝ) ^ 2 * (((G.wt i : ℚ) : ℝ) * ((G.wt j : ℚ) : ℝ)) =
      (w : ℝ) ^ 2 * ((G.len i : ℝ) * G.len j) := by
    rw [hnn, hwi, hwj]; field_simp
  have hn0 : (0 : ℝ) ≤ (nn w : ℝ) ^ 2 := by positivity
  have hTa' : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTa
  have hTb' : (T : ℝ) ≤ (ki : ℝ) * kj := by exact_mod_cast hTb
  have hTc' : (T : ℝ) ≤ (Nc : ℝ) := by exact_mod_cast hTc
  have hTd' : (ki : ℝ) * kj - (G.len i : ℝ) * w * ((G.len j : ℝ) * w) + Nc ≤ T := by
    exact_mod_cast hTd
  have hNb' := abs_le.1 hNb
  have hNb1 : 4 * (Nc : ℝ) - (w : ℝ) ^ 2 * (G.A4 i j : ℝ) ≤ 3 * ((G.len i : ℝ) * G.len j) := by
    exact_mod_cast hNb'.2
  have hNb2 : -(3 * ((G.len i : ℝ) * G.len j)) ≤ 4 * (Nc : ℝ) - (w : ℝ) ^ 2 * (G.A4 i j : ℝ) := by
    exact_mod_cast hNb'.1
  have hLL : (0 : ℝ) ≤ (G.len i : ℝ) * G.len j := by positivity
  split_ifs with hs
  · rw [hs, one_mul, mul_max_of_nonneg _ _ hn0]
    apply max_le
    · linarith
    · have : (nn w : ℝ) ^ 2 * (((G.wt i : ℚ) : ℝ) * ((G.wt j : ℚ) : ℝ) *
          ((ki : ℝ) / ((G.len i * w : ℕ) : ℝ)) * ((kj : ℝ) / ((G.len j * w : ℕ) : ℝ)) -
          (((G.wt i : ℚ) : ℝ) * ((G.wt j : ℚ) : ℝ) - (G.A4 i j : ℝ) / (4 * 1096 ^ 2))) =
          (ki : ℝ) * kj - (w : ℝ) ^ 2 * ((G.len i : ℝ) * G.len j) + (w : ℝ) ^ 2 * (G.A4 i j : ℝ) / 4 := by
        linear_combination hU - hZ + hV
      rw [this]
      linarith
  · have hs' : G.sgn i * G.sgn j = -1 := by
      have key : G.sgn i * G.sgn j = 1 ∨ G.sgn i * G.sgn j = -1 := by
        rcases sgn_pm G i with h | h <;> rcases sgn_pm G j with h' | h' <;> norm_num [h, h']
      exact key.resolve_left hs
    rw [hs', mul_max_of_nonneg _ _ hn0]
    apply max_le
    · have : (nn w : ℝ) ^ 2 * (-((G.A4 i j : ℝ) / (4 * 1096 ^ 2))) = -((w : ℝ) ^ 2 * (G.A4 i j : ℝ) / 4) := by
        linear_combination (-1 : ℝ) * hV
      rw [this]; push_cast; linarith
    · have : (nn w : ℝ) ^ 2 * (-(((G.wt i : ℚ) : ℝ) * ((G.wt j : ℚ) : ℝ) *
          ((ki : ℝ) / ((G.len i * w : ℕ) : ℝ)) * ((kj : ℝ) / ((G.len j * w : ℕ) : ℝ)))) = -((ki : ℝ) * kj) := by
        linear_combination (-1 : ℝ) * hU
      rw [this]; push_cast; linarith

end Final

theorem G24_WF : G24.WF := by decide +kernel

theorem G8_WF : G8.WF := by decide +kernel

/-! Sanity checks of the unit-cell counts (kernel-evaluated) against `Qc`, `K4`. -/
example : Npq 2 1 1 = 3 ∧ Npq 3 1 1 = 7 ∧ Npq 3 1 2 = 9 ∧ Npq 3 2 1 = 2 := by decide +kernel
example : Qc 5 = 6 ∧ Qc 6 = 9 := by decide +kernel

end Pair

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2 Pair

/-- **Lemma 3 (cell pairs), discrete, for every well-formed grid.**  `PairOK G` holds with `C = 3 · 1096² / 4`. -/
theorem pairOK_of_WF (G : Grid) (hG : G.WF) : PairOK G := by
  refine ⟨3 * 1096 ^ 2 / 4, fun w hw σ hσ => ?_⟩
  have hL : ∑ i ∈ range G.N, (G.len i : ℝ) = 1096 := by exact_mod_cast sum_len G hG
  have hE : ∑ i ∈ range G.N, ∑ j ∈ range G.N, (3 / 4 : ℝ) * ((G.len i : ℝ) * G.len j) = 3 * 1096 ^ 2 / 4 := by
    have : ∑ i ∈ range G.N, ∑ j ∈ range G.N, (3 / 4 : ℝ) * ((G.len i : ℝ) * G.len j) =
        (3 / 4 : ℝ) * ((∑ i ∈ range G.N, (G.len i : ℝ)) * ∑ j ∈ range G.N, (G.len j : ℝ)) := by
      rw [sum_mul_sum, mul_sum]
      apply sum_congr rfl; intro i _
      rw [mul_sum]
    rw [this, hL]; ring
  have hsum : (nn w : ℝ) ^ 2 * ∑ i ∈ range G.N, ∑ j ∈ range G.N, G.pterm i j (G.yv w σ i) (G.yv w σ j) ≤
      ∑ i ∈ range G.N, ∑ j ∈ range G.N,
        (((G.sgn i * G.sgn j * ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y : ℤ)) : ℝ) +
      ∑ i ∈ range G.N, ∑ j ∈ range G.N, (3 / 4 : ℝ) * ((G.len i : ℝ) * G.len j) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum; intro i hi
    rw [mem_range] at hi
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum; intro j hj
    rw [mem_range] at hj
    exact pair_term G hG w hw σ hσ hi hj
  have hQ : ((Qd (nn w) (fun x => sstar w x * σ x) : ℤ) : ℝ) =
      ∑ i ∈ range G.N, ∑ j ∈ range G.N,
        (((G.sgn i * G.sgn j * ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y : ℤ)) : ℝ) := by
    rw [Qd_cells G hG w hw σ]
    simp only [Int.cast_sum]
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  rw [hQ]
  rw [hE] at hsum
  nlinarith

/-- `PairOK` for the 130-cell grid `G24`. -/
theorem pairOK24 : PairOK G24 := pairOK_of_WF G24 Pair.G24_WF

/-- `PairOK` for the 146-cell grid `G8`. -/
theorem pairOK8 : PairOK G8 := pairOK_of_WF G8 Pair.G8_WF

#print axioms Npq_bound
#print axioms pair_term
#print axioms pairOK_of_WF
#print axioms pairOK24
#print axioms pairOK8

end Erdos1186Ex
