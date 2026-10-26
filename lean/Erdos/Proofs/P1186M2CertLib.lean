import Mathlib
import Erdos.Proofs.P1186M2
import Erdos.Proofs.P1186Cert128Lib

/-!
# Erdos 1186 - kernel-checkable Shor + triangle-cut certificates for MODEL2 (night 2, lane lean1186d)

Generic library behind `P1186M2Cert64*.lean`, `P1186M2Cert128*.lean`.  No numbers live here; they are in the
generated table modules (`problems/1186/lean_cert2.py`).

**What is certified.**  `Erdos1186Night2M2.CubeLB L σ` (interface `P1186M2.lean`): `xᵀ C x ≥ -σ` on the cube,
`8 C = K4 + K4ᵀ + 8 I + 2 J` (`C8`).  The certificate is a nonnegative integer vector `dn`, a list of triangle cuts
`(i, j, k, s₁, s₂, s₃, mn)` (`mn ≥ 0`, `s₁ s₂ s₃ = 1`, signs `±1`, the cut being
`s₁ x_i x_j + s₂ x_i x_k + s₃ x_j x_k ≥ -1` on `[-1,1]³`) and the integer matrix
`N = 2Q·C8 + 16 diag(dn) - 8 Σ_t mn_t σ_t` (`σ_t` = the signs on the six symmetric off-diagonal entries of the triple),
which must be positive semidefinite.  Then `16 Q·xᵀCx + 16 Σ dn x² - 16 Σ mn·cut ≥ 0`, so `xᵀCx ≥ -(Σ dn + Σ mn)/Q`.

**What the kernel checks** (all by `decide +kernel`, no `native_decide`):
1. every cut is well formed (`Cut.ok`), `dn ≥ 0`, list lengths;
2. `accumulate cuts = acc`: for each row `a` one packed integer `acc_a = Σ_t packCut t a` (the row-`a` contributions of
   all cuts, packed as digits in base `2^32`);
3. LINK, per row `a`: the table row `N_a` equals `2Q·C8 + 16 dn - 8·(cut part)`.  The cut part is never summed entry by
   entry: `Σ_b (N_ab - base_ab) 2^{32 b} + 8·acc_a = 0` together with `|N_ab - base_ab| + 48·Σ mn < 2^32` gives, digit by digit,
   `N_ab - base_ab = -8·rowvec_ab` (injectivity of the base-`2^32` expansion);
4. DOMINANCE: an integer approximate Cholesky factor `C` (rows `c_i`), `E = S N - C Cᵀ`, every row of `E` diagonally
   dominant.  Then `S xᵀNx = Σ_k (Cᵀx)_k² + xᵀEx ≥ 0`.
-/

namespace Erdos1186Night2M2

open Finset Erdos1186Night2

/-! ### Triangle cuts -/

/-- A triangle cut on the triple `(i, j, k)` with multiplier `mn` (an integer, the multiplier is `mn / Q`);
`s1, s2, s3` are the signs of the pairs `(i, j)`, `(i, k)`, `(j, k)`. -/
structure Cut where
  i : ℕ
  j : ℕ
  k : ℕ
  s1 : ℤ
  s2 : ℤ
  s3 : ℤ
  mn : ℤ

/-- Well-formedness (executable): indices in `1..L`, signs `±1` with product `+1`, `mn ≥ 0`. -/
def Cut.ok (L : ℕ) (t : Cut) : Bool :=
  decide (1 ≤ t.i ∧ t.i ≤ L ∧ 1 ≤ t.j ∧ t.j ≤ L ∧ 1 ≤ t.k ∧ t.k ≤ L ∧
    (t.s1 = 1 ∨ t.s1 = -1) ∧ (t.s2 = 1 ∨ t.s2 = -1) ∧ (t.s3 = 1 ∨ t.s3 = -1) ∧
    t.s1 * t.s2 * t.s3 = 1 ∧ 0 ≤ t.mn)

/-- The cut polynomial `s₁ x_i x_j + s₂ x_i x_k + s₃ x_j x_k`. -/
noncomputable def cutval (t : Cut) (x : ℕ → ℝ) : ℝ :=
  (t.s1 : ℝ) * x t.i * x t.j + (t.s2 : ℝ) * x t.i * x t.k + (t.s3 : ℝ) * x t.j * x t.k

/-- The triangle inequality on the cube (multilinear, so a statement about the 8 vertices; here by
`(1 ± u)(1 ± v)(1 ± w) ≥ 0`). -/
theorem cutval_ge (s1 s2 s3 : ℤ) (h1 : s1 = 1 ∨ s1 = -1) (h2 : s2 = 1 ∨ s2 = -1) (h3 : s3 = 1 ∨ s3 = -1)
    (hp : s1 * s2 * s3 = 1) (u v w : ℝ) (hu : |u| ≤ 1) (hv : |v| ≤ 1) (hw : |w| ≤ 1) :
    -1 ≤ (s1 : ℝ) * u * v + (s2 : ℝ) * u * w + (s3 : ℝ) * v * w := by
  rw [abs_le] at hu hv hw
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hw1, hw2⟩ := hw
  have a1 : 0 ≤ 1 + u := by linarith
  have a2 : 0 ≤ 1 - u := by linarith
  have b1 : 0 ≤ 1 + v := by linarith
  have b2 : 0 ≤ 1 - v := by linarith
  have c1 : 0 ≤ 1 + w := by linarith
  have c2 : 0 ≤ 1 - w := by linarith
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    first | (exfalso; revert hp; norm_num; done) | push_cast
  · nlinarith [mul_nonneg (mul_nonneg a1 b1) c1, mul_nonneg (mul_nonneg a2 b2) c2]
  · nlinarith [mul_nonneg (mul_nonneg a1 b1) c2, mul_nonneg (mul_nonneg a2 b2) c1]
  · nlinarith [mul_nonneg (mul_nonneg a1 b2) c1, mul_nonneg (mul_nonneg a2 b1) c2]
  · nlinarith [mul_nonneg (mul_nonneg a2 b1) c1, mul_nonneg (mul_nonneg a1 b2) c2]

/-! ### The cut part of the matrix -/

/-- Kronecker delta on `ℕ`, valued in `ℤ`. -/
def dl (m n : ℕ) : ℤ := if m = n then 1 else 0

/-- Entry `(a, b)` of `Σ`-contribution of ONE cut: `mn · σ_t` on the six symmetric off-diagonal entries. -/
def ccm (t : Cut) (a b : ℕ) : ℤ :=
  t.mn * (t.s1 * (dl a t.i * dl b t.j + dl a t.j * dl b t.i)
        + t.s2 * (dl a t.i * dl b t.k + dl a t.k * dl b t.i)
        + t.s3 * (dl a t.j * dl b t.k + dl a t.k * dl b t.j))

/-- Entry `(a, b)` of `Σ_t mn_t σ_t`. -/
def rowvec (cuts : List Cut) (a b : ℕ) : ℤ := (cuts.map (fun t => ccm t a b)).sum

theorem ccm_comm (t : Cut) (a b : ℕ) : ccm t a b = ccm t b a := by
  unfold ccm; ring

theorem rowvec_comm (cuts : List Cut) (a b : ℕ) : rowvec cuts a b = rowvec cuts b a := by
  unfold rowvec; simp only [ccm_comm _ a b]

theorem sum_dl_dl (L p q : ℕ) (hp : p ∈ Icc 1 L) (hq : q ∈ Icc 1 L) (f : ℕ → ℕ → ℝ) :
    ∑ a ∈ Icc 1 L, ∑ b ∈ Icc 1 L, ((dl a p : ℤ) : ℝ) * ((dl b q : ℤ) : ℝ) * f a b = f p q := by
  have : ∀ a b, ((dl a p : ℤ) : ℝ) * ((dl b q : ℤ) : ℝ) * f a b
      = if a = p then (if b = q then f a b else 0) else 0 := by
    intro a b
    unfold dl
    by_cases h1 : a = p <;> by_cases h2 : b = q <;> simp [h1, h2]
  simp only [this]
  rw [Finset.sum_eq_single p]
  · simp [hq]
  · intro a _ h; simp [h]
  · intro h; exact absurd hp h

theorem sum_dl (L q : ℕ) (hq : q ∈ Icc 1 L) (g : ℕ → ℤ) :
    ∑ b ∈ Icc 1 L, dl b q * g b = g q := by
  have : ∀ b, dl b q * g b = if b = q then g b else 0 := by
    intro b; unfold dl; by_cases h : b = q <;> simp [h]
  simp only [this]
  rw [Finset.sum_eq_single q]
  · simp
  · intro b _ h; simp [h]
  · intro h; exact absurd hq h

/-- The quadratic form of one cut's matrix: `Σ_{ab} ccm t a b x_a x_b = 2·mn·cutval`. -/
theorem quad_ccm (L : ℕ) (t : Cut) (hi : t.i ∈ Icc 1 L) (hj : t.j ∈ Icc 1 L) (hk : t.k ∈ Icc 1 L)
    (x : ℕ → ℝ) :
    ∑ a ∈ Icc 1 L, ∑ b ∈ Icc 1 L, ((ccm t a b : ℤ) : ℝ) * x a * x b = 2 * (t.mn : ℝ) * cutval t x := by
  have key : ∀ a b, ((ccm t a b : ℤ) : ℝ) * x a * x b =
      (t.mn : ℝ) * t.s1 * (((dl a t.i : ℤ) : ℝ) * ((dl b t.j : ℤ) : ℝ) * (x a * x b))
      + (t.mn : ℝ) * t.s1 * (((dl a t.j : ℤ) : ℝ) * ((dl b t.i : ℤ) : ℝ) * (x a * x b))
      + (t.mn : ℝ) * t.s2 * (((dl a t.i : ℤ) : ℝ) * ((dl b t.k : ℤ) : ℝ) * (x a * x b))
      + (t.mn : ℝ) * t.s2 * (((dl a t.k : ℤ) : ℝ) * ((dl b t.i : ℤ) : ℝ) * (x a * x b))
      + (t.mn : ℝ) * t.s3 * (((dl a t.j : ℤ) : ℝ) * ((dl b t.k : ℤ) : ℝ) * (x a * x b))
      + (t.mn : ℝ) * t.s3 * (((dl a t.k : ℤ) : ℝ) * ((dl b t.j : ℤ) : ℝ) * (x a * x b)) := by
    intro a b
    unfold ccm
    push_cast
    ring
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_dl_dl L _ _ hi hj (fun a b => x a * x b), sum_dl_dl L _ _ hj hi (fun a b => x a * x b),
    sum_dl_dl L _ _ hi hk (fun a b => x a * x b), sum_dl_dl L _ _ hk hi (fun a b => x a * x b),
    sum_dl_dl L _ _ hj hk (fun a b => x a * x b), sum_dl_dl L _ _ hk hj (fun a b => x a * x b)]
  unfold cutval
  ring

theorem Cut.ok_idx {L : ℕ} {t : Cut} (h : Cut.ok L t = true) :
    t.i ∈ Icc 1 L ∧ t.j ∈ Icc 1 L ∧ t.k ∈ Icc 1 L := by
  have h' := of_decide_eq_true h
  simp only [Finset.mem_Icc]
  omega

theorem Cut.ok_sign {L : ℕ} {t : Cut} (h : Cut.ok L t = true) :
    (t.s1 = 1 ∨ t.s1 = -1) ∧ (t.s2 = 1 ∨ t.s2 = -1) ∧ (t.s3 = 1 ∨ t.s3 = -1) ∧ t.s1 * t.s2 * t.s3 = 1 ∧
      0 ≤ t.mn := by
  have h' := of_decide_eq_true h
  exact ⟨h'.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.2.2.2.2⟩

/-- `Σ_{ab} (Σ_t mn_t σ_t)_{ab} x_a x_b = 2 Σ_t mn_t cutval_t`. -/
theorem quad_rowvec (L : ℕ) (x : ℕ → ℝ) : ∀ cuts : List Cut, (∀ t ∈ cuts, Cut.ok L t = true) →
    ∑ a ∈ Icc 1 L, ∑ b ∈ Icc 1 L, ((rowvec cuts a b : ℤ) : ℝ) * x a * x b
      = 2 * (cuts.map (fun t => (t.mn : ℝ) * cutval t x)).sum
  | [], _ => by simp [rowvec]
  | t :: ts, h => by
      have ht := h t (by simp)
      have hts : ∀ s ∈ ts, Cut.ok L s = true := fun s hs => h s (List.mem_cons_of_mem _ hs)
      have ih := quad_rowvec L x ts hts
      obtain ⟨hi, hj, hk⟩ := Cut.ok_idx ht
      have hq := quad_ccm L t hi hj hk x
      have e : ∀ a b, ((rowvec (t :: ts) a b : ℤ) : ℝ) * x a * x b =
          ((ccm t a b : ℤ) : ℝ) * x a * x b + ((rowvec ts a b : ℤ) : ℝ) * x a * x b := by
        intro a b
        simp only [rowvec, List.map_cons, List.sum_cons]
        push_cast
        ring
      simp only [e, Finset.sum_add_distrib]
      rw [hq, ih]
      simp only [List.map_cons, List.sum_cons]
      ring

/-! ### Packing the cut part: digits in base `2^32` -/

/-- `2^(32 b)` as an integer (`Nat.pow`, kernel-accelerated). -/
def Bp (b : ℕ) : ℤ := ((2 ^ (32 * b) : ℕ) : ℤ)

/-- Contribution of ONE cut to the packed row `a`: `Σ_b ccm t a b · 2^(32 b)`. -/
def packCut (t : Cut) (a : ℕ) : ℤ :=
  (if a = t.i then t.mn * (t.s1 * Bp t.j + t.s2 * Bp t.k) else 0)
  + (if a = t.j then t.mn * (t.s1 * Bp t.i + t.s3 * Bp t.k) else 0)
  + (if a = t.k then t.mn * (t.s2 * Bp t.i + t.s3 * Bp t.j) else 0)

theorem pack_ccm (L : ℕ) (t : Cut) (a : ℕ) (hi : t.i ∈ Icc 1 L) (hj : t.j ∈ Icc 1 L) (hk : t.k ∈ Icc 1 L) :
    ∑ b ∈ Icc 1 L, ccm t a b * Bp b = packCut t a := by
  have key : ∀ b, ccm t a b * Bp b =
      t.mn * t.s1 * dl a t.i * (dl b t.j * Bp b) + t.mn * t.s1 * dl a t.j * (dl b t.i * Bp b)
      + t.mn * t.s2 * dl a t.i * (dl b t.k * Bp b) + t.mn * t.s2 * dl a t.k * (dl b t.i * Bp b)
      + t.mn * t.s3 * dl a t.j * (dl b t.k * Bp b) + t.mn * t.s3 * dl a t.k * (dl b t.j * Bp b) := by
    intro b; unfold ccm; ring
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_dl L _ hj Bp, sum_dl L _ hi Bp, sum_dl L _ hk Bp]
  unfold packCut dl
  split_ifs <;> ring

theorem pack_rowvec (L : ℕ) (a : ℕ) : ∀ cuts : List Cut, (∀ t ∈ cuts, Cut.ok L t = true) →
    ∑ b ∈ Icc 1 L, rowvec cuts a b * Bp b = (cuts.map (fun t => packCut t a)).sum
  | [], _ => by simp [rowvec]
  | t :: ts, h => by
      have ht := h t (by simp)
      have hts : ∀ s ∈ ts, Cut.ok L s = true := fun s hs => h s (List.mem_cons_of_mem _ hs)
      have ih := pack_rowvec L a ts hts
      obtain ⟨hi, hj, hk⟩ := Cut.ok_idx ht
      have hq := pack_ccm L t a hi hj hk
      have e : ∀ b, rowvec (t :: ts) a b * Bp b = ccm t a b * Bp b + rowvec ts a b * Bp b := by
        intro b
        simp only [rowvec, List.map_cons, List.sum_cons]
        ring
      simp only [e, Finset.sum_add_distrib]
      rw [hq, ih]
      simp only [List.map_cons, List.sum_cons]

theorem Bp_eq (b : ℕ) : Bp b = ((2 : ℤ) ^ 32) ^ b := by
  unfold Bp
  push_cast
  rw [pow_mul]
  norm_num

theorem digits_zero_range : ∀ (n : ℕ) (f : ℕ → ℤ), (∀ t < n, |f t| < 2 ^ 32) →
    ∑ t ∈ range n, f t * ((2 : ℤ) ^ 32) ^ t = 0 → ∀ t < n, f t = 0
  | 0, f, _, _ => fun t ht => absurd ht (Nat.not_lt_zero _)
  | n + 1, f, hf, hs => by
    rw [Finset.sum_range_succ'] at hs
    have e : ∑ t ∈ range n, f (t + 1) * ((2 : ℤ) ^ 32) ^ (t + 1)
        = (2 ^ 32) * ∑ t ∈ range n, f (t + 1) * ((2 : ℤ) ^ 32) ^ t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [e] at hs
    simp only [pow_zero, mul_one] at hs
    have hdvd : ((2 : ℤ) ^ 32) ∣ f 0 := ⟨-(∑ t ∈ range n, f (t + 1) * ((2 : ℤ) ^ 32) ^ t), by linarith⟩
    have h0 : f 0 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (hf 0 (Nat.succ_pos n))
    rw [h0, add_zero] at hs
    have hrest : ∑ t ∈ range n, f (t + 1) * ((2 : ℤ) ^ 32) ^ t = 0 := by
      rcases mul_eq_zero.mp hs with h | h
      · norm_num at h
      · exact h
    have ih := digits_zero_range n (fun t => f (t + 1)) (fun t ht => hf (t + 1) (by omega)) hrest
    intro t ht
    cases t with
    | zero => exact h0
    | succ u => exact ih u (by omega)

/-- Injectivity of the base-`2^32` expansion on bounded digits. -/
theorem digits_zero (L : ℕ) (e : ℕ → ℤ) (he : ∀ b ∈ Icc 1 L, |e b| < 2 ^ 32)
    (hs : ∑ b ∈ Icc 1 L, e b * Bp b = 0) : ∀ b ∈ Icc 1 L, e b = 0 := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel] at hs
  have e2 : ∑ t ∈ range L, e (1 + t) * Bp (1 + t)
      = (2 ^ 32) * ∑ t ∈ range L, e (1 + t) * ((2 : ℤ) ^ 32) ^ t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Bp_eq, pow_add]
    ring
  rw [e2] at hs
  have hrest : ∑ t ∈ range L, e (1 + t) * ((2 : ℤ) ^ 32) ^ t = 0 := by
    rcases mul_eq_zero.mp hs with h | h
    · norm_num at h
    · exact h
  have := digits_zero_range L (fun t => e (1 + t)) (fun t ht => he (1 + t) (by simp [Finset.mem_Icc]; omega)) hrest
  intro b hb
  rw [Finset.mem_Icc] at hb
  have := this (b - 1) (by omega)
  simpa [show 1 + (b - 1) = b by omega] using this

/-! ### Scatter-accumulating the packed rows (one pass over the cut list) -/

/-- Add `v` to entry `n` of a list (no-op beyond the end). -/
def addAt : List ℤ → ℕ → ℤ → List ℤ
  | [], _, _ => []
  | x :: xs, 0, v => (x + v) :: xs
  | x :: xs, n + 1, v => x :: addAt xs n v

theorem length_addAt : ∀ (l : List ℤ) (n : ℕ) (v : ℤ), (addAt l n v).length = l.length
  | [], _, _ => rfl
  | x :: xs, 0, v => rfl
  | x :: xs, n + 1, v => by simp [addAt, length_addAt xs n v]

theorem getD_addAt : ∀ (l : List ℤ) (n m : ℕ) (v : ℤ), n < l.length →
    (addAt l n v).getD m 0 = l.getD m 0 + (if m = n then v else 0)
  | [], n, m, v, h => absurd h (Nat.not_lt_zero _)
  | x :: xs, 0, m, v, h => by
      cases m with
      | zero => simp [addAt]
      | succ m => simp [addAt]
  | x :: xs, n + 1, m, v, h => by
      cases m with
      | zero => simp [addAt]
      | succ m =>
        have ih := getD_addAt xs n m v (by simpa using h)
        simpa [addAt, List.getD_eq_getElem?_getD] using ih

/-- Add the row-`i`, row-`j` and row-`k` contributions of one cut to the accumulator. -/
def cutAcc (acc : List ℤ) (t : Cut) : List ℤ :=
  addAt (addAt (addAt acc (t.i - 1) (t.mn * (t.s1 * Bp t.j + t.s2 * Bp t.k)))
              (t.j - 1) (t.mn * (t.s1 * Bp t.i + t.s3 * Bp t.k)))
        (t.k - 1) (t.mn * (t.s2 * Bp t.i + t.s3 * Bp t.j))

/-- The packed rows: entry `a - 1` is `Σ_t packCut t a`. -/
def accumulate (L : ℕ) (cuts : List Cut) : List ℤ := cuts.foldl cutAcc (List.replicate L 0)

theorem length_cutAcc (acc : List ℤ) (t : Cut) : (cutAcc acc t).length = acc.length := by
  simp [cutAcc, length_addAt]

theorem cutAcc_getD (L : ℕ) (t : Cut) (ht : Cut.ok L t = true) (acc : List ℤ) (hacc : acc.length = L)
    (a : ℕ) (ha : a ∈ Icc 1 L) :
    (cutAcc acc t).getD (a - 1) 0 = acc.getD (a - 1) 0 + packCut t a := by
  obtain ⟨hi, hj, hk⟩ := Cut.ok_idx ht
  rw [Finset.mem_Icc] at hi hj hk ha
  unfold cutAcc
  rw [getD_addAt _ _ _ _ (by simp [length_addAt, hacc]; omega),
    getD_addAt _ _ _ _ (by simp [length_addAt, hacc]; omega),
    getD_addAt _ _ _ _ (by simp [hacc]; omega)]
  unfold packCut
  have e1 : (a - 1 = t.i - 1) ↔ (a = t.i) := by omega
  have e2 : (a - 1 = t.j - 1) ↔ (a = t.j) := by omega
  have e3 : (a - 1 = t.k - 1) ↔ (a = t.k) := by omega
  simp only [e1, e2, e3]
  ring

theorem foldl_cutAcc_getD (L : ℕ) : ∀ (cuts : List Cut), (∀ t ∈ cuts, Cut.ok L t = true) →
    ∀ (acc : List ℤ), acc.length = L → ∀ a ∈ Icc 1 L,
      (cuts.foldl cutAcc acc).getD (a - 1) 0 = acc.getD (a - 1) 0 + (cuts.map (fun t => packCut t a)).sum
  | [], _, acc, _, a, _ => by simp
  | t :: ts, h, acc, hacc, a, ha => by
      have ht := h t (by simp)
      have hts : ∀ s ∈ ts, Cut.ok L s = true := fun s hs => h s (List.mem_cons_of_mem _ hs)
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [foldl_cutAcc_getD L ts hts (cutAcc acc t) (by rw [length_cutAcc]; exact hacc) a ha,
        cutAcc_getD L t ht acc hacc a ha]
      ring

theorem accumulate_getD (L : ℕ) (cuts : List Cut) (h : ∀ t ∈ cuts, Cut.ok L t = true) (a : ℕ)
    (ha : a ∈ Icc 1 L) :
    (accumulate L cuts).getD (a - 1) 0 = (cuts.map (fun t => packCut t a)).sum := by
  unfold accumulate
  rw [foldl_cutAcc_getD L cuts h _ (by simp) a ha]
  rw [Finset.mem_Icc] at ha
  have : (List.replicate L (0 : ℤ)).getD (a - 1) 0 = 0 := by
    rw [List.getD_eq_getElem?_getD]
    simp
  rw [this, zero_add]

/-! ### The certificate -/

/-- The data of a MODEL2 certificate.  `nrows` is the integer matrix `N` (row `i` = `nrows[i-1]`), `rows` an integer
lower-triangular approximate Cholesky factor of `N` at scale `S` (`S = t²`), `acc` the packed cut rows. -/
structure Cert where
  L : ℕ
  Q : ℤ
  S : ℤ
  dn : List ℤ
  cuts : List Cut
  nrows : List (List ℤ)
  rows : List (List ℤ)
  acc : List ℤ

namespace Cert

def dnAt (T : Cert) (i : ℕ) : ℤ := T.dn.getD (i - 1) 0
def row (T : Cert) (i : ℕ) : List ℤ := T.rows.getD (i - 1) []
def nrow (T : Cert) (i : ℕ) : List ℤ := T.nrows.getD (i - 1) []
def accAt (T : Cert) (i : ℕ) : ℤ := T.acc.getD (i - 1) 0
/-- Entry `(i, j)` of `N` (1-indexed). -/
def Mat (T : Cert) (i j : ℕ) : ℤ := (T.nrow i).getD (j - 1) 0
/-- The residual `S·N - ⟨c_i, c_j⟩`. -/
def E (T : Cert) (i j : ℕ) : ℤ := T.S * T.Mat i j - dotL (T.row i) (T.row j)

end Cert

/-- `2 Q·C8 + 16·dn_a·[a = b]`: the formula `N` must equal, apart from the cut part. -/
def baseEntry (L : ℕ) (Q dna : ℤ) (a b : ℕ) : ℤ := 2 * Q * C8 L a b + (if a = b then 16 * dna else 0)

/-! #### Dominance of the residual (the PSD proof) -/

/-- `∑_j |S N_ij - ⟨c_i, c_j⟩|`, with the `N`-row and the list of Cholesky rows traversed in parallel. -/
def absRowSum2 (S : ℤ) (ri : List ℤ) : List ℤ → List (List ℤ) → ℕ
  | nj :: ns, rj :: rest => (S * nj - dotL ri rj).natAbs + absRowSum2 S ri ns rest
  | _, _ => 0

namespace Cert

/-- Row `i` of the residual is diagonally dominant (executable). -/
def rowOK (T : Cert) (i : ℕ) : Bool :=
  decide (((absRowSum2 T.S (T.row i) (T.nrow i) T.rows : ℕ) : ℤ) ≤ 2 * T.E i i)

end Cert

theorem absRowSum2_eq (S : ℤ) (ri : List ℤ) : ∀ (ns : List ℤ) (rs : List (List ℤ)), ns.length = rs.length →
    ((absRowSum2 S ri ns rs : ℕ) : ℤ) = ∑ t ∈ range ns.length, |S * ns.getD t 0 - dotL ri (rs.getD t [])|
  | [], [], _ => by simp [absRowSum2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | nj :: ns, rj :: rest, h => by
      have ih := absRowSum2_eq S ri ns rest (by simpa using h)
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [absRowSum2, List.getD_cons_succ, List.getD_cons_zero]
      push_cast
      rw [ih]
      ring

theorem Cert.rowOK_sound (T : Cert) (hrows : T.rows.length = T.L) (i : ℕ) (hn : (T.nrow i).length = T.L)
    (h : T.rowOK i = true) : ∑ j ∈ Icc 1 T.L, |T.E i j| ≤ 2 * T.E i i := by
  unfold Cert.rowOK at h
  have h' := of_decide_eq_true h
  have key := absRowSum2_eq T.S (T.row i) (T.nrow i) T.rows (by rw [hn, hrows])
  rw [key, hn] at h'
  have : ∑ j ∈ Icc 1 T.L, |T.E i j| =
      ∑ t ∈ range T.L, |T.S * (T.nrow i).getD t 0 - dotL (T.row i) (T.rows.getD t [])| := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    rw [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro t _
    simp [Cert.E, Cert.Mat, Cert.row]
  rw [this]
  exact h'

/-! #### The link: the table `N` equals `2Q·C8 + 16 diag(dn) - 8·(cut part)` -/

/-- `∑_b (v_b - base_ab) 2^{32 b}` over a row list, `b` from `b0` (executable). -/
def packDiff (L : ℕ) (Q dna : ℤ) (a : ℕ) : ℕ → List ℤ → ℤ
  | b, v :: vs => (v - baseEntry L Q dna a b) * Bp b + packDiff L Q dna a (b + 1) vs
  | _, [] => 0

/-- `|v_b - base_ab| < 2^30` for every entry (executable). -/
def boundDiff (L : ℕ) (Q dna : ℤ) (a : ℕ) : ℕ → List ℤ → Bool
  | b, v :: vs => decide ((v - baseEntry L Q dna a b).natAbs < 2 ^ 30) && boundDiff L Q dna a (b + 1) vs
  | _, [] => true

/-- Row `a` of the link check (executable). -/
def Cert.linkOK (T : Cert) (a : ℕ) : Bool :=
  decide (packDiff T.L T.Q (T.dnAt a) a 1 (T.nrow a) + 8 * T.accAt a = 0) &&
    boundDiff T.L T.Q (T.dnAt a) a 1 (T.nrow a)

theorem packDiff_eq (L : ℕ) (Q dna : ℤ) (a : ℕ) : ∀ (vs : List ℤ) (b0 : ℕ),
    packDiff L Q dna a b0 vs =
      ∑ t ∈ range vs.length, (vs.getD t 0 - baseEntry L Q dna a (b0 + t)) * Bp (b0 + t)
  | [], b0 => by simp [packDiff]
  | v :: vs, b0 => by
      have ih := packDiff_eq L Q dna a vs (b0 + 1)
      have hsum : ∑ t ∈ range vs.length, (vs.getD t 0 - baseEntry L Q dna a (b0 + 1 + t)) * Bp (b0 + 1 + t) =
          ∑ t ∈ range vs.length, (vs.getD t 0 - baseEntry L Q dna a (b0 + (t + 1))) * Bp (b0 + (t + 1)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [show b0 + 1 + t = b0 + (t + 1) by omega]
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [packDiff, List.getD_cons_succ, List.getD_cons_zero, add_zero]
      rw [ih, hsum, add_comm]

theorem boundDiff_sound (L : ℕ) (Q dna : ℤ) (a : ℕ) : ∀ (vs : List ℤ) (b0 : ℕ),
    boundDiff L Q dna a b0 vs = true → ∀ t < vs.length, |vs.getD t 0 - baseEntry L Q dna a (b0 + t)| < 2 ^ 30
  | [], b0, _ => fun t ht => absurd ht (by simp)
  | v :: vs, b0, h => by
      simp only [boundDiff, Bool.and_eq_true, decide_eq_true_eq] at h
      intro t ht
      cases t with
      | zero =>
        simp only [List.getD_cons_zero, add_zero]
        have := h.1
        rw [Int.abs_eq_natAbs]
        exact_mod_cast this
      | succ u =>
        have := boundDiff_sound L Q dna a vs (b0 + 1) h.2 u (by simpa using ht)
        simpa [List.getD_cons_succ, show b0 + (u + 1) = b0 + 1 + u by omega] using this

theorem dl_nonneg (m n : ℕ) : 0 ≤ dl m n := by unfold dl; split_ifs <;> norm_num
theorem dl_le_one (m n : ℕ) : dl m n ≤ 1 := by unfold dl; split_ifs <;> norm_num

theorem abs_sign_mul_le (s A : ℤ) (hs : s = 1 ∨ s = -1) (h0 : 0 ≤ A) (h2 : A ≤ 2) : |s * A| ≤ 2 := by
  rcases hs with rfl | rfl <;> simp [abs_of_nonneg h0, h2]

theorem ccm_abs_le {L : ℕ} (t : Cut) (ht : Cut.ok L t = true) (a b : ℕ) : |ccm t a b| ≤ 6 * t.mn := by
  obtain ⟨hs1, hs2, hs3, _, hmn⟩ := Cut.ok_sign ht
  have hA : 0 ≤ dl a t.i * dl b t.j + dl a t.j * dl b t.i ∧ dl a t.i * dl b t.j + dl a t.j * dl b t.i ≤ 2 := by
    have := dl_nonneg a t.i; have := dl_nonneg b t.j; have := dl_nonneg a t.j; have := dl_nonneg b t.i
    have := dl_le_one a t.i; have := dl_le_one b t.j; have := dl_le_one a t.j; have := dl_le_one b t.i
    constructor <;> nlinarith
  have hB : 0 ≤ dl a t.i * dl b t.k + dl a t.k * dl b t.i ∧ dl a t.i * dl b t.k + dl a t.k * dl b t.i ≤ 2 := by
    have := dl_nonneg a t.i; have := dl_nonneg b t.k; have := dl_nonneg a t.k; have := dl_nonneg b t.i
    have := dl_le_one a t.i; have := dl_le_one b t.k; have := dl_le_one a t.k; have := dl_le_one b t.i
    constructor <;> nlinarith
  have hC : 0 ≤ dl a t.j * dl b t.k + dl a t.k * dl b t.j ∧ dl a t.j * dl b t.k + dl a t.k * dl b t.j ≤ 2 := by
    have := dl_nonneg a t.j; have := dl_nonneg b t.k; have := dl_nonneg a t.k; have := dl_nonneg b t.j
    have := dl_le_one a t.j; have := dl_le_one b t.k; have := dl_le_one a t.k; have := dl_le_one b t.j
    constructor <;> nlinarith
  have e1 := abs_sign_mul_le _ _ hs1 hA.1 hA.2
  have e2 := abs_sign_mul_le _ _ hs2 hB.1 hB.2
  have e3 := abs_sign_mul_le _ _ hs3 hC.1 hC.2
  unfold ccm
  rw [abs_mul, abs_of_nonneg hmn]
  have : |t.s1 * (dl a t.i * dl b t.j + dl a t.j * dl b t.i) + t.s2 * (dl a t.i * dl b t.k + dl a t.k * dl b t.i)
      + t.s3 * (dl a t.j * dl b t.k + dl a t.k * dl b t.j)| ≤ 6 := by
    calc _ ≤ |t.s1 * (dl a t.i * dl b t.j + dl a t.j * dl b t.i) + t.s2 * (dl a t.i * dl b t.k + dl a t.k * dl b t.i)|
          + |t.s3 * (dl a t.j * dl b t.k + dl a t.k * dl b t.j)| := abs_add_le _ _
      _ ≤ (|t.s1 * (dl a t.i * dl b t.j + dl a t.j * dl b t.i)| + |t.s2 * (dl a t.i * dl b t.k + dl a t.k * dl b t.i)|)
          + |t.s3 * (dl a t.j * dl b t.k + dl a t.k * dl b t.j)| := by
            gcongr; exact abs_add_le _ _
      _ ≤ 6 := by linarith
  nlinarith

theorem rowvec_abs_le (L : ℕ) (a b : ℕ) : ∀ cuts : List Cut, (∀ t ∈ cuts, Cut.ok L t = true) →
    |rowvec cuts a b| ≤ 6 * (cuts.map Cut.mn).sum
  | [], _ => by simp [rowvec]
  | t :: ts, h => by
      have ht := h t (by simp)
      have hts : ∀ s ∈ ts, Cut.ok L s = true := fun s hs => h s (List.mem_cons_of_mem _ hs)
      have ih := rowvec_abs_le L a b ts hts
      have h1 := ccm_abs_le (L := L) t ht a b
      have e : rowvec (t :: ts) a b = ccm t a b + rowvec ts a b := by
        simp [rowvec]
      rw [e]
      simp only [List.map_cons, List.sum_cons]
      calc |ccm t a b + rowvec ts a b| ≤ |ccm t a b| + |rowvec ts a b| := abs_add_le _ _
        _ ≤ 6 * t.mn + 6 * (ts.map Cut.mn).sum := by linarith
        _ = _ := by ring

theorem Cert.link_sound (T : Cert) (hcuts : ∀ t ∈ T.cuts, Cut.ok T.L t = true)
    (hacc : accumulate T.L T.cuts = T.acc) (hSM : 48 * (T.cuts.map Cut.mn).sum < 2 ^ 30)
    (a : ℕ) (ha : a ∈ Icc 1 T.L) (hn : (T.nrow a).length = T.L) (h : T.linkOK a = true) :
    ∀ b ∈ Icc 1 T.L, T.Mat a b = baseEntry T.L T.Q (T.dnAt a) a b - 8 * rowvec T.cuts a b := by
  unfold Cert.linkOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  -- the packed row of the table
  have hpd : packDiff T.L T.Q (T.dnAt a) a 1 (T.nrow a) =
      ∑ b ∈ Icc 1 T.L, (T.Mat a b - baseEntry T.L T.Q (T.dnAt a) a b) * Bp b := by
    rw [packDiff_eq, hn, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro t _
    simp [Cert.Mat]
  -- the packed cut row
  have hac : T.accAt a = ∑ b ∈ Icc 1 T.L, rowvec T.cuts a b * Bp b := by
    rw [pack_rowvec T.L a T.cuts hcuts, ← accumulate_getD T.L T.cuts hcuts a ha, hacc]
    rfl
  set e : ℕ → ℤ := fun b => T.Mat a b - baseEntry T.L T.Q (T.dnAt a) a b + 8 * rowvec T.cuts a b with he
  have hsum : ∑ b ∈ Icc 1 T.L, e b * Bp b = 0 := by
    have : ∑ b ∈ Icc 1 T.L, e b * Bp b = ∑ b ∈ Icc 1 T.L, (T.Mat a b - baseEntry T.L T.Q (T.dnAt a) a b) * Bp b
        + 8 * ∑ b ∈ Icc 1 T.L, rowvec T.cuts a b * Bp b := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      simp only [he]
      ring
    rw [this, ← hpd, ← hac]
    exact h1
  have hbd := boundDiff_sound T.L T.Q (T.dnAt a) a (T.nrow a) 1 h2
  have hb : ∀ b ∈ Icc 1 T.L, |e b| < 2 ^ 32 := by
    intro b hb
    have hb' := Finset.mem_Icc.mp hb
    have h3 := hbd (b - 1) (by omega)
    have h4 : (T.nrow a).getD (b - 1) 0 = T.Mat a b := rfl
    rw [h4, show 1 + (b - 1) = b by omega] at h3
    have h5 := rowvec_abs_le T.L a b T.cuts hcuts
    simp only [he]
    calc |T.Mat a b - baseEntry T.L T.Q (T.dnAt a) a b + 8 * rowvec T.cuts a b|
        ≤ |T.Mat a b - baseEntry T.L T.Q (T.dnAt a) a b| + |8 * rowvec T.cuts a b| := abs_add_le _ _
      _ < 2 ^ 32 := by
        rw [abs_mul]
        norm_num
        nlinarith
  have hz := digits_zero T.L e hb hsum
  intro b hb'
  have := hz b hb'
  simp only [he] at this
  linarith

/-! #### Positive semidefiniteness of the table `N`, and the cube bound -/

theorem C8_comm (L p q : ℕ) : C8 L p q = C8 L q p := by
  unfold C8
  have : (if p = q then (8 : ℤ) else 0) = (if q = p then 8 else 0) := by
    by_cases h : p = q
    · subst h; rfl
    · have h' : ¬ q = p := fun e => h e.symm
      simp [h, h']
  rw [this]
  ring

theorem Cert.E_comm (T : Cert) (i j : ℕ) (h : T.Mat i j = T.Mat j i) : T.E i j = T.E j i := by
  unfold Cert.E
  rw [h, dotL_comm]

/-- `S·xᵀNx ≥ 0`: Gram part plus a diagonally dominant residual. -/
theorem Cert.psd (T : Cert) (hS : 0 < T.S) (hrows : T.rows.length = T.L)
    (hnrow : ∀ i ∈ Icc 1 T.L, (T.nrow i).length = T.L)
    (hlen : ∀ i ∈ Icc 1 T.L, (T.row i).length ≤ T.L)
    (hsym : ∀ i ∈ Icc 1 T.L, ∀ j ∈ Icc 1 T.L, T.Mat i j = T.Mat j i)
    (hdom : ∀ i ∈ Icc 1 T.L, T.rowOK i = true) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, ((T.Mat i j : ℤ) : ℝ) * x i * x j := by
  set c : ℕ → ℕ → ℝ := fun i k => (((T.row i).getD k 0 : ℤ) : ℝ) with hc
  set Er : ℕ → ℕ → ℝ := fun i j =>
    if i ∈ Icc 1 T.L ∧ j ∈ Icc 1 T.L then ((T.E i j : ℤ) : ℝ) else 0 with hEr
  have hG := gram_nonneg T.L T.L c x
  have hsymE : ∀ i j, Er i j = Er j i := by
    intro i j
    by_cases h : i ∈ Icc 1 T.L ∧ j ∈ Icc 1 T.L
    · have h' : j ∈ Icc 1 T.L ∧ i ∈ Icc 1 T.L := ⟨h.2, h.1⟩
      simp only [hEr, h, h', and_self, if_true]
      rw [T.E_comm i j (hsym i h.1 j h.2)]
    · have h' : ¬ (j ∈ Icc 1 T.L ∧ i ∈ Icc 1 T.L) := fun e => h ⟨e.2, e.1⟩
      simp only [hEr, h, h', if_false]
  have hdomE : ∀ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, |Er i j| ≤ 2 * Er i i := by
    intro i hi
    have h1 := Cert.rowOK_sound T hrows i (hnrow i hi) (hdom i hi)
    have h2 : ((∑ j ∈ Icc 1 T.L, |T.E i j| : ℤ) : ℝ) ≤ ((2 * T.E i i : ℤ) : ℝ) := by exact_mod_cast h1
    have e1 : ∑ j ∈ Icc 1 T.L, |Er i j| = ((∑ j ∈ Icc 1 T.L, |T.E i j| : ℤ) : ℝ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro j hj
      simp only [hEr, hi, hj, and_self, if_true]
    have e2 : Er i i = ((T.E i i : ℤ) : ℝ) := by simp only [hEr, hi, and_self, if_true]
    rw [e1, e2]
    push_cast at h2 ⊢
    exact h2
  have hE := psd_of_dom T.L Er hsymE hdomE x
  have hE' : 0 ≤ ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, ((T.E i j : ℤ) : ℝ) * x i * x j := by
    have : ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, Er i j * x i * x j =
        ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, ((T.E i j : ℤ) : ℝ) * x i * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [hEr, hi, hj, and_self, if_true]
    rw [← this]
    exact hE
  have hME : ∀ i ∈ Icc 1 T.L, ∀ j ∈ Icc 1 T.L,
      (T.S : ℝ) * ((T.Mat i j : ℤ) : ℝ) = (∑ k ∈ range T.L, c i k * c j k) + ((T.E i j : ℤ) : ℝ) := by
    intro i hi j _
    have hd : dotL (T.row i) (T.row j) = ∑ k ∈ range T.L, (T.row i).getD k 0 * (T.row j).getD k 0 :=
      dotL_eq_sum _ _ _ (hlen i hi)
    have : T.S * T.Mat i j = dotL (T.row i) (T.row j) + T.E i j := by
      unfold Cert.E; ring
    have h2 : ((T.S * T.Mat i j : ℤ) : ℝ) = ((dotL (T.row i) (T.row j) + T.E i j : ℤ) : ℝ) := by
      rw [this]
    rw [hd] at h2
    simp only [hc]
    push_cast at h2 ⊢
    linarith
  have hsum : (T.S : ℝ) * ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, ((T.Mat i j : ℤ) : ℝ) * x i * x j =
      (∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, (∑ k ∈ range T.L, c i k * c j k) * x i * x j)
      + ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, ((T.E i j : ℤ) : ℝ) * x i * x j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have := hME i hi j hj
    calc (T.S : ℝ) * (((T.Mat i j : ℤ) : ℝ) * x i * x j)
        = ((T.S : ℝ) * ((T.Mat i j : ℤ) : ℝ)) * x i * x j := by ring
      _ = _ := by rw [this]; ring
  have hSpos : (0 : ℝ) < T.S := by exact_mod_cast hS
  have : 0 ≤ (T.S : ℝ) * ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, ((T.Mat i j : ℤ) : ℝ) * x i * x j := by
    rw [hsum]; exact add_nonneg hG hE'
  exact (mul_nonneg_iff_of_pos_left hSpos).mp this

/-- Every cut is `≥ -1` on the cube: `-Σ mn ≤ Σ mn·cutval`. -/
theorem cuts_lower (L : ℕ) (x : ℕ → ℝ) (hx : ∀ p ∈ Icc 1 L, |x p| ≤ 1) :
    ∀ cuts : List Cut, (∀ t ∈ cuts, Cut.ok L t = true) →
      -((cuts.map Cut.mn).sum : ℝ) ≤ (cuts.map (fun t => (t.mn : ℝ) * cutval t x)).sum
  | [], _ => by simp
  | t :: ts, h => by
      have ht := h t (by simp)
      have hts : ∀ s ∈ ts, Cut.ok L s = true := fun s hs => h s (List.mem_cons_of_mem _ hs)
      have ih := cuts_lower L x hx ts hts
      obtain ⟨hi, hj, hk⟩ := Cut.ok_idx ht
      obtain ⟨hs1, hs2, hs3, hp, hmn⟩ := Cut.ok_sign ht
      have hc := cutval_ge t.s1 t.s2 t.s3 hs1 hs2 hs3 hp (x t.i) (x t.j) (x t.k) (hx _ hi) (hx _ hj) (hx _ hk)
      have hmn' : (0 : ℝ) ≤ t.mn := by exact_mod_cast hmn
      simp only [List.map_cons, List.sum_cons]
      rw [Int.cast_add]
      have hcv : -1 ≤ cutval t x := by unfold cutval; exact hc
      have hm := mul_nonneg hmn' (by linarith : (0 : ℝ) ≤ cutval t x + 1)
      linarith

/-- THE CERTIFICATE THEOREM: the kernel-checked data gives `xᵀ C x ≥ -(Σ dn + Σ mn)/Q` on the cube. -/
theorem cubeLB_of_cert (T : Cert) (hQ : 0 < T.Q) (hS : 0 < T.S)
    (hrows : T.rows.length = T.L)
    (hnrow : ∀ i ∈ Icc 1 T.L, (T.nrow i).length = T.L)
    (hlen : ∀ i ∈ Icc 1 T.L, (T.row i).length ≤ T.L)
    (hdn : ∀ i ∈ Icc 1 T.L, 0 ≤ T.dnAt i)
    (hcuts : ∀ t ∈ T.cuts, Cut.ok T.L t = true)
    (hacc : accumulate T.L T.cuts = T.acc)
    (hSM : 48 * (T.cuts.map Cut.mn).sum < 2 ^ 30)
    (hlink : ∀ a ∈ Icc 1 T.L, T.linkOK a = true)
    (hdom : ∀ i ∈ Icc 1 T.L, T.rowOK i = true) :
    CubeLB T.L (((((∑ i ∈ Icc 1 T.L, T.dnAt i) + (T.cuts.map Cut.mn).sum : ℤ)) : ℚ) / (T.Q : ℚ)) := by
  intro x hx
  have hMat : ∀ i ∈ Icc 1 T.L, ∀ j ∈ Icc 1 T.L,
      T.Mat i j = baseEntry T.L T.Q (T.dnAt i) i j - 8 * rowvec T.cuts i j :=
    fun i hi j hj => Cert.link_sound T hcuts hacc hSM i hi (hnrow i hi) (hlink i hi) j hj
  have hsym : ∀ i ∈ Icc 1 T.L, ∀ j ∈ Icc 1 T.L, T.Mat i j = T.Mat j i := by
    intro i hi j hj
    rw [hMat i hi j hj, hMat j hj i hi, rowvec_comm T.cuts i j]
    unfold baseEntry
    rw [C8_comm T.L i j]
    by_cases h : i = j
    · subst h; rfl
    · have h' : ¬ j = i := fun e => h e.symm
      simp [h, h']
  have hpsd := Cert.psd T hS hrows hnrow hlen hsym hdom x
  -- rewrite the matrix
  have hexp : ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, ((T.Mat i j : ℤ) : ℝ) * x i * x j =
      2 * (T.Q : ℝ) * (∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, (C8 T.L i j : ℝ) * x i * x j)
      + 16 * (∑ i ∈ Icc 1 T.L, ((T.dnAt i : ℤ) : ℝ) * x i ^ 2)
      - 8 * (∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, ((rowvec T.cuts i j : ℤ) : ℝ) * x i * x j) := by
    have e1 : ∀ i ∈ Icc 1 T.L, ∀ j ∈ Icc 1 T.L, ((T.Mat i j : ℤ) : ℝ) * x i * x j =
        2 * (T.Q : ℝ) * ((C8 T.L i j : ℝ) * x i * x j)
        + (if i = j then 16 * ((T.dnAt i : ℤ) : ℝ) * x i ^ 2 else 0)
        - 8 * (((rowvec T.cuts i j : ℤ) : ℝ) * x i * x j) := by
      intro i hi j hj
      rw [hMat i hi j hj]
      unfold baseEntry
      by_cases h : i = j
      · subst h; push_cast; simp; ring
      · simp [h]; ring
    have hdiag : ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L,
        (if i = j then 16 * ((T.dnAt i : ℤ) : ℝ) * x i ^ 2 else 0)
        = 16 * (∑ i ∈ Icc 1 T.L, ((T.dnAt i : ℤ) : ℝ) * x i ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_ite_eq, if_pos hi]
      ring
    rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => e1 i hi j hj))]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hdiag]
  rw [hexp, quad_rowvec T.L x T.cuts hcuts] at hpsd
  -- bounds
  have hD : ∑ i ∈ Icc 1 T.L, ((T.dnAt i : ℤ) : ℝ) * x i ^ 2 ≤ ((∑ i ∈ Icc 1 T.L, T.dnAt i : ℤ) : ℝ) := by
    push_cast
    apply Finset.sum_le_sum
    intro i hi
    have h0 : (0 : ℝ) ≤ ((T.dnAt i : ℤ) : ℝ) := by exact_mod_cast hdn i hi
    have h1 : x i ^ 2 ≤ 1 := by
      have := abs_le.mp (hx i hi)
      nlinarith
    nlinarith
  have hR := cuts_lower T.L x hx T.cuts hcuts
  have hQr : (0 : ℝ) < T.Q := by exact_mod_cast hQ
  have h8 : cform T.L x = (1 / 8 : ℝ) * ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, (C8 T.L i j : ℝ) * x i * x j := rfl
  set A := ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, (C8 T.L i j : ℝ) * x i * x j with hA
  have hcf : cform T.L x = A / 8 := by rw [h8]; ring
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, hcf]
  rw [Int.cast_add]
  have hD' : ∑ i ∈ Icc 1 T.L, ((T.dnAt i : ℤ) : ℝ) * x i ^ 2 ≤ ((∑ i ∈ Icc 1 T.L, T.dnAt i : ℤ) : ℝ) := hD
  have hmain : -(((∑ i ∈ Icc 1 T.L, T.dnAt i : ℤ) : ℝ) + (((T.cuts.map Cut.mn).sum : ℤ) : ℝ)) ≤ (T.Q : ℝ) * (A / 8) := by
    linarith
  have h2 : -(((∑ i ∈ Icc 1 T.L, T.dnAt i : ℤ) : ℝ) + (((T.cuts.map Cut.mn).sum : ℤ) : ℝ)) / (T.Q : ℝ) ≤ A / 8 := by
    rw [div_le_iff₀ hQr]
    linarith
  rw [neg_div] at h2
  exact h2

end Erdos1186Night2M2
