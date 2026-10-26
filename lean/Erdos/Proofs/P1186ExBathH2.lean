import Mathlib
import Erdos.Proofs.P1186Ex
import Erdos.Proofs.P1186ExBathFU

/-!
# Erdos 1186 - the bathtub function `H2` is piecewise linear on unit cells

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's.  At scale `n = 1096 w` the claim's `h` (`H2 w x = 2 H_x`) is, on the unit cell `p` (points
`x = (p-1) w + j`, `1 ≤ j ≤ w`), `α_p w + β_p j + ε` with `|ε| ≤ 2` and integers `α_p`, `β_p` given by the explicit
formulas `alphaF`, `betaF` in terms of the sign table `Usg` and its prefix sums `FU`.  `H2_lin` is the statement; it
needs only the structure of `sstar` (constant on coarse cells of length `2w`).
-/

namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

lemma sstar_eq (w y : ℕ) (hw : 1 ≤ w) (hy : 1 ≤ y) : sstar w y = Usg ((y - 1) / w) := by
  unfold sstar Usg ck sg
  have h1 : (y + (2 * w - 1)) / (2 * w) = (y - 1) / w / 2 + 1 := by
    have e : y + (2 * w - 1) = (y - 1) + 2 * w := by omega
    rw [e, Nat.add_div_right _ (by omega : 0 < 2 * w), Nat.div_div_eq_div_mul, mul_comm w 2]
  show (if c1 ((y + (2 * w - 1)) / (2 * w)) = true then (1 : ℤ) else -1) = _
  rw [h1]

lemma pre_sstar (w : ℕ) (hw : 1 ≤ w) :
    ∀ m, m ≤ 1096 * w → pre (sstar w) m = w * FU (m / w) + ((m % w : ℕ) : ℤ) * Usg (m / w) := by
  intro m
  induction m with
  | zero => intro _; simp [pre_zero, FU_zero]
  | succ m ih =>
    intro hm
    have hm' : m ≤ 1096 * w := by omega
    rw [pre_succ, ih hm', sstar_eq w (m + 1) hw (by omega)]
    simp only [Nat.add_sub_cancel]
    have hqm : m = w * (m / w) + m % w := (Nat.div_add_mod m w).symm
    have hr : m % w < w := Nat.mod_lt _ (by omega)
    have hq : m / w < 1096 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    by_cases hlt : m % w + 1 < w
    · have h1 : (m + 1) / w = m / w ∧ (m + 1) % w = m % w + 1 :=
        (Nat.div_mod_unique (by omega)).2 ⟨by omega, hlt⟩
      rw [h1.1, h1.2]; push_cast; ring
    · have hw1 : m % w + 1 = w := by omega
      have h1 : (m + 1) / w = m / w + 1 ∧ (m + 1) % w = 0 :=
        (Nat.div_mod_unique (by omega)).2 ⟨by rw [Nat.mul_add]; omega, by omega⟩
      rw [h1.1, h1.2, FU_succ _ hq]
      have : ((m % w : ℕ) : ℤ) = (w : ℤ) - 1 := by omega
      rw [this]; push_cast; ring

/-- `pre (sstar w)` at `k w + r`, `0 ≤ r ≤ w`. -/
lemma pre_lin (w : ℕ) (hw : 1 ≤ w) (k r : ℕ) (hk : k ≤ 1095) (hr : r ≤ w) :
    pre (sstar w) (k * w + r) = w * FU k + r * Usg k := by
  rcases Nat.lt_or_ge r w with h | h
  · have h1 : (k * w + r) / w = k ∧ (k * w + r) % w = r :=
      (Nat.div_mod_unique (by omega)).2 ⟨by rw [mul_comm]; omega, h⟩
    rw [pre_sstar w hw _ (by nlinarith), h1.1, h1.2]
  · have hrw : r = w := le_antisymm hr h
    subst hrw
    have h1 : (k * r + r) / r = k + 1 ∧ (k * r + r) % r = 0 :=
      (Nat.div_mod_unique (by omega)).2 ⟨by rw [mul_comm]; ring, by omega⟩
    rw [pre_sstar r hw _ (by nlinarith), h1.1, h1.2, FU_succ k (by omega)]
    push_cast; ring

/-- the same at `2 k w + r`, `0 ≤ r ≤ 2w` (coarse cells have length `2w`). -/
lemma pre_lin2 (w : ℕ) (hw : 1 ≤ w) (k r : ℕ) (hk : k ≤ 547) (hr : r ≤ 2 * w) :
    pre (sstar w) (2 * k * w + r) = w * FU (2 * k) + r * Usg (2 * k) := by
  rcases le_or_gt r w with h | h
  · exact pre_lin w hw (2 * k) r (by omega) h
  · have e : 2 * k * w + r = (2 * k + 1) * w + (r - w) := by
      have : r = w + (r - w) := by omega
      nlinarith
    rw [e, pre_lin w hw (2 * k + 1) (r - w) (by omega) (by omega), Usg_pair, FU_succ (2 * k) (by omega)]
    have : ((r - w : ℕ) : ℤ) = (r : ℤ) - w := by omega
    rw [this]; ring

lemma rowsum (w x : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ nn w) :
    ∑ y ∈ Icc 1 (nn w), rdI (nn w) x y * sstar w y
      = pre (sstar w) ((x + nn w) / 2) - pre (sstar w) (x / 2) := by
  have h1 : ∀ y ∈ Icc 1 (nn w), rdI (nn w) x y * sstar w y
      = if (x / 2 < y ∧ y ≤ (x + nn w) / 2) then sstar w y else 0 := by
    intro y _
    unfold rdI
    have hiff : (1 ≤ 2 * (y : ℤ) - x ∧ 2 * (y : ℤ) - x ≤ (nn w : ℤ)) ↔ (x / 2 < y ∧ y ≤ (x + nn w) / 2) := by
      omega
    by_cases h : x / 2 < y ∧ y ≤ (x + nn w) / 2
    · rw [if_pos (hiff.2 h), if_pos h]; ring
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]; ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have h2 : (Icc 1 (nn w)).filter (fun y => x / 2 < y ∧ y ≤ (x + nn w) / 2)
      = Ioc (x / 2) ((x + nn w) / 2) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h2, sum_Ioc_eq _ (by omega)]

lemma colsum (w x : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ nn w) :
    ∑ e ∈ Icc 1 (nn w), rdI (nn w) e x * sstar w e
      = pre (sstar w) (min (nn w) (2 * x - 1)) - pre (sstar w) (2 * x - nn w - 1) := by
  have h1 : ∀ e ∈ Icc 1 (nn w), rdI (nn w) e x * sstar w e
      = if (2 * x - nn w - 1 < e ∧ e ≤ min (nn w) (2 * x - 1)) then sstar w e else 0 := by
    intro e he
    unfold rdI
    have hiff : (1 ≤ 2 * (x : ℤ) - e ∧ 2 * (x : ℤ) - e ≤ (nn w : ℤ))
        ↔ (2 * x - nn w - 1 < e ∧ e ≤ min (nn w) (2 * x - 1)) := by
      rw [Finset.mem_Icc] at he
      omega
    by_cases h : 2 * x - nn w - 1 < e ∧ e ≤ min (nn w) (2 * x - 1)
    · rw [if_pos (hiff.2 h), if_pos h]; ring
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]; ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have h2 : (Icc 1 (nn w)).filter (fun e => 2 * x - nn w - 1 < e ∧ e ≤ min (nn w) (2 * x - 1))
      = Ioc (2 * x - nn w - 1) (min (nn w) (2 * x - 1)) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h2, sum_Ioc_eq _ (by omega)]

/-- Closed form of `H2` on the unit cell `p' + 1` (points `p' w + j`, `1 ≤ j ≤ w`), in terms of `Usg`, `FU`. -/
theorem H2_formula (w : ℕ) (hw : 1 ≤ w) (p' j : ℕ) (hp : p' ≤ 1095) (hj1 : 1 ≤ j) (hj2 : j ≤ w) :
    H2 w (p' * w + j)
      = - Usg p' * ((w : ℤ) * (FU (p' / 2 + 548) - FU (p' / 2))
          + ((((p' % 2) * w + j) / 2 : ℕ) : ℤ) * (Usg (p' / 2 + 548) - Usg (p' / 2))
          + (if p' < 548 then ((w : ℤ) * FU (2 * p') + (2 * (j : ℤ) - 1) * Usg (2 * p'))
             else -((w : ℤ) * FU (2 * (p' - 548)) + (2 * (j : ℤ) - 1) * Usg (2 * (p' - 548))))) := by
  have hnn : nn w = 1096 * w := rfl
  have hx1 : 1 ≤ p' * w + j := by omega
  have hpw : p' * w ≤ 1095 * w := Nat.mul_le_mul_right _ hp
  have hx2 : p' * w + j ≤ nn w := by rw [hnn]; nlinarith
  -- the sign at x
  have hs : sstar w (p' * w + j) = Usg p' := by
    rw [sstar_eq w _ hw hx1]
    congr 1
    have : p' * w + j - 1 = p' * w + (j - 1) := by omega
    rw [this]
    exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
  unfold H2
  rw [rowsum w _ hx1 hx2, colsum w _ hx1 hx2, hs]
  -- parity decomposition
  obtain ⟨k2, e, he, rfl⟩ : ∃ k2 e, e ≤ 1 ∧ p' = 2 * k2 + e := ⟨p' / 2, p' % 2, by omega, by omega⟩
  have hk2 : k2 ≤ 547 := by omega
  have hk2' : (2 * k2 + e) / 2 = k2 := by omega
  have he2 : (2 * k2 + e) % 2 = e := by omega
  rw [hk2', he2]
  set r := (e * w + j) / 2 with hr
  have hrw : r ≤ w := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · subst h0; omega
    · have : e = 1 := by omega
      subst this; omega
  have ea1 : ((2 * k2 + e) * w + j + nn w) / 2 = (k2 + 548) * w + r := by
    have : (2 * k2 + e) * w + j + nn w = 2 * ((k2 + 548) * w) + (e * w + j) := by rw [hnn]; ring
    rw [this]; omega
  have ea2 : ((2 * k2 + e) * w + j) / 2 = k2 * w + r := by
    have : (2 * k2 + e) * w + j = 2 * (k2 * w) + (e * w + j) := by ring
    rw [this]; omega
  rw [ea1, ea2, pre_lin w hw (k2 + 548) r (by omega) hrw, pre_lin w hw k2 r (by omega) hrw]
  by_cases hlt : 2 * k2 + e < 548
  · rw [if_pos hlt]
    have hx : 2 * ((2 * k2 + e) * w + j) ≤ nn w := by
      have : (2 * k2 + e) * w ≤ 547 * w := Nat.mul_le_mul_right _ (by omega)
      rw [hnn]; nlinarith
    have e2 : 2 * (2 * k2 + e) * w = 2 * ((2 * k2 + e) * w) := by ring
    have ea3 : min (nn w) (2 * ((2 * k2 + e) * w + j) - 1) = 2 * (2 * k2 + e) * w + (2 * j - 1) := by
      rw [e2]
      have h : 2 * ((2 * k2 + e) * w + j) - 1 = 2 * ((2 * k2 + e) * w) + (2 * j - 1) := by omega
      rw [h]; exact min_eq_right (by omega)
    have ea4 : 2 * ((2 * k2 + e) * w + j) - nn w - 1 = 0 := by omega
    rw [ea3, ea4, pre_zero, pre_lin2 w hw (2 * k2 + e) (2 * j - 1) (by omega) (by omega)]
    have : ((2 * j - 1 : ℕ) : ℤ) = 2 * (j : ℤ) - 1 := by omega
    rw [this]; ring
  · rw [if_neg hlt]
    obtain ⟨q, hq⟩ : ∃ q, 2 * k2 + e = 548 + q := ⟨2 * k2 + e - 548, by omega⟩
    have hq547 : q ≤ 547 := by omega
    have hx' : (2 * k2 + e) * w + j = 548 * w + (q * w + j) := by rw [hq]; ring
    have ea3 : min (nn w) (2 * ((2 * k2 + e) * w + j) - 1) = nn w := by
      apply min_eq_left; rw [hnn, hx']; omega
    have ea4 : 2 * ((2 * k2 + e) * w + j) - nn w - 1 = 2 * q * w + (2 * j - 1) := by
      rw [hx', hnn]
      have : 2 * (548 * w + (q * w + j)) = 1096 * w + 2 * q * w + 2 * j := by ring
      omega
    have hpre : pre (sstar w) (nn w) = 0 := by
      rw [hnn, pre_sstar w hw _ le_rfl, Nat.mul_div_cancel _ (by omega : 0 < w), Nat.mul_mod_left]
      simp [FU_1096]
    rw [ea3, ea4, hpre, pre_lin2 w hw q (2 * j - 1) hq547 (by omega)]
    have : ((2 * j - 1 : ℕ) : ℤ) = 2 * (j : ℤ) - 1 := by omega
    rw [this, show 2 * k2 + e - 548 = q by omega]; ring

/-- `(Usg (k+548) - Usg k) / 2 ∈ {-1, 0, 1}` for `k = p'/2`. -/
def Dd (p' : ℕ) : ℤ := (Usg (p' / 2 + 548) - Usg (p' / 2)) / 2
def Qa (p' : ℕ) : ℤ := if p' < 548 then FU (2 * p') else -FU (2 * (p' - 548))
def Qb (p' : ℕ) : ℤ := if p' < 548 then Usg (2 * p') else -Usg (2 * (p' - 548))

/-- the intercept `α` of the unit cell `p' + 1`: `H2 w (p' w + j) = α w + β j + ε`. -/
def alphaF (p' : ℕ) : ℤ :=
  - Usg p' * (FU (p' / 2 + 548) - FU (p' / 2) + ((p' % 2 : ℕ) : ℤ) * Dd p' + Qa p')
/-- the slope `β` of the unit cell `p' + 1`. -/
def betaF (p' : ℕ) : ℤ := - Usg p' * (Dd p' + 2 * Qb p')

lemma Dd_two (p' : ℕ) : Usg (p' / 2 + 548) - Usg (p' / 2) = 2 * Dd p' := by
  unfold Dd
  rcases Usg_pm (p' / 2 + 548) with h | h <;> rcases Usg_pm (p' / 2) with h' | h' <;> rw [h, h'] <;> norm_num

lemma Dd_bd (p' : ℕ) : -1 ≤ Dd p' ∧ Dd p' ≤ 1 := by
  have := Dd_two p'
  rcases Usg_pm (p' / 2 + 548) with h | h <;> rcases Usg_pm (p' / 2) with h' | h' <;> constructor <;> omega

lemma Qb_pm (p' : ℕ) : Qb p' = 1 ∨ Qb p' = -1 := by
  unfold Qb; split_ifs
  · exact Usg_pm _
  · rcases Usg_pm (2 * (p' - 548)) with h | h <;> simp [h]

/-- **`H2` is piecewise linear on unit cells**: `H2 w (p' w + j) = α w + β j + ε`, `|ε| ≤ 2`. -/
theorem H2_lin (w : ℕ) (hw : 1 ≤ w) (p' j : ℕ) (hp : p' ≤ 1095) (hj1 : 1 ≤ j) (hj2 : j ≤ w) :
    |(H2 w (p' * w + j) : ℤ) - (alphaF p' * w + betaF p' * j)| ≤ 2 := by
  rw [H2_formula w hw p' j hp hj1 hj2]
  have hQ : (if p' < 548 then ((w : ℤ) * FU (2 * p') + (2 * (j : ℤ) - 1) * Usg (2 * p'))
             else -((w : ℤ) * FU (2 * (p' - 548)) + (2 * (j : ℤ) - 1) * Usg (2 * (p' - 548))))
      = (w : ℤ) * Qa p' + (2 * (j : ℤ) - 1) * Qb p' := by
    unfold Qa Qb; split_ifs <;> ring
  rw [hQ]
  have hr2 : 2 * ((((p' % 2) * w + j) / 2 : ℕ) : ℤ) + ((((p' % 2) * w + j) % 2 : ℕ) : ℤ)
      = ((p' % 2 : ℕ) : ℤ) * w + j := by
    have hX : ∀ X : ℕ, 2 * ((X / 2 : ℕ) : ℤ) + ((X % 2 : ℕ) : ℤ) = (X : ℤ) := fun X => by omega
    have h := hX ((p' % 2) * w + j)
    rw [Nat.cast_add, Nat.cast_mul] at h
    exact h
  have hD := Dd_two p'
  have key : -Usg p' * ((w : ℤ) * (FU (p' / 2 + 548) - FU (p' / 2))
        + ((((p' % 2) * w + j) / 2 : ℕ) : ℤ) * (Usg (p' / 2 + 548) - Usg (p' / 2))
        + ((w : ℤ) * Qa p' + (2 * (j : ℤ) - 1) * Qb p'))
      - (alphaF p' * w + betaF p' * j)
      = Usg p' * ((((p' % 2) * w + j) % 2 : ℕ) * Dd p' + Qb p') := by
    unfold alphaF betaF
    rw [hD]
    linear_combination (-(Usg p') * Dd p') * hr2
  rw [key]
  have hδ : ((((p' % 2) * w + j) % 2 : ℕ) : ℤ) = 0 ∨ ((((p' % 2) * w + j) % 2 : ℕ) : ℤ) = 1 := by omega
  have hb := Dd_bd p'
  rw [abs_le]
  rcases Usg_pm p' with hU | hU <;> rcases Qb_pm p' with hQb | hQb <;> rcases hδ with hd | hd <;>
    rw [hU, hQb, hd] <;> constructor <;> linarith [hb.1, hb.2]

end Erdos1186Ex
