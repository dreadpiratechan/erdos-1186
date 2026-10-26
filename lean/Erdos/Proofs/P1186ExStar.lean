import Mathlib
import Erdos.Proofs.P1186Ex
import Erdos.Proofs.P1186M2Low

/-!
# Erdos 1186 - the claimed proof of `δ 3 = 117/2192`, lane `exstar`: `StarOK`, the window correlation of the PRS colouring

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its author's.

Main theorem (`StarOK` is the shared interface `P1186Ex.lean`):

```
theorem Erdos1186Ex.starOK : StarOK
```
i.e. there is `C` with `-(5/137) (1096 w)² - C w ≤ Wm (sstar w) (1096 w)` for every `w ≥ 1`, where `sstar w` is the PRS
12-block colouring `ck (2 w)` of `[1, 1096 w]` as `±1`.  In fact `C = 3288` works (`Wm_sstar_lower`).

**Proof** (own derivation, from the reviewers' description of Step 1 of the claim; no code or data of the claim is used).
Use lean1186c's cover inequality `W_lower` (`P1186M2LowB.lean`) with `h = 274`, `N = w`: `L = 548` blocks of length `2 w`
(so `n = 2 · (274 · 2 w) = 1096 w`).  The colouring `sstar w` is constant on each of these blocks (`sstar_cell`), with
the value `σ_p = sg c1 p` on block `p`, so `Xb (sstar w) (2 w) p = 2 w σ_p` exactly (`Xb_sstar`); the cut-loss term
`Σ_p ((2w)² - X_p²)` of `W_lower` is therefore `0`, and
`8 Wm ≥ 2 (2w)² T - 548 (16 w + 32)` with `T = Σ_{q,p ≤ 548} K4 548 p q σ_p σ_q`.
`T = -43840` is computed once, by the kernel (`starT_val`, `decide +kernel`): the column sums of `K4` are closed
forms in the prefix sums of `σ` (`KS_lo`, `KS_hi` of `P1186M2LowB.lean`), which leaves a sum of 274 terms
(`T_eq_starT`).  Since `(5/137) · 1096² = 43840`, this is `Wm ≥ -(5/137) n² - 1096 w - 2192`.
-/

namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

/-- `sstar w` is constant `= sg c1 p` on the block `((p-1)·2w, p·2w]`. -/
lemma sstar_cell (w p x : ℕ) (hw : 1 ≤ w) (hp : 1 ≤ p) (h1 : (p - 1) * (2 * w) < x) (h2 : x ≤ p * (2 * w)) :
    sstar w x = sg c1 p := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  have e : (x + (2 * w - 1)) / (2 * w) = p' + 1 := by
    apply Nat.div_eq_of_lt_le
    · have : (p' + 1) * (2 * w) = p' * (2 * w) + 2 * w := by ring
      simp only [Nat.add_sub_cancel] at h1
      omega
    · have : (p' + 1 + 1) * (2 * w) = p' * (2 * w) + 2 * w + 2 * w := by ring
      have h2' : x ≤ p' * (2 * w) + 2 * w := by
        have : (p' + 1) * (2 * w) = p' * (2 * w) + 2 * w := by ring
        omega
      omega
  have hc : ck (2 * w) x = c1 (p' + 1) := by unfold ck; rw [e]
  unfold sstar sg
  rw [hc]

/-- The block sum of `sstar w` over block `p` is `2 w σ_p`. -/
lemma Xb_sstar (w p : ℕ) (hw : 1 ≤ w) (hp : 1 ≤ p) :
    Xb (sstar w) (2 * w) p = 2 * (w : ℤ) * sg c1 p := by
  unfold Xb
  have hle : (p - 1) * (2 * w) ≤ p * (2 * w) := Nat.mul_le_mul_right _ (by omega)
  rw [← sum_Ioc_eq _ hle]
  rw [Finset.sum_congr rfl (fun x hx => sstar_cell w p x hw hp (mem_Ioc.mp hx).1 (mem_Ioc.mp hx).2)]
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  have : p * (2 * w) - (p - 1) * (2 * w) = 2 * w := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    have : (p' + 1) * (2 * w) = p' * (2 * w) + 2 * w := by ring
    simp only [Nat.add_sub_cancel]
    omega
  rw [this]
  push_cast
  ring

/-- the closed form of `T = Σ_{q,p ≤ 548} K4 548 p q σ_p σ_q` through the column sums of `K4`
(lower blocks `q ≤ 274` and upper blocks `274 + q`). -/
def starT : ℤ :=
  ∑ q ∈ Icc 1 274,
    (sg c1 q * (4 * ∑ p ∈ Icc 1 (2 * q - 2), sg c1 p + 3 * sg c1 (2 * q - 1) + sg c1 (2 * q))
      + sg c1 (274 + q) * (4 * (∑ p ∈ Icc 1 (2 * 274), sg c1 p - ∑ p ∈ Icc 1 (2 * q), sg c1 p)
        + 3 * sg c1 (2 * q) + sg c1 (2 * q - 1)))

/-- **The kernel computation.** -/
theorem starT_val : starT = -43840 := by
  unfold starT
  decide +kernel

lemma T_eq_starT :
    ∑ q ∈ Icc 1 (2 * 274), sg c1 q * ∑ p ∈ Icc 1 (2 * 274), (K4 (2 * 274) p q : ℤ) * sg c1 p = starT := by
  rw [sum_halves]
  unfold starT
  apply Finset.sum_congr rfl
  intro q hq
  have hq' := mem_Icc.mp hq
  rw [KS_lo 274 q _ hq'.1 hq'.2, KS_hi 274 q _ hq'.1 hq'.2]

/-- **`Wm` of the PRS colouring**, integer form: `Wm s* ≥ -43840 w² - 1096 w - 2192` at `n = 1096 w`. -/
theorem Wm_sstar_lower (w : ℕ) (hw : 1 ≤ w) :
    -43840 * (w : ℤ) ^ 2 - 1096 * w - 2192 ≤ Wm (sstar w) (nn w) := by
  have hs : ∀ x, |sstar w x| ≤ 1 := fun x => sg_abs _ x
  have key := W_lower (sstar w) hs 274 w
  have hn : 2 * (274 * (2 * w)) = nn w := by unfold nn; ring
  rw [hn] at key
  have hX : ∀ p ∈ Icc 1 (2 * 274), Xb (sstar w) (2 * w) p = 2 * (w : ℤ) * sg c1 p :=
    fun p hp => Xb_sstar w p hw (mem_Icc.mp hp).1
  have inner : ∀ q, ∑ p ∈ Icc 1 (2 * 274), (K4 (2 * 274) p q : ℤ) * Xb (sstar w) (2 * w) p
      = 2 * (w : ℤ) * ∑ p ∈ Icc 1 (2 * 274), (K4 (2 * 274) p q : ℤ) * sg c1 p := by
    intro q
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hX p hp]
    ring
  have e1 : ∑ q ∈ Icc 1 (2 * 274), Xb (sstar w) (2 * w) q
        * ∑ p ∈ Icc 1 (2 * 274), (K4 (2 * 274) p q : ℤ) * Xb (sstar w) (2 * w) p
      = (2 * (w : ℤ)) ^ 2 * ∑ q ∈ Icc 1 (2 * 274), sg c1 q
        * ∑ p ∈ Icc 1 (2 * 274), (K4 (2 * 274) p q : ℤ) * sg c1 p := by
    simp only [inner]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [hX q hq]
    ring
  have e2 : ∑ p ∈ Icc 1 (2 * 274), ((2 * (w : ℤ)) ^ 2 - Xb (sstar w) (2 * w) p ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [hX p hp]
    have := sg_sq c1 p
    nlinarith [this]
  rw [e1, e2, T_eq_starT, starT_val] at key
  push_cast at key
  nlinarith [key]

/-- **`StarOK`** (the interface proposition of `P1186Ex.lean`), with `C = 3288`. -/
theorem starOK : StarOK := by
  refine ⟨3288, fun w hw => ?_⟩
  have h := Wm_sstar_lower w hw
  have hR : ((-43840 * (w : ℤ) ^ 2 - 1096 * w - 2192 : ℤ) : ℝ) ≤ (Wm (sstar w) (nn w) : ℝ) := by
    exact_mod_cast h
  push_cast at hR
  have hn : ((nn w : ℕ) : ℝ) = 1096 * w := by unfold nn; push_cast; ring
  rw [hn]
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  nlinarith [hR, hw']

end Erdos1186Ex

#print axioms Erdos1186Ex.starT_val
#print axioms Erdos1186Ex.Wm_sstar_lower
#print axioms Erdos1186Ex.starOK
