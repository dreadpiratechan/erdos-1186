import Mathlib
import Erdos.Proofs.P1186Ex

/-!
# Erdos 1186 - the sign table `Usg` of the PRS colouring on unit cells and its prefix sums `FU`

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's.  `Usg k` is the sign of `φ*` on the `k`-th unit cell `(k w, (k+1) w]` (cells of length `w`, `k = 0..1095`);
`FU k = ∑_{x<k} Usg x` is given in closed form (12 blocks) and checked against its recursion by `decide +kernel`.
-/

namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2

/-- sign of the `k`-th unit cell (0-indexed, cell `k` = `(k w, (k+1) w]`). -/
def Usg (k : ℕ) : ℤ := sg c1 (k / 2 + 1)

/-- length of `[a, b) ∩ [0, k)`. -/
def segN (a b k : ℕ) : ℕ := (bif Nat.ble k b then k else b) - (bif Nat.ble k a then k else a)

/-- prefix sums of `Usg` (block edges `0, 56, 68, 124, 198, 316, 548, 780, 898, 972, 1028, 1040, 1096`). -/
def FU (k : ℕ) : ℤ :=
  (segN 0 56 k : ℤ) - segN 56 68 k + segN 68 124 k - segN 124 198 k + segN 198 316 k - segN 316 548 k
    + segN 548 780 k - segN 780 898 k + segN 898 972 k - segN 972 1028 k + segN 1028 1040 k - segN 1040 1096 k

theorem FU_zero : FU 0 = 0 := by decide +kernel

def chkFU (a b : ℕ) : Bool := (List.range' a (b - a)).all (fun k => decide (FU (k + 1) = FU k + Usg k))

theorem chkFU_a : chkFU 0 366 = true := by decide +kernel
theorem chkFU_b : chkFU 366 731 = true := by decide +kernel
theorem chkFU_c : chkFU 731 1096 = true := by decide +kernel

theorem FU_succ : ∀ k < 1096, FU (k + 1) = FU k + Usg k := by
  intro k hk
  have h : ∀ a b : ℕ, chkFU a b = true → a ≤ k → k < b → FU (k + 1) = FU k + Usg k := by
    intro a b hc hak hkb
    unfold chkFU at hc
    rw [List.all_eq_true] at hc
    have := hc k (by rw [List.mem_range']; exact ⟨k - a, by omega, by omega⟩)
    exact of_decide_eq_true this
  by_cases h1 : k < 366
  · exact h 0 366 chkFU_a (Nat.zero_le _) h1
  · by_cases h2 : k < 731
    · exact h 366 731 chkFU_b (by omega) h2
    · exact h 731 1096 chkFU_c (by omega) hk

theorem FU_1096 : FU 1096 = 0 := by decide +kernel

lemma Usg_pm (k : ℕ) : Usg k = 1 ∨ Usg k = -1 := by
  unfold Usg sg; split_ifs <;> simp

lemma Usg_pair (k : ℕ) : Usg (2 * k + 1) = Usg (2 * k) := by
  unfold Usg; congr 2; omega

end Erdos1186Ex
