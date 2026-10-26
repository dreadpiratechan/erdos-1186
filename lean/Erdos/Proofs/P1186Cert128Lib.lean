import Mathlib
import Erdos.Proofs.P1186Prs

/-!
# Erdos 1186 - kernel-checkable diagonal certificates for the PRS08 lower bound (night 2, lane lean1186b)

Generic library behind `P1186Cert128*.lean` (the `L = 128` certificate) and any other size.  Nothing here is
specific to `L = 128`; all numbers live in the generated table modules.

**What is certified.**  `Erdos1186Night2.DiagCert L d` (see `P1186Prs.lean`) says `d ≥ 0` on `1..L` and
`-(∑ d_i x_i²) ≤ xᵀ A x` for every real `x`, i.e. `A + diag d ⪰ 0`.  With `d_i = dn_i / Q` this is
`M := Q·A + diag dn ⪰ 0`, `M` an integer matrix.

**The certificate** (`CertData`): a scale `S > 0`, integer rows `c_i` (row `i` is the list `c_{i,1}, …, c_{i,i}`
of an approximate Cholesky factor `C`, so `G_ij = ⟨c_i, c_j⟩ = (C Cᵀ)_ij`), and the residual
`E = S·M − G` (an integer matrix, symmetric).  If every row of `E` is diagonally dominant,
`∑_j |E_ij| ≤ 2 E_ii`, then for real `x`

  `S · xᵀ M x = ∑_k (∑_i C_ik x_i)² + xᵀ E x ≥ 0`.

So the only things the kernel has to check are the integer inequalities `∑_j |E_ij| ≤ 2 E_ii`
(`rowOK`, evaluated by `decide +kernel`, in chunks of rows over several modules); there is no floating point
and the rounding in the generator is irrelevant to soundness.  Axioms: only `propext, Classical.choice,
Quot.sound` (no `native_decide`).
-/

namespace Erdos1186Night2

open Finset

/-- Dot product of two integer lists (truncating to the shorter one). -/
def dotL : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a * b + dotL as bs
  | _, _ => 0

theorem dotL_comm : ∀ a b : List ℤ, dotL a b = dotL b a
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
      simp only [dotL]
      rw [dotL_comm as bs, mul_comm]

theorem dotL_eq_sum : ∀ (a b : List ℤ) (n : ℕ), a.length ≤ n →
    dotL a b = ∑ k ∈ range n, a.getD k 0 * b.getD k 0
  | [], b, n, _ => by
      cases b <;> simp [dotL]
  | x :: as, b, n, h => by
      cases n with
      | zero => simp at h
      | succ m =>
        cases b with
        | nil => simp [dotL]
        | cons y bs =>
          have ih := dotL_eq_sum as bs m (by simpa using h)
          rw [Finset.sum_range_succ']
          simp [dotL, ih]
          ring

/-- The data of a diagonal-dominance certificate. -/
structure CertData where
  L : ℕ
  Q : ℤ
  S : ℤ
  dn : List ℤ
  rows : List (List ℤ)

namespace CertData

/-- Row `i` (1-indexed) of the approximate Cholesky factor. -/
def row (T : CertData) (i : ℕ) : List ℤ := T.rows.getD (i - 1) []

/-- `dn_i` (1-indexed). -/
def dnAt (T : CertData) (i : ℕ) : ℤ := T.dn.getD (i - 1) 0

/-- The integer matrix `Q·A + diag dn`, entry `(i, j)` (`dni` is `dn_i`). -/
def matAt (L : ℕ) (Q dni : ℤ) (i j : ℕ) : ℤ := Q * (Aprs L i j : ℤ) + if i = j then dni else 0

/-- The residual `S·M - ⟨c_i, c_j⟩`. -/
def Eraw (L : ℕ) (Q S dni : ℤ) (i j : ℕ) (ri rj : List ℤ) : ℤ :=
  S * matAt L Q dni i j - dotL ri rj

def Mat (T : CertData) (i j : ℕ) : ℤ := matAt T.L T.Q (T.dnAt i) i j

def E (T : CertData) (i j : ℕ) : ℤ := Eraw T.L T.Q T.S (T.dnAt i) i j (T.row i) (T.row j)

/-- `∑_j |E_ij|`, `j` running over the rows from `j0` on (executable, one list traversal). -/
def absRowSum (L : ℕ) (Q S dni : ℤ) (i : ℕ) (ri : List ℤ) : ℕ → List (List ℤ) → ℕ
  | _, [] => 0
  | j, rj :: rest => (Eraw L Q S dni i j ri rj).natAbs + absRowSum L Q S dni i ri (j + 1) rest

/-- Row `i` is diagonally dominant: `∑_j |E_ij| ≤ 2 E_ii`.  (Executable.) -/
def rowOK (T : CertData) (i : ℕ) : Bool :=
  decide (((absRowSum T.L T.Q T.S (T.dnAt i) i (T.row i) 1 T.rows : ℕ) : ℤ) ≤ 2 * T.E i i)

theorem Mat_comm (T : CertData) (i j : ℕ) : T.Mat i j = T.Mat j i := by
  unfold Mat matAt
  by_cases h : i = j
  · subst h; rfl
  · have h' : ¬ j = i := fun e => h e.symm
    simp [h, h', Aprs, add_comm]

theorem E_comm (T : CertData) (i j : ℕ) : T.E i j = T.E j i := by
  unfold E Eraw
  have := T.Mat_comm i j
  unfold Mat at this
  rw [this, dotL_comm]

theorem absRowSum_eq (L : ℕ) (Q S dni : ℤ) (i : ℕ) (ri : List ℤ) :
    ∀ (rows : List (List ℤ)) (j0 : ℕ),
      ((absRowSum L Q S dni i ri j0 rows : ℕ) : ℤ) =
        ∑ t ∈ range rows.length, |Eraw L Q S dni i (j0 + t) ri (rows.getD t [])|
  | [], j0 => by simp [absRowSum]
  | rj :: rest, j0 => by
      have ih := absRowSum_eq L Q S dni i ri rest (j0 + 1)
      have hsum : ∑ t ∈ range rest.length, |Eraw L Q S dni i (j0 + 1 + t) ri (rest.getD t [])| =
          ∑ t ∈ range rest.length, |Eraw L Q S dni i (j0 + (t + 1)) ri (rest.getD t [])| := by
        apply Finset.sum_congr rfl
        intro t _
        rw [show j0 + 1 + t = j0 + (t + 1) by omega]
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [absRowSum, List.getD_cons_succ, List.getD_cons_zero, add_zero]
      push_cast
      rw [ih, hsum, add_comm]

theorem rowOK_sound (T : CertData) (hrows : T.rows.length = T.L) (i : ℕ)
    (h : T.rowOK i = true) :
    ∑ j ∈ Icc 1 T.L, |T.E i j| ≤ 2 * T.E i i := by
  unfold rowOK at h
  have h' := of_decide_eq_true h
  have key := absRowSum_eq T.L T.Q T.S (T.dnAt i) i (T.row i) T.rows 1
  rw [key, hrows] at h'
  have : ∑ j ∈ Icc 1 T.L, |T.E i j| =
      ∑ t ∈ range T.L, |Eraw T.L T.Q T.S (T.dnAt i) i (1 + t) (T.row i) (T.rows.getD t [])| := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    rw [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro t _
    simp [E, row]
  rw [this]
  exact h'

end CertData

/-! ### Real analysis: diagonal dominance and Gram matrices -/

/-- A symmetric real matrix with `∑_j |E_ij| ≤ 2 E_ii` is positive semidefinite. -/
theorem psd_of_dom (L : ℕ) (E : ℕ → ℕ → ℝ) (hsym : ∀ i j, E i j = E j i)
    (hdom : ∀ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |E i j| ≤ 2 * E i i) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, E i j * x i * x j := by
  have key : ∀ i j, 0 ≤ E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
      - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0) := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
      ring_nf
      exact le_refl _
    · simp only [h, if_false, sub_zero]
      rcases abs_cases (E i j) with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]
        nlinarith [sq_nonneg (x i + x j), abs_nonneg (E i j)]
      · rw [h1]
        have := abs_nonneg (E i j)
        rw [h1] at this
        nlinarith [sq_nonneg (x i - x j)]
  have h1 : 0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
      - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => key i j
  -- the three pieces
  have hA : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |E i j| / 2 * x i ^ 2 =
      ∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, ← Finset.sum_div]
  have hB : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |E i j| / 2 * x j ^ 2 =
      ∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, ← Finset.sum_div]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym]
  have hC : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (if i = j then (E i i + |E i i|) * x i ^ 2 else 0) =
      ∑ i ∈ Icc 1 L, (E i i + |E i i|) * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_ite_eq]
    simp [hi]
  have hsplit : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
      - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0)) =
      (∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, E i j * x i * x j)
      + (∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2) * 2
      - ∑ i ∈ Icc 1 L, (E i i + |E i i|) * x i ^ 2 := by
    have e1 : ∀ i j, E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
        - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0)
        = E i j * x i * x j + (|E i j| / 2 * x i ^ 2 + |E i j| / 2 * x j ^ 2)
          - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0) := fun i j => by ring
    simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, hA, hB, hC]
    ring
  rw [hsplit] at h1
  have h2 : ∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2 ≤
      ∑ i ∈ Icc 1 L, E i i * x i ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have := hdom i hi
    have hx := sq_nonneg (x i)
    nlinarith
  have h3 : 0 ≤ ∑ i ∈ Icc 1 L, (|E i i| - E i i) * x i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [le_abs_self (E i i)]) (sq_nonneg _)
  have h4 : ∑ i ∈ Icc 1 L, (E i i + |E i i|) * x i ^ 2 =
      ∑ i ∈ Icc 1 L, E i i * x i ^ 2 + ∑ i ∈ Icc 1 L, |E i i| * x i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h5 : ∑ i ∈ Icc 1 L, (|E i i| - E i i) * x i ^ 2 =
      ∑ i ∈ Icc 1 L, |E i i| * x i ^ 2 - ∑ i ∈ Icc 1 L, E i i * x i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

/-- Gram form: `∑_ij (∑_k c_ik c_jk) x_i x_j = ∑_k (∑_i c_ik x_i)² ≥ 0`. -/
theorem gram_nonneg (L n : ℕ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (∑ k ∈ range n, c i k * c j k) * x i * x j := by
  have e : ∀ i j, (∑ k ∈ range n, c i k * c j k) * x i * x j =
      ∑ k ∈ range n, (c i k * x i) * (c j k * x j) := by
    intro i j
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (∑ k ∈ range n, c i k * c j k) * x i * x j =
      ∑ k ∈ range n, (∑ i ∈ Icc 1 L, c i k * x i) ^ 2 := by
    simp only [e, sq, Finset.sum_mul_sum]
    calc _ = ∑ i ∈ Icc 1 L, ∑ k ∈ range n, ∑ j ∈ Icc 1 L, (c i k * x i) * (c j k * x j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [this]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

namespace CertData

/-- The quadratic form of the integer matrix `M = Q·A + diag dn` is nonnegative. -/
theorem psd (T : CertData) (hS : 0 < T.S)
    (hlen : ∀ i ∈ Icc 1 T.L, (T.row i).length ≤ T.L)
    (hdom : ∀ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, |T.E i j| ≤ 2 * T.E i i) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, ((T.Mat i j : ℤ) : ℝ) * x i * x j := by
  set c : ℕ → ℕ → ℝ := fun i k => (((T.row i).getD k 0 : ℤ) : ℝ) with hc
  set Er : ℕ → ℕ → ℝ := fun i j => ((T.E i j : ℤ) : ℝ) with hEr
  have hG := gram_nonneg T.L T.L c x
  have hE := psd_of_dom T.L Er (fun i j => by simp only [hEr]; rw [T.E_comm])
    (fun i hi => by
      have := hdom i hi
      simp only [hEr]
      exact_mod_cast this) x
  -- S * M = G + E entrywise
  have hME : ∀ i ∈ Icc 1 T.L, ∀ j ∈ Icc 1 T.L,
      (T.S : ℝ) * ((T.Mat i j : ℤ) : ℝ) = (∑ k ∈ range T.L, c i k * c j k) + Er i j := by
    intro i hi j _
    have hd : dotL (T.row i) (T.row j) = ∑ k ∈ range T.L, (T.row i).getD k 0 * (T.row j).getD k 0 :=
      dotL_eq_sum _ _ _ (hlen i hi)
    have : T.S * T.Mat i j = dotL (T.row i) (T.row j) + T.E i j := by
      unfold E Eraw Mat; ring
    have h2 : ((T.S * T.Mat i j : ℤ) : ℝ) = ((dotL (T.row i) (T.row j) + T.E i j : ℤ) : ℝ) := by
      rw [this]
    rw [hd] at h2
    simp only [hc, hEr]
    push_cast at h2 ⊢
    linarith
  have hsum : (T.S : ℝ) * ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, ((T.Mat i j : ℤ) : ℝ) * x i * x j =
      (∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, (∑ k ∈ range T.L, c i k * c j k) * x i * x j)
      + ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, Er i j * x i * x j := by
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
    rw [hsum]; exact add_nonneg hG hE
  exact (mul_nonneg_iff_of_pos_left hSpos).mp this

/-- The diagonal certificate `d_i = dn_i / Q` for `A + diag d ⪰ 0`. -/
theorem diagCert (T : CertData) (hQ : 0 < T.Q) (hS : 0 < T.S)
    (hdn : ∀ i ∈ Icc 1 T.L, 0 ≤ T.dnAt i)
    (hlen : ∀ i ∈ Icc 1 T.L, (T.row i).length ≤ T.L)
    (hdom : ∀ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, |T.E i j| ≤ 2 * T.E i i) :
    DiagCert T.L (fun i => ((T.dnAt i : ℤ) : ℚ) / ((T.Q : ℤ) : ℚ)) := by
  have hQr : (0 : ℝ) < T.Q := by exact_mod_cast hQ
  refine ⟨fun i hi => ?_, fun x => ?_⟩
  · have h1 : (0 : ℚ) ≤ ((T.dnAt i : ℤ) : ℚ) := by exact_mod_cast hdn i hi
    have h2 : (0 : ℚ) ≤ ((T.Q : ℤ) : ℚ) := by exact_mod_cast hQ.le
    exact div_nonneg h1 h2
  · have hp := T.psd hS hlen hdom x
    -- expand the matrix
    have hexp : ∑ i ∈ Icc 1 T.L, ∑ j ∈ Icc 1 T.L, ((T.Mat i j : ℤ) : ℝ) * x i * x j =
        (T.Q : ℝ) * qform T.L x + ∑ i ∈ Icc 1 T.L, ((T.dnAt i : ℤ) : ℝ) * x i ^ 2 := by
      unfold qform
      rw [Finset.mul_sum]
      have e1 : ∀ i j, ((T.Mat i j : ℤ) : ℝ) * x i * x j =
          (T.Q : ℝ) * ((Aprs T.L i j : ℝ) * x i * x j) + (if i = j then ((T.dnAt i : ℤ) : ℝ) * x i ^ 2 else 0) := by
        intro i j
        unfold Mat matAt
        by_cases h : i = j
        · subst h; push_cast; simp; ring
        · simp [h]; ring
      simp only [e1, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_ite_eq]
      simp [hi]
    rw [hexp] at hp
    have hsum : ∑ i ∈ Icc 1 T.L, (((fun i => ((T.dnAt i : ℤ) : ℚ) / ((T.Q : ℤ) : ℚ)) i : ℚ) : ℝ) * x i ^ 2 =
        (∑ i ∈ Icc 1 T.L, ((T.dnAt i : ℤ) : ℝ) * x i ^ 2) / (T.Q : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    rw [hsum]
    have : -((∑ i ∈ Icc 1 T.L, ((T.dnAt i : ℤ) : ℝ) * x i ^ 2) / (T.Q : ℝ)) ≤ qform T.L x := by
      rw [neg_le, le_div_iff₀ hQr]
      nlinarith
    exact this

end CertData

end Erdos1186Night2
