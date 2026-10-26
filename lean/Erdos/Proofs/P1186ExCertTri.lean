import Mathlib
import Erdos.Proofs.P1186ExCertChk
import Erdos.Proofs.P1186M2CertLib

/-!
# Erdos 1186 - the triangle terms of the certificates (lane excert, night 3)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is
its author's.  Hand-written, no certificate numbers.

A triangle form is `tri = 1 + s1 u_i u_j + s2 u_j u_k + s3 u_i u_k` with `u_a = 1 - 2 y_a` and signs of product `+1`;
it is `>= 0` on the cube (`triv_nonneg`).  Its coefficients in `evq` are `tc`, `tl`, `tq` (`evq_tri`); for a list of
weighted triangles the summed coefficients `cS`, `lS`, `qS` give `evq_triS`.  How the (thousands of) sums are checked
in the kernel is in `P1186ExCertPk.lean`.
-/

namespace Erdos1186Ex

open Finset Erdos1186Night2M2

/-! ### One triangle -/

structure TriT where
  i : ℕ
  j : ℕ
  k : ℕ
  s1 : ℤ
  s2 : ℤ
  s3 : ℤ
  w : ℤ

def TriT.ok (n : ℕ) (t : TriT) : Bool :=
  decide (t.i < n ∧ t.j < n ∧ t.k < n ∧ (t.s1 = 1 ∨ t.s1 = -1) ∧ (t.s2 = 1 ∨ t.s2 = -1) ∧
    (t.s3 = 1 ∨ t.s3 = -1) ∧ t.s1 * t.s2 * t.s3 = 1 ∧ 0 ≤ t.w)

noncomputable def triv (t : TriT) (y : ℕ → ℝ) : ℝ :=
  1 + (t.s1 : ℝ) * ((1 - 2 * y t.i) * (1 - 2 * y t.j)) + (t.s2 : ℝ) * ((1 - 2 * y t.j) * (1 - 2 * y t.k))
    + (t.s3 : ℝ) * ((1 - 2 * y t.i) * (1 - 2 * y t.k))

theorem tri_ineq (u v w : ℝ) (s1 s2 s3 : ℤ) (hu1 : -1 ≤ u) (hu2 : u ≤ 1) (hv1 : -1 ≤ v) (hv2 : v ≤ 1)
    (hw1 : -1 ≤ w) (hw2 : w ≤ 1) (h1 : s1 = 1 ∨ s1 = -1) (h2 : s2 = 1 ∨ s2 = -1) (h3 : s3 = 1 ∨ s3 = -1)
    (hp : s1 * s2 * s3 = 1) :
    0 ≤ 1 + (s1 : ℝ) * (u * v) + (s2 : ℝ) * (v * w) + (s3 : ℝ) * (u * w) := by
  have pu : 0 ≤ 1 + u := by linarith
  have mu : 0 ≤ 1 - u := by linarith
  have pv : 0 ≤ 1 + v := by linarith
  have mv : 0 ≤ 1 - v := by linarith
  have pw : 0 ≤ 1 + w := by linarith
  have mw : 0 ≤ 1 - w := by linarith
  have A := mul_nonneg (mul_nonneg pu pv) pw
  have B := mul_nonneg (mul_nonneg mu mv) mw
  have C := mul_nonneg (mul_nonneg pu pv) mw
  have D := mul_nonneg (mul_nonneg mu mv) pw
  have E := mul_nonneg (mul_nonneg pu mv) mw
  have F := mul_nonneg (mul_nonneg mu pv) pw
  have G := mul_nonneg (mul_nonneg pu mv) pw
  have H := mul_nonneg (mul_nonneg mu pv) mw
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    first
    | (exfalso; norm_num at hp; done)
    | (push_cast; nlinarith [A, B, C, D, E, F, G, H])

theorem triv_nonneg (t : TriT) (n : ℕ) (ht : t.ok n = true) (y : ℕ → ℝ) (hy : ∀ i < n, 0 ≤ y i ∧ y i ≤ 1) :
    0 ≤ triv t y := by
  unfold TriT.ok at ht
  obtain ⟨hi, hj, hk, h1, h2, h3, hp, _⟩ := of_decide_eq_true ht
  obtain ⟨a0, a1⟩ := hy t.i hi
  obtain ⟨b0, b1⟩ := hy t.j hj
  obtain ⟨c0, c1⟩ := hy t.k hk
  unfold triv
  exact tri_ineq (1 - 2 * y t.i) (1 - 2 * y t.j) (1 - 2 * y t.k) t.s1 t.s2 t.s3 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) h1 h2 h3 hp

/-! ### Coefficients of one triangle in `evq` -/

def tc (t : TriT) : ℤ := 1 + t.s1 + t.s2 + t.s3

def tl (t : TriT) (a : ℕ) : ℤ :=
  -2 * ((if a = t.i then t.s1 + t.s3 else 0) + (if a = t.j then t.s1 + t.s2 else 0)
    + (if a = t.k then t.s2 + t.s3 else 0))

def tq (t : TriT) (a b : ℕ) : ℤ :=
  4 * ((if a = t.i ∧ b = t.j then t.s1 else 0) + (if a = t.j ∧ b = t.k then t.s2 else 0)
    + (if a = t.i ∧ b = t.k then t.s3 else 0))

theorem sum_if_eq (n i : ℕ) (hi : i < n) (f : ℕ → ℝ) :
    ∑ a ∈ range n, (if a = i then f a else 0) = f i := by
  rw [Finset.sum_ite_eq']
  simp [hi]

theorem sum2_if (n i j : ℕ) (hi : i < n) (hj : j < n) (f : ℕ → ℕ → ℝ) :
    ∑ a ∈ range n, ∑ b ∈ range n, (if a = i ∧ b = j then f a b else 0) = f i j := by
  have : ∀ a b : ℕ, (if a = i ∧ b = j then f a b else 0) = if a = i then (if b = j then f a b else 0) else 0 := by
    intro a b
    by_cases h1 : a = i <;> by_cases h2 : b = j <;> simp [h1, h2]
  simp only [this]
  have e : ∀ a ∈ range n, ∑ b ∈ range n, (if a = i then (if b = j then f a b else 0) else 0)
      = if a = i then f a j else 0 := by
    intro a _
    by_cases h1 : a = i
    · simp only [h1, if_true]
      rw [Finset.sum_ite_eq']
      simp [hj]
    · simp [h1]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq']
  simp [hi]

theorem evq_tri (n : ℕ) (t : TriT) (hi : t.i < n) (hj : t.j < n) (hk : t.k < n) (y : ℕ → ℝ) :
    evq n (tc t) (tl t) (tq t) y = triv t y := by
  unfold evq
  have hl : ∑ a ∈ range n, ((tl t a : ℤ) : ℝ) * y a
      = (∑ a ∈ range n, (if a = t.i then -2 * ((t.s1 : ℝ) + t.s3) * y a else 0))
        + (∑ a ∈ range n, (if a = t.j then -2 * ((t.s1 : ℝ) + t.s2) * y a else 0))
        + (∑ a ∈ range n, (if a = t.k then -2 * ((t.s2 : ℝ) + t.s3) * y a else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    unfold tl
    push_cast
    split_ifs <;> ring
  have hq : ∑ a ∈ range n, ∑ b ∈ range n, ((tq t a b : ℤ) : ℝ) * (y a * y b)
      = (∑ a ∈ range n, ∑ b ∈ range n, (if a = t.i ∧ b = t.j then 4 * (t.s1 : ℝ) * (y a * y b) else 0))
        + (∑ a ∈ range n, ∑ b ∈ range n, (if a = t.j ∧ b = t.k then 4 * (t.s2 : ℝ) * (y a * y b) else 0))
        + (∑ a ∈ range n, ∑ b ∈ range n, (if a = t.i ∧ b = t.k then 4 * (t.s3 : ℝ) * (y a * y b) else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    unfold tq
    push_cast
    split_ifs <;> ring
  rw [hl, hq, sum_if_eq n t.i hi, sum_if_eq n t.j hj, sum_if_eq n t.k hk,
    sum2_if n t.i t.j hi hj (fun a b => 4 * (t.s1 : ℝ) * (y a * y b)),
    sum2_if n t.j t.k hj hk (fun a b => 4 * (t.s2 : ℝ) * (y a * y b)),
    sum2_if n t.i t.k hi hk (fun a b => 4 * (t.s3 : ℝ) * (y a * y b))]
  unfold triv tc
  push_cast
  ring

/-! ### Sums over a list of triangles -/

def cS (ts : List TriT) : ℤ := (ts.map (fun t => t.w * tc t)).sum
def lS (ts : List TriT) (a : ℕ) : ℤ := (ts.map (fun t => t.w * tl t a)).sum
def qS (ts : List TriT) (a b : ℕ) : ℤ := (ts.map (fun t => t.w * tq t a b)).sum

theorem evq_triS (n : ℕ) (y : ℕ → ℝ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) →
    evq n (cS ts) (lS ts) (qS ts) y = (ts.map (fun t => (t.w : ℝ) * triv t y)).sum
  | [], _ => by simp [cS, lS, qS, evq]
  | t :: ts, h => by
      have ht : t.ok n = true := h t (by simp)
      have hts : ∀ s ∈ ts, s.ok n = true := fun s hs => h s (by simp [hs])
      have ih := evq_triS n y ts hts
      unfold TriT.ok at ht
      obtain ⟨hi, hj, hk, _⟩ := of_decide_eq_true ht
      have e1 := evq_tri n t hi hj hk y
      have e2 := evq_smul n t.w (tc t) (tl t) (tq t) y
      have e3 := evq_add n (t.w * tc t) (cS ts) (fun a => t.w * tl t a) (lS ts) (fun a b => t.w * tq t a b)
        (qS ts) y
      have hc : cS (t :: ts) = t.w * tc t + cS ts := by simp [cS]
      have hl : lS (t :: ts) = fun a => t.w * tl t a + lS ts a := by funext a; simp [lS]
      have hq : qS (t :: ts) = fun a b => t.w * tq t a b + qS ts a b := by funext a b; simp [qS]
      rw [hc, hl, hq, e3, ← e2, e1, ih]
      simp

theorem list_sum_nonneg_of (n : ℕ) (y : ℕ → ℝ) (hy : ∀ i < n, 0 ≤ y i ∧ y i ≤ 1) :
    ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) → 0 ≤ (ts.map (fun t => (t.w : ℝ) * triv t y)).sum
  | [], _ => by simp
  | t :: ts, h => by
      have ht : t.ok n = true := h t (by simp)
      have hts : ∀ s ∈ ts, s.ok n = true := fun s hs => h s (by simp [hs])
      have ih := list_sum_nonneg_of n y hy ts hts
      have hw : (0 : ℝ) ≤ t.w := by
        unfold TriT.ok at ht
        obtain ⟨_, _, _, _, _, _, _, hw⟩ := of_decide_eq_true ht
        exact_mod_cast hw
      have := mul_nonneg hw (triv_nonneg t n ht y hy)
      simp only [List.map_cons, List.sum_cons]
      linarith

end Erdos1186Ex
