import Mathlib
import Erdos.Proofs.P1186ExCertLib

/-!
# Erdos 1186 - algebra of the `RegionLB` certificates (lane excert, night 3)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is
its author's.  Hand-written, no certificate numbers.  Part B of `P1186ExCertLib.lean`:

* the form side: `FSr` (the nonnegative combination of atom products) is `≥ 0` on the region and
  `U · FSr = evq cF lF qF` (the integer coefficients are explicit functions of the form tables);
* the pair side: `Dz · Lval ≥ PS` and `U · PS = evq cP lP qP`.
-/

namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

/-! ### Affine functions and the double-sum expansion -/

/-- `c + Σ_k e_k y_k`. -/
noncomputable def afn (n : ℕ) (c : ℤ) (e : ℕ → ℤ) (y : ℕ → ℝ) : ℝ := (c : ℝ) + ∑ k ∈ range n, (e k : ℝ) * y k

theorem afn_mul (n : ℕ) (c d : ℤ) (e f : ℕ → ℤ) (y : ℕ → ℝ) :
    afn n c e y * afn n d f y = evq n (c * d) (fun i => c * f i + d * e i) (fun i j => e i * f j) y := by
  unfold afn evq
  have h1 : ∑ i ∈ range n, (((c * f i + d * e i : ℤ) : ℝ)) * y i
      = (c : ℝ) * ∑ i ∈ range n, (f i : ℝ) * y i + (d : ℝ) * ∑ i ∈ range n, (e i : ℝ) * y i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  have h2 : (∑ i ∈ range n, (e i : ℝ) * y i) * ∑ j ∈ range n, (f j : ℝ) * y j
      = ∑ i ∈ range n, ∑ j ∈ range n, ((e i * f j : ℤ) : ℝ) * (y i * y j) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [h1, ← h2]
  push_cast
  ring

theorem sum2_aff (n : ℕ) (u t u' t' : ℤ) (C : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (C i j : ℝ) * (((u : ℝ) + t * y i) * ((u' : ℝ) + t' * y j))
      = evq n (u * u' * ∑ i ∈ range n, ∑ j ∈ range n, C i j)
          (fun a => u * t' * (∑ i ∈ range n, C i a) + t * u' * (∑ j ∈ range n, C a j))
          (fun i j => t * t' * C i j) y := by
  unfold evq
  have key : ∀ i j, (C i j : ℝ) * (((u : ℝ) + t * y i) * ((u' : ℝ) + t' * y j))
      = ((u * u' : ℤ) : ℝ) * (C i j : ℝ) + ((u * t' : ℤ) : ℝ) * (C i j : ℝ) * y j
        + ((t * u' : ℤ) : ℝ) * (C i j : ℝ) * y i + ((t * t' * C i j : ℤ) : ℝ) * (y i * y j) := by
    intro i j
    push_cast
    ring
  simp only [key, Finset.sum_add_distrib]
  have e1 : ∑ i ∈ range n, ∑ j ∈ range n, ((u * u' : ℤ) : ℝ) * (C i j : ℝ)
      = ((u * u' * ∑ i ∈ range n, ∑ j ∈ range n, C i j : ℤ) : ℝ) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have e2 : ∑ i ∈ range n, ∑ j ∈ range n, ((u * t' : ℤ) : ℝ) * (C i j : ℝ) * y j
      = ∑ a ∈ range n, ((u * t' * ∑ i ∈ range n, C i a : ℤ) : ℝ) * y a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  have e3 : ∑ i ∈ range n, ∑ j ∈ range n, ((t * u' : ℤ) : ℝ) * (C i j : ℝ) * y i
      = ∑ a ∈ range n, ((t * u' * ∑ j ∈ range n, C a j : ℤ) : ℝ) * y a := by
    apply Finset.sum_congr rfl
    intro a _
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [e1, e2, e3]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-! ### The form side -/

/-- The form tables (already multiplied by the common factor), and the integer data of `R·m`, `R·lo`, `R·hi`. -/
structure FD where
  n : ℕ
  Yv : ℕ → ℤ
  Ov : ℕ → ℤ
  A1 : ℕ → ℤ
  A2 : ℕ → ℤ
  A3 : ℕ → ℤ
  A4 : ℕ → ℤ
  YY : ℕ → ℕ → ℤ
  OO : ℕ → ℕ → ℤ
  YO : ℕ → ℕ → ℤ
  pp : ℤ
  rr : ℤ
  ss : ℤ
  om : ℕ → ℤ
  Lo : ℤ
  Hi : ℤ

/-- `R = 20 · 1096`, `U = R²`. -/
def Rr : ℤ := 21920
def Uu : ℤ := 21920 * 21920

namespace FD

/-- The nonnegative combination of atom products (atoms `y_i`, `1 - y_i`, `m - lo`, `hi - m`). -/
noncomputable def FSr (d : FD) (m lo hi : ℝ) (y : ℕ → ℝ) : ℝ :=
  (∑ i ∈ range d.n, ((d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i)))
  + ((d.pp : ℝ) * (m - lo) + (d.rr : ℝ) * (hi - m))
  + ∑ i ∈ range d.n, ∑ j ∈ range d.n, ((d.YY i j : ℝ) * (y i * y j)
      + (d.OO i j : ℝ) * ((1 - y i) * (1 - y j)) + (d.YO i j : ℝ) * (y i * (1 - y j)))
  + ∑ i ∈ range d.n, ((d.A1 i : ℝ) * (y i * (m - lo)) + (d.A2 i : ℝ) * ((1 - y i) * (m - lo))
      + (d.A3 i : ℝ) * (y i * (hi - m)) + (d.A4 i : ℝ) * ((1 - y i) * (hi - m)))
  + (d.ss : ℝ) * ((m - lo) * (hi - m))

/-- all multipliers are `≥ 0`. -/
structure Nonneg (d : FD) : Prop where
  Yv : ∀ i < d.n, 0 ≤ d.Yv i
  Ov : ∀ i < d.n, 0 ≤ d.Ov i
  A1 : ∀ i < d.n, 0 ≤ d.A1 i
  A2 : ∀ i < d.n, 0 ≤ d.A2 i
  A3 : ∀ i < d.n, 0 ≤ d.A3 i
  A4 : ∀ i < d.n, 0 ≤ d.A4 i
  YY : ∀ i < d.n, ∀ j < d.n, 0 ≤ d.YY i j
  OO : ∀ i < d.n, ∀ j < d.n, 0 ≤ d.OO i j
  YO : ∀ i < d.n, ∀ j < d.n, 0 ≤ d.YO i j
  pp : 0 ≤ d.pp
  rr : 0 ≤ d.rr
  ss : 0 ≤ d.ss

theorem FSr_nonneg (d : FD) (h : d.Nonneg) (m lo hi : ℝ) (y : ℕ → ℝ) (hy : ∀ i < d.n, 0 ≤ y i ∧ y i ≤ 1)
    (hl : lo ≤ m) (hh : m ≤ hi) : 0 ≤ d.FSr m lo hi y := by
  have ml : 0 ≤ m - lo := by linarith
  have hm : 0 ≤ hi - m := by linarith
  have c : ∀ z : ℤ, 0 ≤ z → (0 : ℝ) ≤ (z : ℝ) := fun z hz => by exact_mod_cast hz
  unfold FSr
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_
  · refine Finset.sum_nonneg fun i hi' => ?_
    have hi'' := Finset.mem_range.mp hi'
    obtain ⟨h0, h1⟩ := hy i hi''
    exact add_nonneg (mul_nonneg (c _ (h.Yv i hi'')) h0) (mul_nonneg (c _ (h.Ov i hi'')) (by linarith))
  · exact add_nonneg (mul_nonneg (c _ h.pp) ml) (mul_nonneg (c _ h.rr) hm)
  · refine Finset.sum_nonneg fun i hi' => Finset.sum_nonneg fun j hj' => ?_
    have hi'' := Finset.mem_range.mp hi'
    have hj'' := Finset.mem_range.mp hj'
    obtain ⟨a0, a1⟩ := hy i hi''
    obtain ⟨b0, b1⟩ := hy j hj''
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact mul_nonneg (c _ (h.YY i hi'' j hj'')) (mul_nonneg a0 b0)
    · exact mul_nonneg (c _ (h.OO i hi'' j hj'')) (mul_nonneg (by linarith) (by linarith))
    · exact mul_nonneg (c _ (h.YO i hi'' j hj'')) (mul_nonneg a0 (by linarith))
  · refine Finset.sum_nonneg fun i hi' => ?_
    have hi'' := Finset.mem_range.mp hi'
    obtain ⟨a0, a1⟩ := hy i hi''
    refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
    · exact mul_nonneg (c _ (h.A1 i hi'')) (mul_nonneg a0 ml)
    · exact mul_nonneg (c _ (h.A2 i hi'')) (mul_nonneg (by linarith) ml)
    · exact mul_nonneg (c _ (h.A3 i hi'')) (mul_nonneg a0 hm)
    · exact mul_nonneg (c _ (h.A4 i hi'')) (mul_nonneg (by linarith) hm)
  · exact mul_nonneg (c _ h.ss) (mul_nonneg ml hm)

/-! #### The integer coefficients of `U · FSr` -/

def u1 (d : FD) (i : ℕ) : ℤ := d.A1 i - d.A2 i
def u2 (d : FD) (i : ℕ) : ℤ := d.A3 i - d.A4 i
def u10 (d : FD) : ℤ := (∑ i ∈ range d.n, d.A2 i) + d.pp
def u20 (d : FD) : ℤ := (∑ i ∈ range d.n, d.A4 i) + d.rr

def cF (d : FD) : ℤ :=
  Uu * ((∑ i ∈ range d.n, d.Ov i) + ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.OO i j)
    + Rr * (-d.Lo * d.u10 + d.Hi * d.u20) - d.ss * d.Lo * d.Hi

def lF (d : FD) (a : ℕ) : ℤ :=
  Uu * (d.Yv a - d.Ov a - (∑ j ∈ range d.n, d.OO a j) - (∑ i ∈ range d.n, d.OO i a) + ∑ j ∈ range d.n, d.YO a j)
    + Rr * (d.om a * d.u10 - d.Lo * d.u1 a - d.om a * d.u20 + d.Hi * d.u2 a)
    + d.ss * d.om a * (d.Lo + d.Hi)

def qF (d : FD) (i j : ℕ) : ℤ :=
  Uu * (d.YY i j + d.OO i j - d.YO i j) + Rr * d.om j * (d.u1 i - d.u2 i) - d.ss * d.om i * d.om j

theorem evq_zero (n : ℕ) (y : ℕ → ℝ) : evq n 0 (fun _ => 0) (fun _ _ => 0) y = 0 := by
  simp [evq]

theorem evq_afn (n : ℕ) (c : ℤ) (e : ℕ → ℤ) (y : ℕ → ℝ) :
    afn n c e y = evq n c e (fun _ _ => 0) y := by
  simp [afn, evq]

/-- `U · FSr = evq cF lF qF`, where `R m = Σ om y`, `R lo = Lo`, `R hi = Hi`. -/
theorem FSr_evq (d : FD) (m lo hi : ℝ) (y : ℕ → ℝ)
    (hm : (Rr : ℝ) * m = ∑ k ∈ range d.n, (d.om k : ℝ) * y k)
    (hlo : (Rr : ℝ) * lo = d.Lo) (hhi : (Rr : ℝ) * hi = d.Hi) :
    (Uu : ℝ) * d.FSr m lo hi y = evq d.n d.cF d.lF d.qF y := by
  have hUR : (Uu : ℝ) = (Rr : ℝ) * (Rr : ℝ) := by norm_num [Uu, Rr]
  have hml : (Rr : ℝ) * (m - lo) = afn d.n (-d.Lo) d.om y := by
    unfold afn
    push_cast
    rw [mul_sub, hm, hlo]
    ring
  have hhm : (Rr : ℝ) * (hi - m) = afn d.n d.Hi (fun k => - d.om k) y := by
    unfold afn
    push_cast
    rw [mul_sub, hm, hhi]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  -- the four groups
  have g1 : ∑ i ∈ range d.n, ((d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i))
      = evq d.n (∑ i ∈ range d.n, d.Ov i) (fun a => d.Yv a - d.Ov a) (fun _ _ => 0) y := by
    unfold evq
    simp only [Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
    have : ∀ i, (d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i)
        = (d.Ov i : ℝ) + ((d.Yv i - d.Ov i : ℤ) : ℝ) * y i := by
      intro i
      push_cast
      ring
    simp only [this, Finset.sum_add_distrib]
    push_cast
    rfl
  have hGml : afn d.n d.u10 d.u1 y
      = (d.pp : ℝ) + ∑ i ∈ range d.n, ((d.A1 i : ℝ) * y i + (d.A2 i : ℝ) * (1 - y i)) := by
    unfold afn FD.u10 FD.u1
    have : ∀ i, (d.A1 i : ℝ) * y i + (d.A2 i : ℝ) * (1 - y i)
        = (d.A2 i : ℝ) + ((d.A1 i - d.A2 i : ℤ) : ℝ) * y i := by
      intro i
      push_cast
      ring
    simp only [this, Finset.sum_add_distrib]
    push_cast
    ring
  have hGhm : afn d.n d.u20 d.u2 y
      = (d.rr : ℝ) + ∑ i ∈ range d.n, ((d.A3 i : ℝ) * y i + (d.A4 i : ℝ) * (1 - y i)) := by
    unfold afn FD.u20 FD.u2
    have : ∀ i, (d.A3 i : ℝ) * y i + (d.A4 i : ℝ) * (1 - y i)
        = (d.A4 i : ℝ) + ((d.A3 i - d.A4 i : ℤ) : ℝ) * y i := by
      intro i
      push_cast
      ring
    simp only [this, Finset.sum_add_distrib]
    push_cast
    ring
  have g2 : (d.pp : ℝ) * (m - lo) + (d.rr : ℝ) * (hi - m)
      + ∑ i ∈ range d.n, ((d.A1 i : ℝ) * (y i * (m - lo)) + (d.A2 i : ℝ) * ((1 - y i) * (m - lo))
        + (d.A3 i : ℝ) * (y i * (hi - m)) + (d.A4 i : ℝ) * ((1 - y i) * (hi - m)))
      = afn d.n d.u10 d.u1 y * (m - lo) + afn d.n d.u20 d.u2 y * (hi - m) := by
    rw [hGml, hGhm]
    have e : ∀ i, (d.A1 i : ℝ) * (y i * (m - lo)) + (d.A2 i : ℝ) * ((1 - y i) * (m - lo))
        + (d.A3 i : ℝ) * (y i * (hi - m)) + (d.A4 i : ℝ) * ((1 - y i) * (hi - m))
        = ((d.A1 i : ℝ) * y i + (d.A2 i : ℝ) * (1 - y i)) * (m - lo)
          + ((d.A3 i : ℝ) * y i + (d.A4 i : ℝ) * (1 - y i)) * (hi - m) := by
      intro i
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  have g3 : ∑ i ∈ range d.n, ∑ j ∈ range d.n, ((d.YY i j : ℝ) * (y i * y j)
      + (d.OO i j : ℝ) * ((1 - y i) * (1 - y j)) + (d.YO i j : ℝ) * (y i * (1 - y j)))
      = evq d.n (0 * 0 * ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.YY i j)
          (fun a => 0 * 1 * (∑ i ∈ range d.n, d.YY i a) + 1 * 0 * (∑ j ∈ range d.n, d.YY a j))
          (fun i j => 1 * 1 * d.YY i j) y
        + evq d.n (1 * 1 * ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.OO i j)
          (fun a => 1 * (-1) * (∑ i ∈ range d.n, d.OO i a) + (-1) * 1 * (∑ j ∈ range d.n, d.OO a j))
          (fun i j => (-1) * (-1) * d.OO i j) y
        + evq d.n (0 * 1 * ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.YO i j)
          (fun a => 0 * (-1) * (∑ i ∈ range d.n, d.YO i a) + 1 * 1 * (∑ j ∈ range d.n, d.YO a j))
          (fun i j => 1 * (-1) * d.YO i j) y := by
    rw [← sum2_aff d.n 0 1 0 1 d.YY y, ← sum2_aff d.n 1 (-1) 1 (-1) d.OO y,
      ← sum2_aff d.n 0 1 1 (-1) d.YO y]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have g5 : (d.ss : ℝ) * ((m - lo) * (hi - m)) * (Uu : ℝ)
      = (d.ss : ℝ) * (afn d.n (-d.Lo) d.om y * afn d.n d.Hi (fun k => - d.om k) y) := by
    rw [← hml, ← hhm, hUR]
    ring
  -- assemble
  have hFS : d.FSr m lo hi y
      = ∑ i ∈ range d.n, ((d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i))
        + ∑ i ∈ range d.n, ∑ j ∈ range d.n, ((d.YY i j : ℝ) * (y i * y j)
          + (d.OO i j : ℝ) * ((1 - y i) * (1 - y j)) + (d.YO i j : ℝ) * (y i * (1 - y j)))
        + (afn d.n d.u10 d.u1 y * (m - lo) + afn d.n d.u20 d.u2 y * (hi - m))
        + (d.ss : ℝ) * ((m - lo) * (hi - m)) := by
    rw [← g2]
    unfold FD.FSr
    ring
  have hG2 : (Uu : ℝ) * (afn d.n d.u10 d.u1 y * (m - lo) + afn d.n d.u20 d.u2 y * (hi - m))
      = (Rr : ℝ) * (afn d.n d.u10 d.u1 y * afn d.n (-d.Lo) d.om y
          + afn d.n d.u20 d.u2 y * afn d.n d.Hi (fun k => - d.om k) y) := by
    rw [← hml, ← hhm, hUR]
    ring
  rw [hFS, mul_add, mul_add, mul_add, hG2, g1, g3, mul_comm (Uu : ℝ) ((d.ss : ℝ) * _), g5,
    afn_mul, afn_mul, afn_mul]
  simp only [mul_add, evq_smul, ← evq_add]
  apply evq_congr
  · unfold FD.cF FD.u10 FD.u20
    ring
  · intro a _
    unfold FD.lF FD.u10 FD.u20 FD.u1 FD.u2
    ring
  · intro i _ j _
    unfold FD.qF FD.u1 FD.u2
    ring

end FD

/-! ### The pair side -/

/-- The data of the pair part: integer accessors of the grid and the table `θ` (numerators over `Qn`). -/
structure PD where
  G : Grid
  lenz : ℕ → ℤ
  sgz : ℕ → ℤ
  alz : ℕ → ℤ
  btz : ℕ → ℤ
  a4z : ℕ → ℕ → ℤ
  th : ℕ → ℕ → ℤ

namespace PD

def sz (d : PD) (i j : ℕ) : ℤ := if d.sgz i * d.sgz j = 1 then 1 else -1

def Kz (d : PD) (i j : ℕ) : ℤ := 300 * (Qn - d.th i j) * d.lenz i * d.lenz j

def cz (d : PD) (i j : ℕ) : ℤ :=
  if d.sgz i * d.sgz j = 1 then 75 * (Qn - d.th i j) * (4 * d.lenz i * d.lenz j - d.a4z i j)
  else 75 * d.th i j * d.a4z i j

/-- the integer-coefficient lower bound of `Dz · Lval`. -/
noncomputable def PS (d : PD) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range d.G.N, ((d.alz i : ℝ) * y i + (d.btz i : ℝ) * y i ^ 2)
    + ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j) - (d.cz i j : ℝ))

/-- the accessors agree with the grid; `θ ∈ [0, Qn]`. -/
structure Ok (d : PD) : Prop where
  len : ∀ i < d.G.N, d.lenz i = (d.G.len i : ℤ)
  sg : ∀ i < d.G.N, d.sgz i = d.G.sgn i
  al : ∀ i < d.G.N, d.G.ai i * (Dz : ℚ) = (d.alz i : ℚ)
  bt : ∀ i < d.G.N, d.G.bi i * (Dz : ℚ) = (d.btz i : ℚ)
  a4 : ∀ i < d.G.N, ∀ j < d.G.N, d.a4z i j = (d.G.A4 i j : ℤ)
  th : ∀ i < d.G.N, ∀ j < d.G.N, 0 ≤ d.th i j ∧ d.th i j ≤ Qn

theorem PS_le (d : PD) (h : d.Ok) (y : ℕ → ℝ) : d.PS y ≤ (Dz : ℝ) * d.G.Lval y := by
  unfold PS Grid.Lval
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  apply add_le_add
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have ha : (d.G.ai i : ℝ) * (Dz : ℝ) = (d.alz i : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (h.al i hi')
      simpa using this
    have hb : (d.G.bi i : ℝ) * (Dz : ℝ) = (d.btz i : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (h.bt i hi')
      simpa using this
    rw [← ha, ← hb]
    ring
  · apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have key := pterm_scaled d.G i j (d.th i j) (h.th i hi' j hj').1 (h.th i hi' j hj').2 (y i) (y j)
    have e1 : sgnP d.G i j * Kp d.G (d.th i j) i j = d.sz i j * d.Kz i j := by
      unfold sgnP Kp sz Kz
      rw [h.len i hi', h.len j hj', h.sg i hi', h.sg j hj']
    have e2 : cp d.G (d.th i j) i j = d.cz i j := by
      unfold cp cz
      rw [A4v_eq, h.len i hi', h.len j hj', h.sg i hi', h.sg j hj', h.a4 i hi' j hj']
    rw [e1, e2] at key
    exact key

/-- the integer coefficients of `U · PS`. -/
def cP (d : PD) : ℤ := -Uu * ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, d.cz i j
def lP (d : PD) (a : ℕ) : ℤ := Uu * d.alz a
def qP (d : PD) (i j : ℕ) : ℤ := Uu * (d.sz i j * d.Kz i j + if i = j then d.btz i else 0)

theorem PS_evq (d : PD) (y : ℕ → ℝ) : (Uu : ℝ) * d.PS y = evq d.G.N d.cP d.lP d.qP y := by
  have e : d.PS y = evq d.G.N (-∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, d.cz i j) d.alz
      (fun i j => d.sz i j * d.Kz i j + if i = j then d.btz i else 0) y := by
    unfold PS evq
    have hb : ∀ i ∈ range d.G.N, (d.btz i : ℝ) * y i ^ 2
        = ∑ j ∈ range d.G.N, (((if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j) := by
      intro i hi
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [sq]
      · intro j _ hji
        simp [Ne.symm hji]
    have hb' : ∑ i ∈ range d.G.N, (d.btz i : ℝ) * y i ^ 2
        = ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j) :=
      Finset.sum_congr rfl hb
    have hc : ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j) - (d.cz i j : ℝ))
        = ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j))
          - ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (d.cz i j : ℝ) := by
      simp only [Finset.sum_sub_distrib]
    rw [hc, Finset.sum_add_distrib, hb']
    have hq : ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j + if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j)
        = ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j))
          + ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hq]
    push_cast
    ring
  rw [e, evq_smul]
  apply evq_congr
  · unfold cP
    ring
  · intro i _
    rfl
  · intro i _ j _
    rfl

end PD

theorem evq_sub3 (n : ℕ) (c c' c'' : ℤ) (l l' l'' : ℕ → ℤ) (q q' q'' : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    evq n (c - c' - c'') (fun i => l i - l' i - l'' i) (fun i j => q i j - q' i j - q'' i j) y
      = evq n c l q y - evq n c' l' q' y - evq n c'' l'' q'' y := by
  unfold evq
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- The abstract certificate theorem: from the integer data to `RegionLB`. -/
theorem region_of_data (pd : PD) (fd : FD) (loN hiN : ℤ)
    (hok : pd.Ok) (hfn : fd.Nonneg) (hn : fd.n = pd.G.N)
    (hom : ∀ i < pd.G.N, fd.om i = 20 * pd.lenz i) (hLo : fd.Lo = 1096 * loN) (hHi : fd.Hi = 1096 * hiN)
    (cT : ℤ) (lT : ℕ → ℤ) (qT : ℕ → ℕ → ℤ)
    (hT : ∀ y : ℕ → ℝ, (∀ i < pd.G.N, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq pd.G.N cT lT qT y)
    (Nm : ℕ → ℕ → ℤ)
    (hpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ a ∈ Icc 1 (pd.G.N + 1), ∑ b ∈ Icc 1 (pd.G.N + 1), (Nm a b : ℝ) * x a * x b)
    (h00 : Uu * Nm 1 1 = pd.cP - fd.cF - cT)
    (h0i : ∀ i < pd.G.N, 2 * Uu * Nm 1 (i + 2) = pd.lP i - fd.lF i - lT i)
    (hi0 : ∀ i < pd.G.N, 2 * Uu * Nm (i + 2) 1 = pd.lP i - fd.lF i - lT i)
    (hij : ∀ i < pd.G.N, ∀ j < pd.G.N, 2 * Uu * Nm (i + 2) (j + 2)
      = (pd.qP i j - fd.qF i j - qT i j) + (pd.qP j i - fd.qF j i - qT j i)) :
    RegionLB pd.G ((loN : ℚ) / 20) ((hiN : ℚ) / 20) := by
  intro y hy hlo hhi
  have hy' : ∀ i < fd.n, 0 ≤ y i ∧ y i ≤ 1 := by
    rw [hn]; exact hy
  -- R m
  have hRm : (Rr : ℝ) * pd.G.mval y = ∑ k ∈ range fd.n, (fd.om k : ℝ) * y k := by
    unfold Grid.mval
    rw [Finset.mul_sum, hn]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [hom k hk', hok.len k hk']
    unfold Grid.wt Rr
    push_cast
    ring
  have hRlo : (Rr : ℝ) * (((loN : ℚ) / 20 : ℚ) : ℝ) = fd.Lo := by
    rw [hLo]; unfold Rr; push_cast; ring
  have hRhi : (Rr : ℝ) * (((hiN : ℚ) / 20 : ℚ) : ℝ) = fd.Hi := by
    rw [hHi]; unfold Rr; push_cast; ring
  have hFS := fd.FSr_nonneg hfn (pd.G.mval y) (((loN : ℚ) / 20 : ℚ) : ℝ) (((hiN : ℚ) / 20 : ℚ) : ℝ) y hy' hlo hhi
  have hFSe := FD.FSr_evq fd (pd.G.mval y) (((loN : ℚ) / 20 : ℚ) : ℝ) (((hiN : ℚ) / 20 : ℚ) : ℝ) y hRm hRlo hRhi
  have hFSe' : (Uu : ℝ) * fd.FSr (pd.G.mval y) (((loN : ℚ) / 20 : ℚ) : ℝ) (((hiN : ℚ) / 20 : ℚ) : ℝ) y
      = evq pd.G.N fd.cF fd.lF fd.qF y := by
    rw [← hn]; exact hFSe
  have hPS := PD.PS_evq pd y
  have hPSle := PD.PS_le pd hok y
  have hTy := hT y hy
  -- the matrix
  set x : ℕ → ℝ := fun a => if a = 1 then 1 else y (a - 2) with hx
  have hx1 : x 1 = 1 := by simp [hx]
  have hx2 : ∀ i, x (i + 2) = y i := by
    intro i
    simp [hx]
  have hg := gram_ev pd.G.N Nm x y hx1 hx2
  have hpos := hpsd x
  rw [hg] at hpos
  have hmat : (Uu : ℝ) * evq pd.G.N (Nm 1 1) (fun i => Nm 1 (i + 2) + Nm (i + 2) 1) (fun i j => Nm (i + 2) (j + 2)) y
      = evq pd.G.N (pd.cP - fd.cF - cT) (fun i => pd.lP i - fd.lF i - lT i)
          (fun i j => pd.qP i j - fd.qF i j - qT i j) y := by
    rw [evq_smul]
    apply evq_congr
    · exact h00
    · intro i hi
      have a := h0i i hi
      have b := hi0 i hi
      linarith
    · intro i hi j hj
      have a := hij i hi j hj
      have b := hij j hj i hi
      linarith
  rw [evq_sub3, ← hPS, ← hFSe'] at hmat
  have hU : (0 : ℝ) < Uu := by norm_num [Uu]
  have hD : (0 : ℝ) < Dz := by norm_num [Dz, Qn]
  have hprod : 0 ≤ (Uu : ℝ) * evq pd.G.N (Nm 1 1) (fun i => Nm 1 (i + 2) + Nm (i + 2) 1)
      (fun i j => Nm (i + 2) (j + 2)) y := mul_nonneg hU.le hpos
  have h1 : 0 ≤ (Uu : ℝ) * pd.PS y := by
    have := mul_nonneg hU.le hFS
    linarith
  have h2 : 0 ≤ pd.PS y := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hU hneg
    linarith
  have h3 : 0 ≤ (Dz : ℝ) * pd.G.Lval y := le_trans h2 hPSle
  exact (mul_nonneg_iff_of_pos_left hD).mp h3

end Erdos1186Ex
