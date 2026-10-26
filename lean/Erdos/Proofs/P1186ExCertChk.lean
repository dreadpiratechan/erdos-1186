import Mathlib
import Erdos.Proofs.P1186ExCertAlg

/-!
# Erdos 1186 - kernel-checkable layer of the `RegionLB` certificates (lane excert, night 3)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is
its author's.  Hand-written, no certificate numbers (they are in the generated modules `P1186ExCert<r>*.lean`).

`Tabs` bundles the packed integer tables of one region; `mkPD`, `mkFD` read the abstract data of
`P1186ExCertAlg.lean` out of them.  The Bool checks below are evaluated by `decide +kernel` in the generated
modules (in row chunks); their soundness lemmas turn `= true` into the hypotheses of `region_of_data`.
-/

namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

/-! ### The tables of one region -/

structure Tabs where
  n : ℕ
  loN : ℤ
  hiN : ℤ
  Zn : ℤ
  ppn : ℤ
  rrn : ℤ
  ssn : ℤ
  Wg : ℕ
  vlo : ℕ
  vhi : ℕ
  vlen : ℕ
  vsg : ℕ
  Wa : ℕ
  vAl : ℕ
  vBt : ℕ
  Wf : ℕ
  vYv : ℕ
  vOv : ℕ
  vA1 : ℕ
  vA2 : ℕ
  vA3 : ℕ
  vA4 : ℕ
  YYT : List ℕ
  OOT : List ℕ
  YOT : List ℕ
  Wt : ℕ
  thT : List ℕ
  Wn : ℕ
  NT : List ℕ
  crows : List (List ℤ)
  czr : List ℤ

/-- `A4` by corner tests (full / empty blocks) and the real count only for the remaining pairs. -/
def a4acc (G : Grid) (lo hi len : ℕ → ℤ) (i j : ℕ) : ℤ :=
  if 1 ≤ 2 * (lo j + 1) - hi i - 1 ∧ 2 * hi j - (lo i + 1) - 1 ≤ 1094 then 4 * len i * len j
  else if 2 * hi j - (lo i + 1) - 1 ≤ -2 ∨ 1097 ≤ 2 * (lo j + 1) - hi i - 1 then 0
  else (G.A4 i j : ℤ)

theorem a4acc_eq (G : Grid) (lo hi len : ℕ → ℤ) (i j : ℕ) (hi1 : lo i = G.lo i) (hi2 : hi i = G.hi i)
    (hi3 : len i = G.len i) (hj1 : lo j = G.lo j) (hj2 : hi j = G.hi j) (hj3 : len j = G.len j) :
    a4acc G lo hi len i j = (G.A4 i j : ℤ) := by
  have h := A4v_eq G i j
  unfold a4acc
  rw [hi1, hi2, hi3, hj1, hj2, hj3]
  unfold A4v at h
  split_ifs at h ⊢ with c1 c2
  · rw [← h]
    push_cast
    ring
  · rw [← h]
    simp
  · exact_mod_cast h.symm

def mkPD (T : Tabs) (G : Grid) : PD where
  G := G
  lenz := vc T.Wg T.vlen
  sgz := vc T.Wg T.vsg
  alz := vc T.Wa T.vAl
  btz := vc T.Wa T.vBt
  a4z := a4acc G (vc T.Wg T.vlo) (vc T.Wg T.vhi) (vc T.Wg T.vlen)
  th := tb T.Wt T.thT

def mkFD (T : Tabs) : FD where
  n := T.n
  Yv := fun i => T.Zn * vc T.Wf T.vYv i
  Ov := fun i => T.Zn * vc T.Wf T.vOv i
  A1 := fun i => T.Zn * vc T.Wf T.vA1 i
  A2 := fun i => T.Zn * vc T.Wf T.vA2 i
  A3 := fun i => T.Zn * vc T.Wf T.vA3 i
  A4 := fun i => T.Zn * vc T.Wf T.vA4 i
  YY := fun i j => T.Zn * tb T.Wf T.YYT i j
  OO := fun i j => T.Zn * tb T.Wf T.OOT i j
  YO := fun i j => T.Zn * tb T.Wf T.YOT i j
  pp := T.Zn * T.ppn
  rr := T.Zn * T.rrn
  ss := T.Zn * T.ssn
  om := fun i => 20 * vc T.Wg T.vlen i
  Lo := 1096 * T.loN
  Hi := 1096 * T.hiN

/-- the matrix of the certificate, indices `1 .. n+1` (index `1` is the constant). -/
def Nmat (T : Tabs) (a b : ℕ) : ℤ := tb T.Wn T.NT (a - 1) (b - 1)

/-! ### Bool checks -/

/-- grid vectors agree with the grid; `α, β` are the integers `a_i Dz`, `b_i Dz`. -/
def gridChk (T : Tabs) (G : Grid) (i : ℕ) : Bool :=
  decide (vc T.Wg T.vlo i = (G.lo i : ℤ) ∧ vc T.Wg T.vhi i = (G.hi i : ℤ) ∧ vc T.Wg T.vlen i = (G.len i : ℤ) ∧
    vc T.Wg T.vsg i = G.sgn i ∧ G.ai i * (Dz : ℚ) = ((vc T.Wa T.vAl i : ℤ) : ℚ) ∧
    G.bi i * (Dz : ℚ) = ((vc T.Wa T.vBt i : ℤ) : ℚ))

/-- the multiplier vectors are `≥ 0`. -/
def vecChk (T : Tabs) (i : ℕ) : Bool :=
  decide (0 ≤ vc T.Wf T.vYv i ∧ 0 ≤ vc T.Wf T.vOv i ∧ 0 ≤ vc T.Wf T.vA1 i ∧ 0 ≤ vc T.Wf T.vA2 i ∧
    0 ≤ vc T.Wf T.vA3 i ∧ 0 ≤ vc T.Wf T.vA4 i)

def scalChk (T : Tabs) : Bool := decide (0 ≤ T.ppn ∧ 0 ≤ T.rrn ∧ 0 ≤ T.ssn ∧ 0 < T.Zn)

/-- the extra (triangle) term of the matrix identity. -/
structure Tri where
  cT : ℤ
  lT : ℕ → ℤ
  qT : ℕ → ℕ → ℤ

def Tri.zero : Tri := ⟨0, fun _ => 0, fun _ _ => 0⟩

/-- pair entry `(i, j)`: ranges of `θ` and the form multipliers, and the identity for `2U N_{ij}`. -/
def pairChk (T : Tabs) (G : Grid) (tr : Tri) (i j : ℕ) : Bool :=
  decide ((0 ≤ tb T.Wt T.thT i j ∧ tb T.Wt T.thT i j ≤ Qn) ∧ 0 ≤ tb T.Wf T.YYT i j ∧ 0 ≤ tb T.Wf T.OOT i j ∧
    0 ≤ tb T.Wf T.YOT i j ∧
    2 * Uu * Nmat T (i + 2) (j + 2) =
      ((mkPD T G).qP i j - (mkFD T).qF i j - tr.qT i j) + ((mkPD T G).qP j i - (mkFD T).qF j i - tr.qT j i))

/-- constant and linear entries. -/
def linChk (T : Tabs) (G : Grid) (tr : Tri) (i : ℕ) : Bool :=
  decide (2 * Uu * Nmat T 1 (i + 2) = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i ∧
    2 * Uu * Nmat T (i + 2) 1 = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i)

/-- row sums of the constant coefficients `cz` (claimed in the tables, checked row by row). -/
def czRowChk (T : Tabs) (G : Grid) (i : ℕ) : Bool :=
  decide ((∑ j ∈ range G.N, (mkPD T G).cz i j) = T.czr.getD i 0)

def constChk (T : Tabs) (G : Grid) (tr : Tri) : Bool :=
  decide (Uu * Nmat T 1 1 = -Uu * (∑ i ∈ range G.N, T.czr.getD i 0) - (mkFD T).cF - tr.cT)

/-! ### Diagonal dominance of `N - C Cᵀ` -/

def absSumRow (W : ℕ) (nr : ℕ) (ri : List ℤ) : ℕ → List (List ℤ) → ℕ
  | _, [] => 0
  | j, rj :: rest => (dec W nr j - dotL ri rj).natAbs + absSumRow W nr ri (j + 1) rest

def domRow (T : Tabs) (a : ℕ) : Bool :=
  decide (((absSumRow T.Wn (T.NT.getD a 0) (T.crows.getD a []) 0 T.crows : ℕ) : ℤ)
    ≤ 2 * (dec T.Wn (T.NT.getD a 0) a - dotL (T.crows.getD a []) (T.crows.getD a [])))

def lenChk (T : Tabs) : Bool :=
  decide (T.crows.length = T.n + 1) && T.crows.all (fun r => decide (r.length ≤ T.n + 1))

theorem absSumRow_eq (W nr : ℕ) (ri : List ℤ) :
    ∀ (rows : List (List ℤ)) (j0 : ℕ),
      ((absSumRow W nr ri j0 rows : ℕ) : ℤ) =
        ∑ t ∈ range rows.length, |dec W nr (j0 + t) - dotL ri (rows.getD t [])|
  | [], j0 => by simp [absSumRow]
  | rj :: rest, j0 => by
      have ih := absSumRow_eq W nr ri rest (j0 + 1)
      have hsum : ∑ t ∈ range rest.length, |dec W nr (j0 + 1 + t) - dotL ri (rest.getD t [])| =
          ∑ t ∈ range rest.length, |dec W nr (j0 + (t + 1)) - dotL ri (rest.getD t [])| := by
        apply Finset.sum_congr rfl
        intro t _
        rw [show j0 + 1 + t = j0 + (t + 1) by omega]
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [absSumRow, List.getD_cons_succ, List.getD_cons_zero, add_zero]
      push_cast
      rw [ih, hsum, add_comm]

theorem domRow_sound (T : Tabs) (hrows : T.crows.length = T.n + 1) (a : ℕ) (h : domRow T a = true) :
    ∑ b ∈ Icc 1 (T.n + 1), |Nmat T (a + 1) b - dotL (T.crows.getD a []) (T.crows.getD (b - 1) [])|
      ≤ 2 * (Nmat T (a + 1) (a + 1) - dotL (T.crows.getD a []) (T.crows.getD a [])) := by
  unfold domRow at h
  have h' := of_decide_eq_true h
  rw [absSumRow_eq, hrows] at h'
  have e : ∑ b ∈ Icc 1 (T.n + 1), |Nmat T (a + 1) b - dotL (T.crows.getD a []) (T.crows.getD (b - 1) [])|
      = ∑ t ∈ range (T.n + 1), |dec T.Wn (T.NT.getD a 0) (0 + t) - dotL (T.crows.getD a []) (T.crows.getD t [])| := by
    rw [sum_Icc_one]
    apply Finset.sum_congr rfl
    intro t _
    unfold Nmat tb
    simp
  rw [e]
  unfold Nmat tb
  simpa using h'

/-! ### Positive semidefiniteness from the dominance rows -/

theorem psd_of_rows (L : ℕ) (Nm : ℕ → ℕ → ℤ) (crow : ℕ → List ℤ)
    (hlen : ∀ i ∈ Icc 1 L, (crow i).length ≤ L)
    (hsym : ∀ i ∈ Icc 1 L, ∀ j ∈ Icc 1 L, Nm i j = Nm j i)
    (hdom : ∀ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |Nm i j - dotL (crow i) (crow j)|
      ≤ 2 * (Nm i i - dotL (crow i) (crow i))) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (Nm i j : ℝ) * x i * x j := by
  set c : ℕ → ℕ → ℝ := fun i k => (((crow i).getD k 0 : ℤ) : ℝ) with hc
  set Er : ℕ → ℕ → ℝ := fun i j =>
    if i ∈ Icc 1 L ∧ j ∈ Icc 1 L then ((Nm i j - dotL (crow i) (crow j) : ℤ) : ℝ) else 0 with hEr
  have hG := gram_nonneg L L c x
  have hEs : ∀ i j, Er i j = Er j i := by
    intro i j
    simp only [hEr]
    by_cases h : i ∈ Icc 1 L ∧ j ∈ Icc 1 L
    · have h' : j ∈ Icc 1 L ∧ i ∈ Icc 1 L := ⟨h.2, h.1⟩
      rw [if_pos h, if_pos h', hsym i h.1 j h.2, dotL_comm (crow i) (crow j)]
    · have h' : ¬ (j ∈ Icc 1 L ∧ i ∈ Icc 1 L) := fun hh => h ⟨hh.2, hh.1⟩
      rw [if_neg h, if_neg h']
  have hE := psd_of_dom L Er hEs
    (fun i hi => by
      have hd := hdom i hi
      have e : ∀ j ∈ Icc 1 L, |Er i j| = |((Nm i j - dotL (crow i) (crow j) : ℤ) : ℝ)| := by
        intro j hj
        simp only [hEr]
        rw [if_pos ⟨hi, hj⟩]
      have e2 : Er i i = ((Nm i i - dotL (crow i) (crow i) : ℤ) : ℝ) := by
        simp only [hEr]
        rw [if_pos ⟨hi, hi⟩]
      rw [Finset.sum_congr rfl e, e2]
      have hcast : (∑ j ∈ Icc 1 L, |((Nm i j - dotL (crow i) (crow j) : ℤ) : ℝ)|)
          = ((∑ j ∈ Icc 1 L, |Nm i j - dotL (crow i) (crow j)| : ℤ) : ℝ) := by
        push_cast
        rfl
      rw [hcast]
      exact_mod_cast hd) x
  have hsum : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (Nm i j : ℝ) * x i * x j =
      (∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (∑ k ∈ range L, c i k * c j k) * x i * x j)
      + ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, Er i j * x i * x j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hd : dotL (crow i) (crow j) = ∑ k ∈ range L, (crow i).getD k 0 * (crow j).getD k 0 :=
      dotL_eq_sum _ _ _ (hlen i hi)
    have e : (Nm i j : ℝ) = (∑ k ∈ range L, c i k * c j k) + Er i j := by
      simp only [hEr, hc]
      rw [if_pos ⟨hi, hj⟩]
      have : (Nm i j : ℤ) = (∑ k ∈ range L, (crow i).getD k 0 * (crow j).getD k 0) + (Nm i j - dotL (crow i) (crow j)) := by
        rw [← hd]; ring
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) this
      simp only [Int.cast_add, Int.cast_sum, Int.cast_mul] at h2
      exact h2
    rw [e]
    ring
  rw [hsum]
  exact add_nonneg hG hE

/-! ### From the Bool checks to `RegionLB` -/

theorem gridChk_spec (T : Tabs) (G : Grid) (i : ℕ) (h : gridChk T G i = true) :
    vc T.Wg T.vlo i = (G.lo i : ℤ) ∧ vc T.Wg T.vhi i = (G.hi i : ℤ) ∧ vc T.Wg T.vlen i = (G.len i : ℤ) ∧
    vc T.Wg T.vsg i = G.sgn i ∧ G.ai i * (Dz : ℚ) = ((vc T.Wa T.vAl i : ℤ) : ℚ) ∧
    G.bi i * (Dz : ℚ) = ((vc T.Wa T.vBt i : ℤ) : ℚ) := of_decide_eq_true h

theorem vecChk_spec (T : Tabs) (i : ℕ) (h : vecChk T i = true) :
    0 ≤ vc T.Wf T.vYv i ∧ 0 ≤ vc T.Wf T.vOv i ∧ 0 ≤ vc T.Wf T.vA1 i ∧ 0 ≤ vc T.Wf T.vA2 i ∧
    0 ≤ vc T.Wf T.vA3 i ∧ 0 ≤ vc T.Wf T.vA4 i := of_decide_eq_true h

theorem scalChk_spec (T : Tabs) (h : scalChk T = true) : 0 ≤ T.ppn ∧ 0 ≤ T.rrn ∧ 0 ≤ T.ssn ∧ 0 < T.Zn :=
  of_decide_eq_true h

theorem pairChk_spec (T : Tabs) (G : Grid) (tr : Tri) (i j : ℕ) (h : pairChk T G tr i j = true) :
    (0 ≤ tb T.Wt T.thT i j ∧ tb T.Wt T.thT i j ≤ Qn) ∧ 0 ≤ tb T.Wf T.YYT i j ∧ 0 ≤ tb T.Wf T.OOT i j ∧
    0 ≤ tb T.Wf T.YOT i j ∧
    2 * Uu * Nmat T (i + 2) (j + 2) =
      ((mkPD T G).qP i j - (mkFD T).qF i j - tr.qT i j) + ((mkPD T G).qP j i - (mkFD T).qF j i - tr.qT j i) :=
  of_decide_eq_true h

theorem linChk_spec (T : Tabs) (G : Grid) (tr : Tri) (i : ℕ) (h : linChk T G tr i = true) :
    2 * Uu * Nmat T 1 (i + 2) = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i ∧
    2 * Uu * Nmat T (i + 2) 1 = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i := of_decide_eq_true h

theorem cP_eq (T : Tabs) (G : Grid) (hcz : ∀ i < G.N, czRowChk T G i = true) :
    (mkPD T G).cP = -Uu * ∑ i ∈ range G.N, T.czr.getD i 0 := by
  unfold PD.cP
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact of_decide_eq_true (hcz i (Finset.mem_range.mp hi))

theorem constChk_spec (T : Tabs) (G : Grid) (tr : Tri) (hcz : ∀ i < G.N, czRowChk T G i = true)
    (h : constChk T G tr = true) :
    Uu * Nmat T 1 1 = (mkPD T G).cP - (mkFD T).cF - tr.cT := by
  rw [cP_eq T G hcz]
  exact of_decide_eq_true h

theorem two_Uu_ne : (2 * Uu : ℤ) ≠ 0 := by unfold Uu; norm_num

theorem Nsym (T : Tabs) (G : Grid) (tr : Tri)
    (hlin : ∀ i < G.N, linChk T G tr i = true)
    (hpair : ∀ i < G.N, ∀ j < G.N, pairChk T G tr i j = true) :
    ∀ a ∈ Icc 1 (G.N + 1), ∀ b ∈ Icc 1 (G.N + 1), Nmat T a b = Nmat T b a := by
  intro a ha b hb
  rw [Finset.mem_Icc] at ha hb
  by_cases h1 : a = 1
  · subst h1
    by_cases h2 : b = 1
    · subst h2; rfl
    · obtain ⟨j, rfl⟩ : ∃ j, b = j + 2 := ⟨b - 2, by omega⟩
      have hl := linChk_spec T G tr j (hlin j (by omega))
      exact mul_left_cancel₀ two_Uu_ne (hl.1.trans hl.2.symm)
  · obtain ⟨i, rfl⟩ : ∃ i, a = i + 2 := ⟨a - 2, by omega⟩
    by_cases h2 : b = 1
    · subst h2
      have hl := linChk_spec T G tr i (hlin i (by omega))
      exact mul_left_cancel₀ two_Uu_ne (hl.2.trans hl.1.symm)
    · obtain ⟨j, rfl⟩ : ∃ j, b = j + 2 := ⟨b - 2, by omega⟩
      have e1 := (pairChk_spec T G tr i j (hpair i (by omega) j (by omega))).2.2.2.2
      have e2 := (pairChk_spec T G tr j i (hpair j (by omega) i (by omega))).2.2.2.2
      refine mul_left_cancel₀ two_Uu_ne ?_
      rw [e1, e2]
      ring

theorem lenChk_spec (T : Tabs) (h : lenChk T = true) :
    T.crows.length = T.n + 1 ∧ ∀ r ∈ T.crows, r.length ≤ T.n + 1 := by
  unfold lenChk at h
  rw [Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1, ?_⟩
  intro r hr
  have := List.all_eq_true.mp h.2 r hr
  exact of_decide_eq_true this

theorem region_of_tabs_aux (T : Tabs) (G : Grid) (tr : Tri) (hn : T.n = G.N)
    (hgrid : ∀ i < G.N, gridChk T G i = true)
    (hvec : ∀ i < G.N, vecChk T i = true)
    (hscal : scalChk T = true)
    (hpair : ∀ i < G.N, ∀ j < G.N, pairChk T G tr i j = true)
    (hlin : ∀ i < G.N, linChk T G tr i = true)
    (hcz : ∀ i < G.N, czRowChk T G i = true)
    (hconst : constChk T G tr = true)
    (hlen : lenChk T = true)
    (hdom : ∀ a < G.N + 1, domRow T a = true)
    (hT : ∀ y : ℕ → ℝ, (∀ i < T.n, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq T.n tr.cT tr.lT tr.qT y) :
    RegionLB G ((T.loN : ℚ) / 20) ((T.hiN : ℚ) / 20) := by
  have hT' : ∀ y : ℕ → ℝ, (∀ i < G.N, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq G.N tr.cT tr.lT tr.qT y := by
    intro y hy
    rw [← hn]
    rw [← hn] at hy
    exact hT y hy
  obtain ⟨hppn, hrrn, hssn, hZn⟩ := scalChk_spec T hscal
  have hok : (mkPD T G).Ok := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.1
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.2.1
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.2.2.1
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.2.2.2
    · intro i hi j hj
      have a := gridChk_spec T G i (hgrid i hi)
      have b := gridChk_spec T G j (hgrid j hj)
      exact a4acc_eq G _ _ _ i j a.1 a.2.1 a.2.2.1 b.1 b.2.1 b.2.2.1
    · intro i hi j hj
      exact (pairChk_spec T G tr i j (hpair i hi j hj)).1
  have hfn : (mkFD T).Nonneg := by
    have hz : ∀ x : ℤ, 0 ≤ x → 0 ≤ T.Zn * x := fun x hx => mul_nonneg hZn.le hx
    have hn' : (mkFD T).n = G.N := hn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.2.2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.2.2.2
    · intro i hi j hj
      exact hz _ (pairChk_spec T G tr i j (hpair i (hn' ▸ hi) j (hn' ▸ hj))).2.1
    · intro i hi j hj
      exact hz _ (pairChk_spec T G tr i j (hpair i (hn' ▸ hi) j (hn' ▸ hj))).2.2.1
    · intro i hi j hj
      exact hz _ (pairChk_spec T G tr i j (hpair i (hn' ▸ hi) j (hn' ▸ hj))).2.2.2.1
    · exact hz _ hppn
    · exact hz _ hrrn
    · exact hz _ hssn
  obtain ⟨hcl, hrl⟩ := lenChk_spec T hlen
  have hpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ a ∈ Icc 1 (G.N + 1), ∑ b ∈ Icc 1 (G.N + 1), (Nmat T a b : ℝ) * x a * x b := by
    intro x
    refine psd_of_rows (G.N + 1) (Nmat T) (fun i => T.crows.getD (i - 1) []) ?_ (Nsym T G tr hlin hpair) ?_ x
    · intro i hi
      rw [Finset.mem_Icc] at hi
      have hlt : i - 1 < T.crows.length := by omega
      have hmem : T.crows.getD (i - 1) [] ∈ T.crows := by
        rw [List.getD_eq_getElem _ _ hlt]
        exact List.getElem_mem hlt
      show (T.crows.getD (i - 1) []).length ≤ G.N + 1
      rw [← hn]
      exact hrl _ hmem
    · intro i hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
      have h := domRow_sound T (by omega) a (hdom a (by omega))
      simp only [Nat.add_sub_cancel]
      rw [hn] at h
      exact h
  exact region_of_data (mkPD T G) (mkFD T) T.loN T.hiN hok hfn hn (fun _ _ => rfl) rfl rfl tr.cT tr.lT tr.qT hT'
    (Nmat T) hpsd (constChk_spec T G tr hcz hconst)
    (fun i hi => (linChk_spec T G tr i (hlin i hi)).1)
    (fun i hi => (linChk_spec T G tr i (hlin i hi)).2)
    (fun i hi j hj => (pairChk_spec T G tr i j (hpair i hi j hj)).2.2.2.2)

/-- The same, with the cell count given as a literal `m` so that the hypotheses never unfold `G.N`. -/
theorem region_of_tabs (T : Tabs) (G : Grid) (tr : Tri) (m : ℕ) (hm : G.N = m) (hn : T.n = m)
    (hgrid : ∀ i < m, gridChk T G i = true)
    (hvec : ∀ i < m, vecChk T i = true)
    (hscal : scalChk T = true)
    (hpair : ∀ i < m, ∀ j < m, pairChk T G tr i j = true)
    (hlin : ∀ i < m, linChk T G tr i = true)
    (hcz : ∀ i < m, czRowChk T G i = true)
    (hconst : constChk T G tr = true)
    (hlen : lenChk T = true)
    (hdom : ∀ a < m + 1, domRow T a = true)
    (hT : ∀ y : ℕ → ℝ, (∀ i < T.n, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq T.n tr.cT tr.lT tr.qT y) :
    RegionLB G ((T.loN : ℚ) / 20) ((T.hiN : ℚ) / 20) := by
  subst hm
  exact region_of_tabs_aux T G tr hn hgrid hvec hscal hpair hlin hcz hconst hlen hdom hT

/-! ### Chunked `∀ i < n` from `List.all` over `range'` -/

theorem all_range_of {f : ℕ → Bool} {a k : ℕ} (h : (List.range' a k).all f = true) :
    ∀ i, a ≤ i → i < a + k → f i = true := by
  intro i h1 h2
  have := List.all_eq_true.mp h i (by rw [List.mem_range']; exact ⟨i - a, by omega, by omega⟩)
  exact this

theorem all_range0_of {f : ℕ → Bool} {n : ℕ} (h : (List.range n).all f = true) : ∀ i, i < n → f i = true := by
  intro i hi
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem all_range_of2 {f : ℕ → ℕ → Bool} {a k n : ℕ}
    (h : (List.range' a k).all (fun i => (List.range n).all (fun j => f i j)) = true) :
    ∀ i, a ≤ i → i < a + k → ∀ j, j < n → f i j = true := by
  intro i h1 h2 j hj
  have h3 := all_range_of h i h1 h2
  exact all_range0_of h3 j hj

theorem all_range_of2c {f : ℕ → ℕ → Bool} {g : ℕ → Bool} {a k n : ℕ}
    (h : (List.range' a k).all (fun i => (List.range n).all (fun j => f i j) && g i) = true) :
    ∀ i, a ≤ i → i < a + k → (∀ j, j < n → f i j = true) ∧ g i = true := by
  intro i h1 h2
  have h3 := all_range_of h i h1 h2
  rw [Bool.and_eq_true] at h3
  exact ⟨fun j hj => all_range0_of h3.1 j hj, h3.2⟩

theorem Tri.zero_ok (n : ℕ) :
    ∀ y : ℕ → ℝ, (∀ i < n, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq n Tri.zero.cT Tri.zero.lT Tri.zero.qT y := by
  intro y _
  exact le_of_eq (FD.evq_zero n y).symm

end Erdos1186Ex
