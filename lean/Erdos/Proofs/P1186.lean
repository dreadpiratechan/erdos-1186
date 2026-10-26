import Mathlib
import Erdos.Proofs.P1186Tab

/-! # Erdos 1186 - three `research solved` statements of upstream `variants`, proved in Lean

For the minimum number `minMonoCount k n` of monochromatic `k`-term progressions in a 2-colouring of `[1, n]` and
`δ k = liminf minMonoCount k n / n^2` (definitions copied VERBATIM from upstream formal-conjectures c83a94d,
`FormalConjectures/ErdosProblems/1186.lean`; only the namespace differs), this module proves, with the upstream
statements:

* `erdos_1186.variants.prs_bounds_upper : δ 3 ≤ 117 / 2192` (the upper half of upstream `prs_bounds`);
* `erdos_1186.variants.probabilistic : δ k ≤ 1 / ((k - 1) * 2 ^ k)` for `k ≥ 2`;
* `erdos_1186.variants.van_der_waerden : 0 < δ k` for `k ≥ 2`.

Not proved here: the lower half `1675 / 32768 ≤ δ 3` of `prs_bounds` (an SDP certificate) and the open `erdos_1186`,
`prs_conjecture`.

**Proof of the PRS upper bound.**  The colouring of `[1, 548 K]` is the pull-back along `x ↦ ⌈x / K⌉` of the 12-block
colouring `c1` of `[1, 548]` (blocks 28, 6, 28, 37, 59, 116, 116, 59, 37, 28, 6, 28).  Writing `a = K A + r`,
`d = K D + s` with `r, s ∈ [1, K]`, a progression `(a, d)` of 3 terms is monochromatic iff the coarse triple
`(A + 1, A + D + u + 1, A + 2 D + v + 1)` is, where the carries `u ∈ {0, 1}`, `v ∈ {0, 1, 2}` are functions of `(r, s)`
only (`u3`, `v3`).  So `monoCount ≤ ∑_{(r, s)} M_{u v}` where `M_{uv}` counts the monochromatic coarse triples; the four
values that occur (16304, 16028, 16028, 15756) are computed by `decide +kernel` in `Erdos.Proofs.P1186Tab`.  Since
`M_{00}` is only slightly larger than `16028` and occurs only for `r + 2 s ≤ K` (at most `K^2 / 4` pairs) while
`M_{12}` is smaller and occurs for `2 K < r + 2 s` (at least as many pairs), `monoCount ≤ 16029 K^2`
(`monoCount_ck_le`), and `16029 / 548^2 = 117 / 2192`.  Hence `minMonoCount 3 (548 K) / (548 K)^2 ≤ 117 / 2192` along
`n = 548 K`, which suffices for the `liminf`.  (The exact count is `16029 K^2 - 274 K + (K mod 2)`, checked by computer
for `K ≤ 10`; only the inequality is needed.)

**Proof of the probabilistic bound.**  Average `monoCount` over the `2^n` colourings `colOf s` of the subsets
`s ⊆ [1, n]`: each progression is monochromatic for at most `2 * 2^(n-k)` of them, and there are at most `n^2 / (2 (k-1))`
progressions (`card_aps_le`), so the minimum is at most `n^2 / ((k - 1) 2^k)`.

**Proof of positivity.**  The finite Hales-Jewett theorem of Mathlib (`Combinatorics.Line.exists_mono_in_high_dimension`)
gives a finite van der Waerden number `W` for `k`-term progressions in 2 colours (`vdw_finite`).  In `[1, n]` every
colouring then has, for each of the at least `(n/2)(n/(2W))` progressions `w` of length `W`, a monochromatic `k`-term
progression inside `w` (`window_has_ap`), and each `k`-term progression lies in at most `W^2` windows (`card_rel_le`):
`n^2 ≤ 12 W^3 * monoCount` for `n ≥ 4W` (`sq_le_monoCount`), so `δ k ≥ 1 / (12 W^3) > 0`.

All three results use only `propext`, `Classical.choice`, `Quot.sound` (see the `#print axioms` lines at the end). -/

open Filter Asymptotics

namespace Erdos1186Day

/--
`monoCount k n c` is the number of monochromatic $k$-term arithmetic progressions in
$\{1,\ldots,n\}$ under the $2$-colouring `c`. The progression $a, a+d, \ldots, a+(k-1)d$ with first
term $a$ and common difference $d \geq 1$ is the pair `(a, d)`, with $a \geq 1$ and
$a + (k-1)d \leq n$. Each progression is counted once.

This is the count of [Er80, p. 93]: there are $\sim n^2/(2(k-1))$ progressions, and the upper bound
in (7) there is their number times the probability $2^{1-k}$ that a random colouring makes one of
them monochromatic. The definition is meant for $k \geq 2$.
-/
def monoCount (k n : ℕ) (c : ℕ → Bool) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p : ℕ × ℕ =>
    p.1 + (k - 1) * p.2 ≤ n ∧ ∀ i < k, c (p.1 + i * p.2) = c p.1).card

/--
`minMonoCount k n` is the least number of monochromatic $k$-term arithmetic progressions in a
$2$-colouring of $\{1,\ldots,n\}$. This is $A(n;k)$ in [Er80, p. 93]. The set of values contains
`monoCount k n (fun _ => true)`, so `sInf` is a true minimum.
-/
noncomputable def minMonoCount (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ c : ℕ → Bool, monoCount k n c = m}

/--
`δ k` is the largest constant $\delta_k$ such that every $2$-colouring of $\{1,\ldots,n\}$ has at
least $(\delta_k - o(1))n^2$ monochromatic $k$-term arithmetic progressions, that is,
$\liminf_{n\to\infty} A(n;k)/n^2$.

The quotient `minMonoCount k n / n ^ 2` lies in $[0,1]$, so this `liminf` is not a junk value.
Convergence of the quotient is not assumed. If it converges, `δ k` is its limit.
-/
noncomputable def δ (k : ℕ) : ℝ :=
  atTop.liminf (fun n : ℕ ↦ (minMonoCount k n : ℝ) / (n : ℝ) ^ 2)

theorem minMonoCount_le (k n : ℕ) (c : ℕ → Bool) : minMonoCount k n ≤ monoCount k n c :=
  Nat.sInf_le ⟨c, rfl⟩

theorem le_minMonoCount (k n B : ℕ) (h : ∀ c : ℕ → Bool, B ≤ monoCount k n c) :
    B ≤ minMonoCount k n := by
  unfold minMonoCount
  have hne : ({m : ℕ | ∃ c : ℕ → Bool, monoCount k n c = m}).Nonempty := ⟨_, fun _ => true, rfl⟩
  apply le_csInf hne
  rintro m ⟨c, rfl⟩
  exact h c

open Finset

theorem monoCount_le_sq (k n : ℕ) (c : ℕ → Bool) : monoCount k n c ≤ n ^ 2 := by
  unfold monoCount
  calc _ ≤ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).card := Finset.card_filter_le _ _
    _ = n ^ 2 := by simp [sq]

theorem quot_nonneg (k n : ℕ) : 0 ≤ (minMonoCount k n : ℝ) / (n : ℝ) ^ 2 := by positivity

theorem quot_le_one (k n : ℕ) : (minMonoCount k n : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by positivity)]
    have h1 : minMonoCount k n ≤ n ^ 2 :=
      (minMonoCount_le k n (fun _ => true)).trans (monoCount_le_sq k n _)
    exact_mod_cast h1

theorem bddBelow_quot (k : ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ ↦ (minMonoCount k n : ℝ) / (n : ℝ) ^ 2) :=
  isBoundedUnder_of ⟨0, fun n => quot_nonneg k n⟩

theorem cobdd_quot (k : ℕ) :
    IsCoboundedUnder (· ≥ ·) atTop (fun n : ℕ ↦ (minMonoCount k n : ℝ) / (n : ℝ) ^ 2) :=
  isCoboundedUnder_ge_of_le atTop (fun n => quot_le_one k n)

/-- To bound `δ k` above, it suffices to exhibit, for each `ε > 0`, infinitely many `n`
with quotient at most `b + ε`. -/
theorem delta_le_of_frequently (k : ℕ) (b : ℝ)
    (h : ∀ ε > 0, ∃ᶠ n in atTop, (minMonoCount k n : ℝ) / (n : ℝ) ^ 2 ≤ b + ε) : δ k ≤ b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact liminf_le_of_frequently_le (h ε hε) (bddBelow_quot k)

theorem le_delta_of_eventually (k : ℕ) (b : ℝ)
    (h : ∀ᶠ n in atTop, b ≤ (minMonoCount k n : ℝ) / (n : ℝ) ^ 2) : b ≤ δ k :=
  le_liminf_of_le (cobdd_quot k) h

/-! ## The probabilistic bound -/

/-- The pairs `(a, d)` indexing the `k`-term progressions of `[1, n]`. -/
def aps (k n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p : ℕ × ℕ => p.1 + (k - 1) * p.2 ≤ n

theorem monoCount_eq (k n : ℕ) (c : ℕ → Bool) :
    monoCount k n c = ((aps k n).filter fun p : ℕ × ℕ => ∀ i < k, c (p.1 + i * p.2) = c p.1).card := by
  unfold monoCount aps
  rw [Finset.filter_filter]

theorem monoCount_le_aps (k n : ℕ) (c : ℕ → Bool) : monoCount k n c ≤ (aps k n).card := by
  rw [monoCount_eq]; exact Finset.card_filter_le _ _

/-- fibre of the "last term" map -/
theorem card_fibre_le (m n t : ℕ) (hm : 1 ≤ m) :
    (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p : ℕ × ℕ => p.1 + m * p.2 ≤ n).filter
        (fun p : ℕ × ℕ => p.1 + m * p.2 = t)).card ≤ (t - 1) / m := by
  have : (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p : ℕ × ℕ => p.1 + m * p.2 ≤ n).filter
        (fun p : ℕ × ℕ => p.1 + m * p.2 = t)).card ≤ (Finset.Icc 1 ((t - 1) / m)).card := by
    apply Finset.card_le_card_of_injOn (fun p => p.2)
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc]
      obtain ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩, h6⟩ := hp
      refine ⟨h3, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      have := Nat.mul_comm m p.2
      omega
    · intro p hp q hq hpq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp hq
      have : p.2 = q.2 := hpq
      ext
      · have : p.1 + m * p.2 = q.1 + m * q.2 := by omega
        rw [‹p.2 = q.2›] at this
        omega
      · exact hpq
  simpa using this

theorem sum_pred_le (n : ℕ) : 2 * ∑ t ∈ Finset.Icc 1 n, (t - 1) ≤ n ^ 2 := by
  induction n with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    nlinarith

theorem card_aps_le (k n : ℕ) (hk : 2 ≤ k) : 2 * (k - 1) * (aps k n).card ≤ n ^ 2 := by
  have hm : 1 ≤ k - 1 := by omega
  set m := k - 1 with hmdef
  have hfib := Finset.card_eq_sum_card_fiberwise (s := aps k n) (t := Finset.Icc 1 n)
    (f := fun p : ℕ × ℕ => p.1 + m * p.2) (by
      intro p hp
      simp only [Finset.mem_coe, aps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      constructor <;> nlinarith [hp.1.1.1, hp.1.2.1])
  have hle : (aps k n).card ≤ ∑ t ∈ Finset.Icc 1 n, (t - 1) / m := by
    rw [hfib]
    apply Finset.sum_le_sum
    intro t _
    exact card_fibre_le m n t hm
  have h2 : ∀ t, m * ((t - 1) / m) ≤ t - 1 := fun t => Nat.mul_div_le _ _
  have h3 : m * ∑ t ∈ Finset.Icc 1 n, (t - 1) / m ≤ ∑ t ∈ Finset.Icc 1 n, (t - 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun t _ => h2 t)
  have h4 := sum_pred_le n
  calc 2 * m * (aps k n).card ≤ 2 * m * ∑ t ∈ Finset.Icc 1 n, (t - 1) / m := by
        exact Nat.mul_le_mul_left _ hle
    _ = 2 * (m * ∑ t ∈ Finset.Icc 1 n, (t - 1) / m) := by ring
    _ ≤ 2 * ∑ t ∈ Finset.Icc 1 n, (t - 1) := Nat.mul_le_mul_left _ h3
    _ ≤ n ^ 2 := h4

/-! ## The probabilistic bound -/

/-- The colouring of `ℕ` attached to a finite set. -/
def colOf (s : Finset ℕ) : ℕ → Bool := fun x => decide (x ∈ s)

theorem card_mono_sets_le (k n : ℕ) (hk : 1 ≤ k) (p : ℕ × ℕ) (hp : p ∈ aps k n) :
    (((Finset.Icc 1 n).powerset).filter
        (fun s => ∀ i < k, colOf s (p.1 + i * p.2) = colOf s p.1)).card ≤ 2 * 2 ^ (n - k) := by
  classical
  simp only [aps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨h1, _⟩, h3, _⟩, h5⟩ := hp
  set U := Finset.Icc 1 n with hU
  set P : Finset ℕ := (Finset.range k).image (fun i => p.1 + i * p.2) with hPdef
  have hPU : P ⊆ U := by
    intro x hx
    simp only [hPdef, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [hU, Finset.mem_Icc]
    have : i * p.2 ≤ (k - 1) * p.2 := Nat.mul_le_mul_right _ (by omega)
    constructor <;> omega
  have hPcard : P.card = k := by
    rw [hPdef, Finset.card_image_of_injOn, Finset.card_range]
    intro i _ j _ hij
    have : i * p.2 = j * p.2 := by simpa using hij
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  have hp1 : p.1 ∈ P := by
    simp only [hPdef, Finset.mem_image, Finset.mem_range]
    exact ⟨0, by omega, by simp⟩
  have hUP : (U \ P).card = n - k := by
    rw [Finset.card_sdiff_of_subset hPU, hPcard]
    simp [hU]
  have hsub : ((Finset.Icc 1 n).powerset.filter
        (fun s => ∀ i < k, colOf s (p.1 + i * p.2) = colOf s p.1)) ⊆
      (U.powerset.filter (fun s => P ⊆ s)) ∪ (U.powerset.filter (fun s => Disjoint P s)) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_powerset] at hs
    obtain ⟨hsU, hs⟩ := hs
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_powerset]
    by_cases ha : p.1 ∈ s
    · left
      refine ⟨hsU, fun x hx => ?_⟩
      simp only [hPdef, Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have := hs i hi
      simp only [colOf, ha, decide_true, decide_eq_true_eq] at this
      exact this
    · right
      refine ⟨hsU, Finset.disjoint_left.mpr fun x hx hxs => ?_⟩
      simp only [hPdef, Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have := hs i hi
      simp only [colOf, ha, decide_false, decide_eq_false_iff_not] at this
      simp only [colOf, hxs, decide_true] at this
      simp [ha] at this
  have hA : (U.powerset.filter (fun s => P ⊆ s)).card ≤ 2 ^ (n - k) := by
    calc _ ≤ (U \ P).powerset.card := by
          apply Finset.card_le_card_of_injOn (fun s => s \ P)
          · intro s hs
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hs ⊢
            exact Finset.sdiff_subset_sdiff hs.1 (Finset.Subset.refl P)
          · intro s hs t ht hst
            simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hs ht
            have : s \ P = t \ P := hst
            rw [← Finset.sdiff_union_of_subset hs.2, ← Finset.sdiff_union_of_subset ht.2, this]
      _ = 2 ^ (n - k) := by rw [Finset.card_powerset, hUP]
  have hB : (U.powerset.filter (fun s => Disjoint P s)).card ≤ 2 ^ (n - k) := by
    calc _ ≤ (U \ P).powerset.card := by
          apply Finset.card_le_card
          intro s hs
          simp only [Finset.mem_filter, Finset.mem_powerset] at hs ⊢
          intro x hx
          rw [Finset.mem_sdiff]
          exact ⟨hs.1 hx, fun hxP => Finset.disjoint_left.mp hs.2 hxP hx⟩
      _ = 2 ^ (n - k) := by rw [Finset.card_powerset, hUP]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 ^ (n - k) + 2 ^ (n - k) := Nat.add_le_add hA hB
    _ = 2 * 2 ^ (n - k) := by ring

theorem minMonoCount_mul_le (k n : ℕ) (hk : 2 ≤ k) :
    minMonoCount k n * 2 ^ (k - 1) ≤ (aps k n).card := by
  classical
  by_cases hkn : k ≤ n
  swap
  · have : (aps k n).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro p hp
      simp only [aps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨h1, _⟩, h3, _⟩, h5⟩ := hp
      have : (k - 1) * 1 ≤ (k - 1) * p.2 := Nat.mul_le_mul_left _ h3
      omega
    have h0 : minMonoCount k n = 0 := by
      have := (minMonoCount_le k n (fun _ => true)).trans (monoCount_le_aps k n _)
      omega
    simp [h0]
  have hsum : ∑ s ∈ (Finset.Icc 1 n).powerset, monoCount k n (colOf s) ≤
      (aps k n).card * (2 * 2 ^ (n - k)) := by
    have : ∀ s : Finset ℕ, monoCount k n (colOf s) =
        ∑ p ∈ aps k n, if (∀ i < k, colOf s (p.1 + i * p.2) = colOf s p.1) then 1 else 0 := by
      intro s
      rw [monoCount_eq, Finset.card_filter]
    simp_rw [this]
    rw [Finset.sum_comm]
    calc _ = ∑ p ∈ aps k n, ((Finset.Icc 1 n).powerset.filter
          (fun s => ∀ i < k, colOf s (p.1 + i * p.2) = colOf s p.1)).card := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.card_filter]
      _ ≤ ∑ p ∈ aps k n, 2 * 2 ^ (n - k) :=
          Finset.sum_le_sum (fun p hp => card_mono_sets_le k n (by omega) p hp)
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  have hlow : 2 ^ n * minMonoCount k n ≤ ∑ s ∈ (Finset.Icc 1 n).powerset, monoCount k n (colOf s) := by
    calc 2 ^ n * minMonoCount k n = ∑ s ∈ (Finset.Icc 1 n).powerset, minMonoCount k n := by
          rw [Finset.sum_const, Finset.card_powerset, Nat.card_Icc, smul_eq_mul]
          simp
      _ ≤ _ := Finset.sum_le_sum (fun s _ => minMonoCount_le k n _)
  have hpow : 2 ^ n = 2 ^ (n - k) * 2 * 2 ^ (k - 1) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  have h2 := hlow.trans hsum
  rw [hpow] at h2
  have hpos : 0 < 2 * 2 ^ (n - k) := by positivity
  have : minMonoCount k n * 2 ^ (k - 1) * (2 * 2 ^ (n - k)) ≤ (aps k n).card * (2 * 2 ^ (n - k)) := by
    calc _ = 2 ^ (n - k) * 2 * 2 ^ (k - 1) * minMonoCount k n := by ring
      _ ≤ _ := h2
  exact Nat.le_of_mul_le_mul_right this hpos

/-- `minMonoCount k n * ((k-1) * 2^k) ≤ n^2`. -/
theorem minMonoCount_bound (k n : ℕ) (hk : 2 ≤ k) :
    minMonoCount k n * ((k - 1) * 2 ^ k) ≤ n ^ 2 := by
  have h1 := minMonoCount_mul_le k n hk
  have h2 := card_aps_le k n hk
  have hk2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  calc minMonoCount k n * ((k - 1) * 2 ^ k)
      = (minMonoCount k n * 2 ^ (k - 1)) * (2 * (k - 1)) := by rw [hk2]; ring
    _ ≤ (aps k n).card * (2 * (k - 1)) := Nat.mul_le_mul_right _ h1
    _ = 2 * (k - 1) * (aps k n).card := by ring
    _ ≤ n ^ 2 := h2

theorem probabilistic_aux (k : ℕ) (hk : 2 ≤ k) : δ k ≤ 1 / (((k : ℝ) - 1) * 2 ^ k) := by
  apply delta_le_of_frequently
  intro ε hε
  apply Filter.Eventually.frequently
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < ((k : ℝ) - 1) * 2 ^ k := by
    apply mul_pos <;> [linarith; positivity]
  have hb := minMonoCount_bound k n hk
  have hb' : (minMonoCount k n : ℝ) * (((k : ℝ) - 1) * 2 ^ k) ≤ (n : ℝ) ^ 2 := by
    have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have h := (by exact_mod_cast hb : (minMonoCount k n : ℝ) * (((k - 1 : ℕ) : ℝ) * 2 ^ k) ≤ (n : ℝ) ^ 2)
    rwa [this] at h
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have : (minMonoCount k n : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (((k : ℝ) - 1) * 2 ^ k) := by
    rw [div_le_div_iff₀ hn2 hpos]
    linarith
  linarith

/-! ## The Parrilo-Robertson-Saracino upper bound `δ 3 ≤ 117/2192` -/

/-- the pull-back of `c1` along `x ↦ ⌈x / k⌉`: the PRS colouring of `[1, 548 k]`. -/
def ck (k x : ℕ) : Bool := c1 ((x + (k - 1)) / k)

/-- `0` if `r + s ≤ k`, else `1`: the carry of `r + s` over a multiple of `k`. -/
def u3 (k r s : ℕ) : ℕ := if r + s ≤ k then 0 else 1

/-- the carry (0, 1 or 2) of `r + 2 s` over multiples of `k`. -/
def v3 (k r s : ℕ) : ℕ := if r + 2 * s ≤ k then 0 else if r + 2 * s ≤ 2 * k then 1 else 2

theorem ceil_div (k j w t : ℕ) (hk : 0 < k) (h1 : k * t < w) (h2 : w ≤ k * t + k) :
    (k * j + w + (k - 1)) / k = j + t + 1 := by
  apply Nat.div_eq_of_lt_le
  · have : (j + t + 1) * k = k * j + k * t + k := by ring
    omega
  · have : (j + t + 1 + 1) * k = k * j + k * t + k + k := by ring
    omega

theorem u3_spec (k r s : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ k) (hs1 : 1 ≤ s) (hs2 : s ≤ k) :
    k * u3 k r s < r + s ∧ r + s ≤ k * u3 k r s + k := by
  unfold u3
  split_ifs with h <;> constructor <;> omega

theorem v3_spec (k r s : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ k) (hs1 : 1 ≤ s) (hs2 : s ≤ k) :
    k * v3 k r s < r + 2 * s ∧ r + 2 * s ≤ k * v3 k r s + k := by
  unfold v3
  split_ifs with h h' <;> constructor <;> omega

theorem ck_a (k A r : ℕ) (hk : 0 < k) (hr1 : 1 ≤ r) (hr2 : r ≤ k) :
    ck k (k * A + r) = c1 (A + 1) := by
  unfold ck
  have := ceil_div k A r 0 hk (by omega) (by omega)
  rw [this]

theorem ck_b (k A D r s : ℕ) (hk : 0 < k) (hr1 : 1 ≤ r) (hr2 : r ≤ k) (hs1 : 1 ≤ s) (hs2 : s ≤ k) :
    ck k (k * A + r + (k * D + s)) = c1 (A + D + u3 k r s + 1) := by
  unfold ck
  have h := u3_spec k r s hr1 hr2 hs1 hs2
  have := ceil_div k (A + D) (r + s) (u3 k r s) hk h.1 h.2
  have e : k * A + r + (k * D + s) + (k - 1) = k * (A + D) + (r + s) + (k - 1) := by ring
  rw [e, this]

theorem ck_c (k A D r s : ℕ) (hk : 0 < k) (hr1 : 1 ≤ r) (hr2 : r ≤ k) (hs1 : 1 ≤ s) (hs2 : s ≤ k) :
    ck k (k * A + r + 2 * (k * D + s)) = c1 (A + 2 * D + v3 k r s + 1) := by
  unfold ck
  have h := v3_spec k r s hr1 hr2 hs1 hs2
  have := ceil_div k (A + 2 * D) (r + 2 * s) (v3 k r s) hk h.1 h.2
  have e : k * A + r + 2 * (k * D + s) + (k - 1) = k * (A + 2 * D) + (r + 2 * s) + (k - 1) := by ring
  rw [e, this]

theorem cond3_iff (u v A D : ℕ) :
    cond3 u v A D = true ↔
      A + 2 * D + v + 1 ≤ 548 ∧ c1 (A + 1) = c1 (A + D + u + 1) ∧
        c1 (A + 1) = c1 (A + 2 * D + v + 1) := by
  simp [cond3, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq, and_assoc]

theorem split_pos (k a : ℕ) (hk : 0 < k) (ha : 1 ≤ a) :
    ∃ A r, a = k * A + r ∧ 1 ≤ r ∧ r ≤ k := by
  refine ⟨(a - 1) / k, (a - 1) % k + 1, ?_, by omega, ?_⟩
  · have := Nat.div_add_mod (a - 1) k
    omega
  · have := Nat.mod_lt (a - 1) hk
    omega

/-- the index set of the coarse description. -/
def Pk (k : ℕ) : Finset (ℕ × ℕ) := Finset.Icc 1 k ×ˢ Finset.Icc 1 k

/-- coarse pairs `((r, s), (A, D))` whose triple is monochromatic for `c1`. -/
def Gset (k : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (Pk k ×ˢ (Finset.range 548 ×ˢ Finset.range 548)).filter
    (fun x => cond3 (u3 k x.1.1 x.1.2) (v3 k x.1.1 x.1.2) x.2.1 x.2.2 = true)

theorem monoCount_le_Gset (k : ℕ) (hk : 0 < k) :
    monoCount 3 (548 * k) (ck k) ≤ (Gset k).card := by
  unfold monoCount
  apply Finset.card_le_card_of_surjOn (fun x : (ℕ × ℕ) × (ℕ × ℕ) => (k * x.2.1 + x.1.1, k * x.2.2 + x.1.2))
  rintro ⟨a, d⟩ hy
  simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_setOf_eq] at hy
  obtain ⟨⟨⟨ha1, ha2⟩, hd1, hd2⟩, hn, hall⟩ := hy
  have h1 := hall 1 (by norm_num)
  have h2 := hall 2 (by norm_num)
  obtain ⟨A, r, hae, hr1, hr2⟩ := split_pos k a hk ha1
  obtain ⟨D, s, hde, hs1, hs2⟩ := split_pos k d hk hd1
  subst hae hde
  simp only [one_mul] at h1
  have hv := v3_spec k r s hr1 hr2 hs1 hs2
  have hA : A < 548 := by
    have : k * A < k * 548 := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hD : D < 548 := by
    have : k * D < k * 548 := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hle : A + 2 * D + v3 k r s + 1 ≤ 548 := by
    by_contra hcon
    have h548 : 548 ≤ A + 2 * D + v3 k r s := by omega
    have hm : k * 548 ≤ k * (A + 2 * D + v3 k r s) := Nat.mul_le_mul_left _ h548
    have e : k * (A + 2 * D + v3 k r s) = k * A + 2 * (k * D) + k * v3 k r s := by ring
    simp only [Nat.reduceSub] at hn
    omega
  have hc1 : c1 (A + 1) = c1 (A + D + u3 k r s + 1) := by
    rw [← ck_a k A r hk hr1 hr2, ← ck_b k A D r s hk hr1 hr2 hs1 hs2]
    exact h1.symm
  have hc2 : c1 (A + 1) = c1 (A + 2 * D + v3 k r s + 1) := by
    rw [← ck_a k A r hk hr1 hr2, ← ck_c k A D r s hk hr1 hr2 hs1 hs2]
    exact h2.symm
  refine ⟨((r, s), (A, D)), ?_, rfl⟩
  simp only [Finset.coe_filter, Gset, Pk, Finset.mem_product, Finset.mem_Icc, Finset.mem_range,
    Set.mem_setOf_eq]
  exact ⟨⟨⟨⟨hr1, hr2⟩, hs1, hs2⟩, hA, hD⟩, (cond3_iff _ _ _ _).mpr ⟨hle, hc1, hc2⟩⟩

theorem card_filter_prod {α β : Type*} (s : Finset α) (t : Finset β) (p : α → β → Prop)
    [∀ a b, Decidable (p a b)] :
    ((s ×ˢ t).filter (fun x => p x.1 x.2)).card = ∑ a ∈ s, (t.filter (p a)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.card_filter]

theorem cntD_eq (u v A m : ℕ) :
    cntD u v A m = ((Finset.range m).filter (fun D => cond3 u v A D = true)).card := by
  induction m with
  | zero => simp [cntD]
  | succ m ih =>
    rw [cntD, ih, Finset.range_succ, Finset.filter_insert]
    cases h : cond3 u v A m
    · simp
    · simp only [if_true, cond_true]
      rw [Finset.card_insert_of_notMem (by simp)]

theorem sum_cntD_eq (u v m : ℕ) :
    ∑ A ∈ Finset.range m, cntD u v A 548 = cntRange u v 0 m := by
  induction m with
  | zero => simp [cntRange]
  | succ m ih => rw [Finset.sum_range_succ, ih, cntRange, Nat.zero_add]

theorem cardB (u v : ℕ) :
    ((Finset.range 548 ×ˢ Finset.range 548).filter (fun b : ℕ × ℕ => cond3 u v b.1 b.2 = true)).card =
      cntRange u v 0 548 := by
  rw [card_filter_prod (Finset.range 548) (Finset.range 548) (fun A D => cond3 u v A D = true)]
  rw [← sum_cntD_eq]
  apply Finset.sum_congr rfl
  intro A _
  rw [cntD_eq]

theorem card_Gset (k : ℕ) :
    (Gset k).card = ∑ p ∈ Pk k, cntRange (u3 k p.1 p.2) (v3 k p.1 p.2) 0 548 := by
  unfold Gset
  rw [card_filter_prod (Pk k) (Finset.range 548 ×ˢ Finset.range 548)
    (fun p b => cond3 (u3 k p.1 p.2) (v3 k p.1 p.2) b.1 b.2 = true)]
  apply Finset.sum_congr rfl
  intro p _
  rw [cardB]

/-- the region `r + 2 s ≤ k` of the unit square (a triangle of area `k²/4`) -/
def R00 (k : ℕ) : Finset (ℕ × ℕ) := (Pk k).filter fun p => p.1 + 2 * p.2 ≤ k

/-- the region `r + 2 s > 2k` -/
def R12 (k : ℕ) : Finset (ℕ × ℕ) := (Pk k).filter fun p => 2 * k < p.1 + 2 * p.2

theorem R00_le_R12 (k : ℕ) : (R00 k).card ≤ (R12 k).card := by
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (k + 1 - p.1, k + 1 - p.2))
  · intro p hp
    simp only [R00, R12, Pk, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_setOf_eq, Finset.mem_coe] at hp ⊢
    omega
  · intro p hp q hq h
    simp only [R00, Pk, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_setOf_eq] at hp hq
    simp only [Prod.mk.injEq] at h
    ext <;> omega

theorem two_Tri_le (k : ℕ) :
    2 * ((Pk k).filter fun p => p.1 + p.2 ≤ k).card ≤ k ^ 2 := by
  set Tri := (Pk k).filter fun p => p.1 + p.2 ≤ k with hTri
  have hcard : (Tri ×ˢ (Finset.univ : Finset Bool)).card = 2 * Tri.card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]; ring
  have hP : (Pk k).card = k ^ 2 := by simp [Pk, sq]
  rw [← hP, ← hcard]
  apply Finset.card_le_card_of_injOn
    (fun x : (ℕ × ℕ) × Bool => if x.2 then (k + 1 - x.1.1, k + 1 - x.1.2) else x.1)
  · rintro ⟨p, b⟩ hx
    simp only [hTri, Pk, Finset.coe_product, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_setOf_eq, Set.mem_prod, Finset.coe_univ, Set.mem_univ, and_true, Finset.mem_coe] at hx ⊢
    cases b <;> simp <;> omega
  · rintro ⟨p, b⟩ hx ⟨q, b'⟩ hy h
    simp only [hTri, Pk, Finset.coe_product, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_setOf_eq, Set.mem_prod, Finset.coe_univ, Set.mem_univ, and_true] at hx hy
    cases b <;> cases b' <;> simp at h <;> simp [Prod.ext_iff] at h ⊢ <;> omega

theorem two_R00_le_Tri (k : ℕ) :
    2 * (R00 k).card ≤ ((Pk k).filter fun p => p.1 + p.2 ≤ k).card := by
  set Tri := (Pk k).filter fun p => p.1 + p.2 ≤ k with hTri
  have hcard : (R00 k ×ˢ (Finset.univ : Finset Bool)).card = 2 * (R00 k).card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]; ring
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun x : (ℕ × ℕ) × Bool => if x.2 then (x.1.2, x.1.1 + x.1.2) else (x.1.1 + x.1.2, x.1.2))
  · rintro ⟨p, b⟩ hx
    simp only [hTri, R00, Pk, Finset.coe_product, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_setOf_eq, Set.mem_prod, Finset.coe_univ, Set.mem_univ, and_true, Finset.mem_coe] at hx ⊢
    cases b <;> simp <;> omega
  · rintro ⟨p, b⟩ hx ⟨q, b'⟩ hy h
    simp only [R00, Pk, Finset.coe_product, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_setOf_eq, Set.mem_prod, Finset.coe_univ, Set.mem_univ, and_true] at hx hy
    cases b <;> cases b' <;> simp at h <;> simp [Prod.ext_iff] at h ⊢ <;> omega

theorem four_R00_le (k : ℕ) : 4 * (R00 k).card ≤ k ^ 2 := by
  have h1 := two_R00_le_Tri k
  have h2 := two_Tri_le k
  omega

theorem cnt_pointwise (k : ℕ) (p : ℕ × ℕ) (hp : p ∈ Pk k) :
    cntRange (u3 k p.1 p.2) (v3 k p.1 p.2) 0 548 + 272 * (if 2 * k < p.1 + 2 * p.2 then 1 else 0) ≤
      16028 + 276 * (if p.1 + 2 * p.2 ≤ k then 1 else 0) := by
  simp only [Pk, Finset.mem_product, Finset.mem_Icc] at hp
  obtain ⟨⟨hr1, hr2⟩, hs1, hs2⟩ := hp
  unfold u3 v3
  by_cases h0 : p.1 + 2 * p.2 ≤ k
  · have h' : p.1 + p.2 ≤ k := by omega
    have hR : ¬ 2 * k < p.1 + 2 * p.2 := by omega
    simp [h0, h', hR, cnt_00]
  · by_cases h1 : p.1 + p.2 ≤ k
    · have h' : p.1 + 2 * p.2 ≤ 2 * k := by omega
      have hR : ¬ 2 * k < p.1 + 2 * p.2 := by omega
      simp [h0, h1, h', hR, cnt_01]
    · by_cases h2 : p.1 + 2 * p.2 ≤ 2 * k
      · have hR : ¬ 2 * k < p.1 + 2 * p.2 := by omega
        simp [h0, h1, h2, hR, cnt_11]
      · have h3 : 2 * k < p.1 + 2 * p.2 := by omega
        simp [h0, h1, h2, h3, cnt_12]

theorem monoCount_ck_le (k : ℕ) (hk : 0 < k) : monoCount 3 (548 * k) (ck k) ≤ 16029 * k ^ 2 := by
  have h1 := monoCount_le_Gset k hk
  rw [card_Gset] at h1
  have hsum : ∑ p ∈ Pk k, (cntRange (u3 k p.1 p.2) (v3 k p.1 p.2) 0 548 +
      272 * (if 2 * k < p.1 + 2 * p.2 then 1 else 0)) ≤
      ∑ p ∈ Pk k, (16028 + 276 * (if p.1 + 2 * p.2 ≤ k then 1 else 0)) :=
    Finset.sum_le_sum (fun p hp => cnt_pointwise k p hp)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.card_filter, ← Finset.card_filter, Finset.sum_const, smul_eq_mul] at hsum
  have hP : (Pk k).card = k ^ 2 := by simp [Pk, sq]
  have hR : (R12 k).card = ((Pk k).filter fun p => 2 * k < p.1 + 2 * p.2).card := rfl
  have hR0 : (R00 k).card = ((Pk k).filter fun p => p.1 + 2 * p.2 ≤ k).card := rfl
  have h2 := R00_le_R12 k
  have h3 := four_R00_le k
  rw [hP] at hsum
  rw [← hR, ← hR0] at hsum
  omega

/-! ## Positivity of `δ k` (van der Waerden + supersaturation) -/

/-- **Finite van der Waerden** (from the finite Hales-Jewett theorem of Mathlib): there is `W` such that
every `2`-colouring of `ℕ` has a monochromatic `k`-term progression `a, a + d, …, a + (k-1) d` with
`1 ≤ a`, `1 ≤ d` and `a + (k-1) d ≤ W`. -/
theorem vdw_finite (k : ℕ) (hk : 1 ≤ k) :
    ∃ W : ℕ, ∀ c : ℕ → Bool, ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ W ∧
      ∀ i < k, c (a + i * d) = c a := by
  classical
  obtain ⟨ι, _inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) Bool
  refine ⟨1 + Fintype.card ι * (k - 1), fun c => ?_⟩
  obtain ⟨l, c0, hl⟩ := hι (fun v => c (1 + ∑ i, (v i : ℕ)))
  set s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none) with hs
  set f : ι → ℕ := fun i => ((l.idxFun i).map (fun y : Fin k => (y : ℕ))).getD 0 with hf
  have key : ∀ x : Fin k, ∑ i, ((l x i : Fin k) : ℕ) = s.card * (x : ℕ) + ∑ i ∈ sᶜ, f i := by
    intro x
    rw [← Finset.sum_add_sum_compl s]
    congr 1
    · calc ∑ i ∈ s, ((l x i : Fin k) : ℕ) = ∑ i ∈ s, (x : ℕ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hs, Finset.mem_filter] at hi
            rw [Combinatorics.Line.apply_none l x i hi.2]
        _ = s.card * (x : ℕ) := by rw [Finset.sum_const, smul_eq_mul]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hs, Finset.compl_filter, Finset.mem_filter] at hi
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.2
      simp [hf, ← hy]
  have hfle : ∀ i, f i ≤ k - 1 := by
    intro i
    rcases h : l.idxFun i with _ | y
    · simp [hf, h]
    · have := y.isLt
      simp only [hf, h, Option.map_some, Option.getD_some]
      omega
  have hd : 1 ≤ s.card :=
    Finset.card_pos.mpr ⟨l.proper.choose, by simp [hs, l.proper.choose_spec]⟩
  have hcard := Finset.card_add_card_compl s
  have hsum : ∑ i ∈ sᶜ, f i ≤ sᶜ.card * (k - 1) := by
    have := Finset.sum_le_card_nsmul sᶜ f (k - 1) (fun i _ => hfle i)
    simpa [smul_eq_mul] using this
  refine ⟨1 + ∑ i ∈ sᶜ, f i, s.card, by omega, hd, ?_, ?_⟩
  · calc 1 + ∑ i ∈ sᶜ, f i + (k - 1) * s.card ≤ 1 + sᶜ.card * (k - 1) + (k - 1) * s.card := by omega
      _ = 1 + (s.card + sᶜ.card) * (k - 1) := by ring
      _ = 1 + Fintype.card ι * (k - 1) := by rw [hcard]
  · intro i hi
    have h1 := hl ⟨i, hi⟩
    have h0 := hl ⟨0, by omega⟩
    simp only [key] at h1 h0
    have e1 : 1 + (s.card * (⟨i, hi⟩ : Fin k).val + ∑ j ∈ sᶜ, f j) =
        1 + ∑ j ∈ sᶜ, f j + i * s.card := by
      simp only [Fin.val_mk]; ring
    have e0 : 1 + (s.card * (⟨0, by omega⟩ : Fin k).val + ∑ j ∈ sᶜ, f j) =
        1 + ∑ j ∈ sᶜ, f j + 0 * s.card := by
      simp only [Fin.val_mk]; ring
    simp only [e1] at h1
    simp only [e0] at h0
    rw [h1]
    simpa using h0.symm

/-- `q` is a `k`-progression of `[1,n]` lying inside the `W`-term window `w`:
`q = (w.1 + (a'-1) w.2, d' w.2)` for some `a', d' ∈ [1, W]`. -/
def rel (W : ℕ) (w q : ℕ × ℕ) : Prop :=
  ∃ a' d' : ℕ, 1 ≤ a' ∧ a' ≤ W ∧ 1 ≤ d' ∧ d' ≤ W ∧ q.1 = w.1 + (a' - 1) * w.2 ∧ q.2 = d' * w.2

theorem window_has_ap (k n W : ℕ) (hk : 2 ≤ k)
    (hW : ∀ c : ℕ → Bool, ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ W ∧
      ∀ i < k, c (a + i * d) = c a)
    (c : ℕ → Bool) (w : ℕ × ℕ) (hw : w ∈ aps W n) :
    ∃ q ∈ (aps k n).filter (fun p : ℕ × ℕ => ∀ i < k, c (p.1 + i * p.2) = c p.1), rel W w q := by
  simp only [aps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hw
  obtain ⟨⟨⟨hx1, hx2⟩, he1, he2⟩, hwn⟩ := hw
  obtain ⟨a', d', ha1, hd1, hbound, hmono⟩ := hW (fun t => c (w.1 + (t - 1) * w.2))
  have hk1 : 1 ≤ k - 1 := by omega
  have ha2 : a' ≤ W := by
    have : 1 * d' ≤ (k - 1) * d' := Nat.mul_le_mul_right _ hk1
    omega
  have hd2 : d' ≤ W := by
    have : 1 * d' ≤ (k - 1) * d' := Nat.mul_le_mul_right _ hk1
    omega
  have hq2 : 1 ≤ d' * w.2 := Nat.mul_pos hd1 he1
  have e1 : w.1 + (a' - 1) * w.2 + (k - 1) * (d' * w.2) = w.1 + ((a' - 1) + (k - 1) * d') * w.2 := by ring
  have e2 : ((a' - 1) + (k - 1) * d') * w.2 ≤ (W - 1) * w.2 := Nat.mul_le_mul_right _ (by omega)
  have hbig : w.1 + (a' - 1) * w.2 + (k - 1) * (d' * w.2) ≤ n := by omega
  have hq2k : d' * w.2 ≤ (k - 1) * (d' * w.2) := by
    have := Nat.mul_le_mul_right (d' * w.2) hk1
    omega
  refine ⟨(w.1 + (a' - 1) * w.2, d' * w.2), ?_, a', d', ha1, ha2, hd1, hd2, rfl, rfl⟩
  simp only [aps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨⟨⟨by omega, by omega⟩, hq2, by omega⟩, hbig⟩, ?_⟩
  intro i hi
  have h := hmono i hi
  have e3 : a' + i * d' - 1 = (a' - 1) + i * d' := by omega
  simp only [e3] at h
  have e4 : w.1 + ((a' - 1) + i * d') * w.2 = w.1 + (a' - 1) * w.2 + i * (d' * w.2) := by ring
  rw [e4] at h
  simpa using h

open Classical in
theorem card_rel_le (W n : ℕ) (q : ℕ × ℕ) :
    ((aps W n).filter (fun w => rel W w q)).card ≤ W * W := by
  have hsub : (aps W n).filter (fun w => rel W w q) ⊆
      ((Finset.Icc 1 W ×ˢ Finset.Icc 1 W).image
        (fun p : ℕ × ℕ => (q.1 - (p.1 - 1) * (q.2 / p.2), q.2 / p.2))) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨a', d', ha1, ha2, hd1, hd2, h1, h2⟩ := hw.2
    rw [Finset.mem_image]
    refine ⟨(a', d'), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_Icc]; omega
    · have h3 : q.2 / d' = w.2 := by rw [h2]; exact Nat.mul_div_cancel_left w.2 hd1
      simp only [h3]
      ext
      · simp only; omega
      · rfl
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 W ×ˢ Finset.Icc 1 W).card := Finset.card_image_le
    _ = W * W := by simp

open Classical in
theorem supersat (k W n : ℕ) (hk : 2 ≤ k)
    (hW : ∀ c : ℕ → Bool, ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ W ∧
      ∀ i < k, c (a + i * d) = c a)
    (c : ℕ → Bool) :
    (aps W n).card ≤ monoCount k n c * (W * W) := by
  rw [monoCount_eq]
  set M := (aps k n).filter (fun p : ℕ × ℕ => ∀ i < k, c (p.1 + i * p.2) = c p.1) with hM
  calc (aps W n).card = ∑ w ∈ aps W n, 1 := by simp
    _ ≤ ∑ w ∈ aps W n, (M.filter (fun q => rel W w q)).card := by
        apply Finset.sum_le_sum
        intro w hw
        obtain ⟨q, hq, hrel⟩ := window_has_ap k n W hk hW c w hw
        exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hrel⟩⟩
    _ = ∑ w ∈ aps W n, ∑ q ∈ M, if rel W w q then 1 else 0 := by
        apply Finset.sum_congr rfl; intro w _; rw [Finset.card_filter]
    _ = ∑ q ∈ M, ∑ w ∈ aps W n, if rel W w q then 1 else 0 := Finset.sum_comm
    _ = ∑ q ∈ M, ((aps W n).filter (fun w => rel W w q)).card := by
        apply Finset.sum_congr rfl; intro q _; rw [Finset.card_filter]
    _ ≤ ∑ q ∈ M, (W * W) := Finset.sum_le_sum (fun q _ => card_rel_le W n q)
    _ = M.card * (W * W) := by simp

theorem card_aps_ge (W n : ℕ) (hW : 1 ≤ W) : (n / 2) * (n / (2 * W)) ≤ (aps W n).card := by
  have hsub : Finset.Icc 1 (n / 2) ×ˢ Finset.Icc 1 (n / (2 * W)) ⊆ aps W n := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨hx1, hx2⟩, he1, he2⟩ := hp
    simp only [aps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    have h1 : 2 * W * (n / (2 * W)) ≤ n := Nat.mul_div_le n (2 * W)
    have h2 : W * p.2 ≤ W * (n / (2 * W)) := Nat.mul_le_mul_left _ he2
    have h3 : (W - 1) * p.2 ≤ W * p.2 := Nat.mul_le_mul_right _ (by omega)
    have h4 : 2 * W * (n / (2 * W)) = 2 * (W * (n / (2 * W))) := by ring
    have h5 : n / (2 * W) ≤ n := Nat.div_le_self _ _
    refine ⟨⟨⟨hx1, by omega⟩, he1, by omega⟩, by omega⟩
  calc (n / 2) * (n / (2 * W)) = (Finset.Icc 1 (n / 2) ×ˢ Finset.Icc 1 (n / (2 * W))).card := by simp
    _ ≤ _ := Finset.card_le_card hsub

theorem sq_le_monoCount (k W n : ℕ) (hk : 2 ≤ k) (hW1 : 1 ≤ W)
    (hW : ∀ c : ℕ → Bool, ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ W ∧
      ∀ i < k, c (a + i * d) = c a)
    (hn : 4 * W ≤ n) (c : ℕ → Bool) :
    n ^ 2 ≤ 12 * W ^ 3 * monoCount k n c := by
  have h1 := card_aps_ge W n hW1
  have h2 := supersat k W n hk hW c
  set p := n / 2 with hp
  set q := n / (2 * W) with hq
  have hp1 : n ≤ 3 * p := by omega
  have hq1 : n ≤ 4 * W * q := by
    have h3 : n = 2 * W * q + n % (2 * W) := by
      have := Nat.div_add_mod n (2 * W)
      rw [hq]; omega
    have h4 : n % (2 * W) < 2 * W := Nat.mod_lt _ (by omega)
    have h5 : 1 ≤ q := by
      rw [hq]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have h6 : 2 * W * q = 2 * (W * q) := by ring
    have h7 : W ≤ W * q := by nlinarith
    have h8 : 4 * W * q = 4 * (W * q) := by ring
    omega
  have h9 : n * n ≤ (3 * p) * (4 * W * q) := Nat.mul_le_mul hp1 hq1
  have h10 : (3 * p) * (4 * W * q) = 12 * W * (p * q) := by ring
  have h11 : 12 * W * (p * q) ≤ 12 * W * (monoCount k n c * (W * W)) :=
    Nat.mul_le_mul_left _ (h1.trans h2)
  calc n ^ 2 = n * n := by ring
    _ ≤ 12 * W * (monoCount k n c * (W * W)) := h9.trans (h10 ▸ h11)
    _ = 12 * W ^ 3 * monoCount k n c := by ring

theorem exists_min_colouring (k n : ℕ) : ∃ c : ℕ → Bool, monoCount k n c = minMonoCount k n := by
  have hne : ({m : ℕ | ∃ c : ℕ → Bool, monoCount k n c = m}).Nonempty :=
    ⟨monoCount k n (fun _ => true), fun _ => true, rfl⟩
  exact Nat.sInf_mem hne

theorem van_der_waerden_aux (k : ℕ) (hk : 2 ≤ k) : 0 < δ k := by
  obtain ⟨W, hW⟩ := vdw_finite k (by omega)
  have hW1 : 1 ≤ W := by
    obtain ⟨a, d, ha, hd, hb, _⟩ := hW (fun _ => true)
    omega
  have hWpos : (0 : ℝ) < 12 * (W : ℝ) ^ 3 := by positivity
  have hlow : 1 / (12 * (W : ℝ) ^ 3) ≤ δ k := by
    apply le_delta_of_eventually
    filter_upwards [eventually_ge_atTop (4 * W)] with n hn
    obtain ⟨c, hc⟩ := exists_min_colouring k n
    have h := sq_le_monoCount k W n hk hW1 hW hn c
    rw [hc] at h
    have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := by
      have : 0 < n := by omega
      positivity
    rw [div_le_div_iff₀ hWpos hnpos]
    have h' : (n : ℝ) ^ 2 ≤ 12 * (W : ℝ) ^ 3 * (minMonoCount k n : ℝ) := by exact_mod_cast h
    linarith
  exact lt_of_lt_of_le (by positivity) hlow

/-! ## The upper half of `prs_bounds` -/

theorem minMonoCount_ck (K : ℕ) (hK : 0 < K) : minMonoCount 3 (548 * K) ≤ 16029 * K ^ 2 :=
  (minMonoCount_le 3 (548 * K) (ck K)).trans (monoCount_ck_le K hK)

theorem prs_upper : δ 3 ≤ 117 / 2192 := by
  apply delta_le_of_frequently
  intro ε hε
  rw [Filter.frequently_atTop]
  intro a
  refine ⟨548 * (a + 1), by omega, ?_⟩
  have h := minMonoCount_ck (a + 1) (by omega)
  have h' : (minMonoCount 3 (548 * (a + 1)) : ℝ) ≤ 16029 * ((a : ℝ) + 1) ^ 2 := by
    exact_mod_cast h
  have hx : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) < ((548 * (a + 1) : ℕ) : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  push_cast
  have := mul_nonneg hε.le (sq_nonneg (548 * ((a : ℝ) + 1)))
  nlinarith

/-! ## The statements, in the shape of upstream formal-conjectures c83a94d -/

/--
Van der Waerden's theorem implies $\delta_k\gg_k 1$.

For fixed $k$ this says $\delta_k > 0$.
-/
theorem erdos_1186.variants.van_der_waerden (k : ℕ) (hk : 2 ≤ k) : 0 < δ k :=
  van_der_waerden_aux k hk

/--
The probabilistic method implies
$$\delta_k \leq \frac{1}{(k-1)2^{k}}.$$
-/
theorem erdos_1186.variants.probabilistic (k : ℕ) (hk : 2 ≤ k) :
    δ k ≤ 1 / (((k : ℝ) - 1) * 2 ^ k) :=
  probabilistic_aux k hk

/--
Parrilo, Robertson, and Saracino [PRS08] have proved
$$0.0511\approx \frac{1675}{32768}\leq \delta_3 \leq \frac{117}{2192}\approx 0.0533,$$
and conjectured the upper bound is correct.

This is the upper half of upstream `erdos_1186.variants.prs_bounds`
(`1675 / 32768 ≤ δ 3 ∧ δ 3 ≤ 117 / 2192`); the lower half is not proved here.
-/
theorem erdos_1186.variants.prs_bounds_upper : δ 3 ≤ 117 / 2192 := prs_upper

end Erdos1186Day

#print axioms Erdos1186Day.erdos_1186.variants.prs_bounds_upper
#print axioms Erdos1186Day.erdos_1186.variants.probabilistic
#print axioms Erdos1186Day.erdos_1186.variants.van_der_waerden
