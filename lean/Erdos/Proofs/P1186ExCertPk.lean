import Mathlib
import Erdos.Proofs.P1186ExCertTri

/-!
# Erdos 1186 - the triangle terms as packed big-integer sums (lane excert, night 3)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is
its author's.  Hand-written, no certificate numbers.

The triangle part of a certificate is `Σ_t w_t tri_t` over thousands of triangles.  Its coefficients form an `n`-vector
`l` and an `n × n` matrix `q`.  Instead of accumulating them entry by entry, the kernel adds, for every triangle, three
integers `w * c * 2^(W p)` (position `p` = the entry index): the sum over all triangles is one big integer whose
base-`2^W` digits are the entries.  The generated modules check, by `decide +kernel`, exact integer equations between
these sums and the claimed packed tables; the lemmas below turn them into the entry equations
`dec W L a = lS ts a` and `tb W QR a b = qS ts a b` (digit extraction with an offset), and so into `hT` of
`region_of_tabs`.
-/

namespace Erdos1186Ex

open Finset Erdos1186Night2M2

/-! ### Base-`B` digits of a packed natural number -/

theorem digit_pack (B : ℕ) (hB : 0 < B) : ∀ (n : ℕ) (d : ℕ → ℕ), (∀ a < n, d a < B) →
    ∀ a < n, ((∑ c ∈ range n, d c * B ^ c) / B ^ a) % B = d a := by
  intro n
  induction n with
  | zero => intro d _ a ha; exact absurd ha (Nat.not_lt_zero _)
  | succ n ih =>
    intro d hd a ha
    have hd0 : d 0 < B := hd 0 (Nat.succ_pos n)
    have e : ∑ c ∈ range (n + 1), d c * B ^ c = d 0 + B * ∑ c ∈ range n, d (c + 1) * B ^ c := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [e]
    have hdiv : (d 0 + B * ∑ c ∈ range n, d (c + 1) * B ^ c) / B = ∑ c ∈ range n, d (c + 1) * B ^ c := by
      rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hd0, zero_add]
    cases a with
    | zero =>
      simp only [pow_zero, Nat.div_one]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd0]
    | succ a =>
      have ha' : a < n := by omega
      rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
      exact ih (fun c => d (c + 1)) (fun c hc => hd (c + 1) (by omega)) a ha'

theorem pack_lt (B : ℕ) : ∀ (n : ℕ) (d : ℕ → ℕ), (∀ a < n, d a < B) → ∑ c ∈ range n, d c * B ^ c < B ^ n
  | 0, d, _ => by simp
  | n + 1, d, hd => by
    rw [Finset.sum_range_succ]
    have ih := pack_lt B n d (fun a ha => hd a (by omega))
    have h2 := hd n (by omega)
    calc ∑ c ∈ range n, d c * B ^ c + d n * B ^ n < B ^ n + d n * B ^ n := Nat.add_lt_add_right ih _
      _ = (d n + 1) * B ^ n := by ring
      _ ≤ B * B ^ n := Nat.mul_le_mul_right _ h2
      _ = B ^ (n + 1) := by ring

/-- `2^(W p)` as an integer. -/
def bp (W p : ℕ) : ℤ := ((2 ^ (W * p) : ℕ) : ℤ)

theorem bp_eq (W a : ℕ) : bp W a = ((2 ^ W : ℕ) : ℤ) ^ a := by
  unfold bp
  push_cast
  rw [pow_mul]

theorem bp_add (W n a b : ℕ) : bp W (n * a + b) = bp (W * n) a * bp W b := by
  unfold bp
  push_cast
  rw [← pow_add]
  congr 1
  ring

theorem two_pow_eq (W : ℕ) (hW : 1 ≤ W) : 2 ^ W = 2 * 2 ^ (W - 1) := by
  rw [← pow_succ']
  congr 1
  omega

/-- digits of an offset packing: if `P = Σ (v a + H) 2^(W a)` with `-H ≤ v a < H`, `H = 2^(W-1)`, then `dec W P a = v a`. -/
theorem dec_of_pack (W : ℕ) (hW : 1 ≤ W) (n : ℕ) (v : ℕ → ℤ) (P : ℕ)
    (hv : ∀ a < n, -((2 ^ (W - 1) : ℕ) : ℤ) ≤ v a ∧ v a < ((2 ^ (W - 1) : ℕ) : ℤ))
    (hP : (P : ℤ) = ∑ a ∈ range n, (v a + ((2 ^ (W - 1) : ℕ) : ℤ)) * bp W a) : ∀ a < n, dec W P a = v a := by
  have hB : 2 ^ W = 2 * 2 ^ (W - 1) := two_pow_eq W hW
  generalize hH : 2 ^ (W - 1) = H at hB hv hP
  have hBi : ((2 ^ W : ℕ) : ℤ) = 2 * (H : ℤ) := by exact_mod_cast hB
  have hd : ∀ a < n, (((v a + (H : ℤ)).toNat : ℕ) : ℤ) = v a + H := by
    intro a ha
    exact Int.toNat_of_nonneg (by have := (hv a ha).1; omega)
  have hdlt : ∀ a < n, (v a + (H : ℤ)).toNat < 2 ^ W := by
    intro a ha
    have h1 := hd a ha
    have h2 := (hv a ha).2
    have : (((v a + (H : ℤ)).toNat : ℕ) : ℤ) < ((2 ^ W : ℕ) : ℤ) := by rw [h1, hBi]; omega
    exact_mod_cast this
  have hsum : (∑ c ∈ range n, (v c + (H : ℤ)).toNat * (2 ^ W) ^ c) = P := by
    have : ((∑ c ∈ range n, (v c + (H : ℤ)).toNat * (2 ^ W) ^ c : ℕ) : ℤ) = (P : ℤ) := by
      rw [hP]
      push_cast
      apply Finset.sum_congr rfl
      intro c hc
      rw [hd c (Finset.mem_range.mp hc), bp_eq]
      push_cast
      ring
    exact_mod_cast this
  intro a ha
  have h := digit_pack (2 ^ W) (by positivity) n (fun c => (v c + (H : ℤ)).toNat) hdlt a ha
  simp only [] at h
  rw [hsum] at h
  unfold dec
  rw [hH, pow_mul, h, hd a ha]
  ring

/-- digits of a table of offset-packed rows. -/
theorem tb_of_pack (W n : ℕ) (hW : 1 ≤ W) (v : ℕ → ℕ → ℤ) (QR : List ℕ)
    (hv : ∀ a < n, ∀ b < n, -((2 ^ (W - 1) : ℕ) : ℤ) ≤ v a b ∧ v a b < ((2 ^ (W - 1) : ℕ) : ℤ))
    (hQR : ∀ a < n, QR.getD a 0 < 2 ^ (W * n))
    (hX : ((∑ a ∈ range n, QR.getD a 0 * (2 ^ (W * n)) ^ a : ℕ) : ℤ) =
        ∑ a ∈ range n, (∑ b ∈ range n, (v a b + ((2 ^ (W - 1) : ℕ) : ℤ)) * bp W b) * bp (W * n) a) :
    ∀ a < n, ∀ b < n, tb W QR a b = v a b := by
  have hB : 2 ^ W = 2 * 2 ^ (W - 1) := two_pow_eq W hW
  generalize hH : 2 ^ (W - 1) = H at hB hv hX
  have hBi : ((2 ^ W : ℕ) : ℤ) = 2 * (H : ℤ) := by exact_mod_cast hB
  have hd : ∀ a < n, ∀ b < n, (((v a b + (H : ℤ)).toNat : ℕ) : ℤ) = v a b + H := by
    intro a ha b hb
    exact Int.toNat_of_nonneg (by have := (hv a ha b hb).1; omega)
  have hdlt : ∀ a < n, ∀ b < n, (v a b + (H : ℤ)).toNat < 2 ^ W := by
    intro a ha b hb
    have h1 := hd a ha b hb
    have h2 := (hv a ha b hb).2
    have : (((v a b + (H : ℤ)).toNat : ℕ) : ℤ) < ((2 ^ W : ℕ) : ℤ) := by rw [h1, hBi]; omega
    exact_mod_cast this
  -- the rows
  let e : ℕ → ℕ := fun a => ∑ b ∈ range n, (v a b + (H : ℤ)).toNat * (2 ^ W) ^ b
  have he_lt : ∀ a < n, e a < 2 ^ (W * n) := by
    intro a ha
    have := pack_lt (2 ^ W) n (fun b => (v a b + (H : ℤ)).toNat) (fun b hb => hdlt a ha b hb)
    rw [← pow_mul] at this
    exact this
  have he_cast : ∀ a < n, (e a : ℤ) = ∑ b ∈ range n, (v a b + (H : ℤ)) * bp W b := by
    intro a ha
    simp only [e]
    push_cast
    apply Finset.sum_congr rfl
    intro b hb
    rw [hd a ha b (Finset.mem_range.mp hb), bp_eq]
    push_cast
    ring
  have hsum : (∑ a ∈ range n, e a * (2 ^ (W * n)) ^ a) = ∑ a ∈ range n, QR.getD a 0 * (2 ^ (W * n)) ^ a := by
    have : ((∑ a ∈ range n, e a * (2 ^ (W * n)) ^ a : ℕ) : ℤ) = ((∑ a ∈ range n, QR.getD a 0 * (2 ^ (W * n)) ^ a : ℕ) : ℤ) := by
      rw [hX]
      push_cast
      apply Finset.sum_congr rfl
      intro a ha
      rw [he_cast a (Finset.mem_range.mp ha), bp_eq (W * n) a]
      push_cast
      ring
    exact_mod_cast this
  have hCpos : 0 < 2 ^ (W * n) := by positivity
  intro a ha b hb
  have h1 := digit_pack (2 ^ (W * n)) hCpos n e he_lt a ha
  have h2 := digit_pack (2 ^ (W * n)) hCpos n (fun a => QR.getD a 0) hQR a ha
  simp only [] at h2
  rw [← hsum] at h2
  have hrow : QR.getD a 0 = e a := by rw [← h1, ← h2]
  have hpack : (e a : ℤ) = ∑ b ∈ range n, (v a b + (H : ℤ)) * bp W b := he_cast a ha
  have hvr : ∀ b < n, -(2 ^ (W - 1) : ℕ) ≤ v a b ∧ v a b < ((2 ^ (W - 1) : ℕ) : ℤ) := by
    intro b hb; rw [hH]; exact hv a ha b hb
  have := dec_of_pack W hW n (v a) (e a) (by intro b hb; have := hv a ha b hb; rw [hH]; exact this)
    (by rw [hH]; exact hpack) b hb
  unfold tb
  rw [hrow]
  exact this

/-! ### The per-triangle terms -/

def cterm (t : TriT) : ℤ := t.w * tc t

def lterm (W : ℕ) (t : TriT) : ℤ :=
  (t.w * (-2 * (t.s1 + t.s3))) * bp W t.i + (t.w * (-2 * (t.s1 + t.s2))) * bp W t.j
    + (t.w * (-2 * (t.s2 + t.s3))) * bp W t.k

def qterm (W n : ℕ) (t : TriT) : ℤ :=
  (t.w * (4 * t.s1)) * bp W (n * t.i + t.j) + (t.w * (4 * t.s2)) * bp W (n * t.j + t.k)
    + (t.w * (4 * t.s3)) * bp W (n * t.i + t.k)

def wterm (t : TriT) : ℤ := t.w

theorem sumI_if (n i : ℕ) (hi : i < n) (f : ℕ → ℤ) :
    ∑ a ∈ range n, (if a = i then f a else 0) = f i := by
  rw [Finset.sum_ite_eq']
  simp [hi]

theorem sumI_if2 (n i j : ℕ) (hi : i < n) (hj : j < n) (f : ℕ → ℕ → ℤ) :
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

theorem sum_tl (W n : ℕ) (t : TriT) (hi : t.i < n) (hj : t.j < n) (hk : t.k < n) :
    ∑ a ∈ range n, (t.w * tl t a) * bp W a = lterm W t := by
  have h : ∀ a, (t.w * tl t a) * bp W a = (if a = t.i then (t.w * (-2 * (t.s1 + t.s3))) * bp W a else 0)
      + (if a = t.j then (t.w * (-2 * (t.s1 + t.s2))) * bp W a else 0)
      + (if a = t.k then (t.w * (-2 * (t.s2 + t.s3))) * bp W a else 0) := by
    intro a
    unfold tl
    split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib]
  rw [sumI_if n t.i hi (fun a => (t.w * (-2 * (t.s1 + t.s3))) * bp W a),
    sumI_if n t.j hj (fun a => (t.w * (-2 * (t.s1 + t.s2))) * bp W a),
    sumI_if n t.k hk (fun a => (t.w * (-2 * (t.s2 + t.s3))) * bp W a)]
  rfl

theorem sum_tq (W n : ℕ) (t : TriT) (hi : t.i < n) (hj : t.j < n) (hk : t.k < n) :
    ∑ a ∈ range n, ∑ b ∈ range n, (t.w * tq t a b) * bp W (n * a + b) = qterm W n t := by
  have h : ∀ a b, (t.w * tq t a b) * bp W (n * a + b) =
      (if a = t.i ∧ b = t.j then (t.w * (4 * t.s1)) * bp W (n * a + b) else 0)
      + (if a = t.j ∧ b = t.k then (t.w * (4 * t.s2)) * bp W (n * a + b) else 0)
      + (if a = t.i ∧ b = t.k then (t.w * (4 * t.s3)) * bp W (n * a + b) else 0) := by
    intro a b
    unfold tq
    split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib]
  rw [sumI_if2 n t.i t.j hi hj (fun a b => (t.w * (4 * t.s1)) * bp W (n * a + b)),
    sumI_if2 n t.j t.k hj hk (fun a b => (t.w * (4 * t.s2)) * bp W (n * a + b)),
    sumI_if2 n t.i t.k hi hk (fun a b => (t.w * (4 * t.s3)) * bp W (n * a + b))]
  rfl

theorem ok_idx (n : ℕ) (t : TriT) (ht : t.ok n = true) : t.i < n ∧ t.j < n ∧ t.k < n := by
  unfold TriT.ok at ht
  obtain ⟨hi, hj, hk, _⟩ := of_decide_eq_true ht
  exact ⟨hi, hj, hk⟩

theorem ok_w (n : ℕ) (t : TriT) (ht : t.ok n = true) : 0 ≤ t.w := by
  unfold TriT.ok at ht
  obtain ⟨_, _, _, _, _, _, _, hw⟩ := of_decide_eq_true ht
  exact hw

theorem sum_lS (W n : ℕ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) →
    ∑ a ∈ range n, lS ts a * bp W a = (ts.map (lterm W)).sum
  | [], _ => by simp [lS]
  | t :: ts, h => by
      have ht := h t (by simp)
      have ih := sum_lS W n ts (fun s hs => h s (by simp [hs]))
      obtain ⟨hi, hj, hk⟩ := ok_idx n t ht
      have e : ∀ a, lS (t :: ts) a * bp W a = (t.w * tl t a) * bp W a + lS ts a * bp W a := by
        intro a
        simp only [lS, List.map_cons, List.sum_cons]
        ring
      simp only [e, Finset.sum_add_distrib, ih, sum_tl W n t hi hj hk, List.map_cons, List.sum_cons]

theorem sum_qS (W n : ℕ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) →
    ∑ a ∈ range n, ∑ b ∈ range n, qS ts a b * bp W (n * a + b) = (ts.map (qterm W n)).sum
  | [], _ => by simp [qS]
  | t :: ts, h => by
      have ht := h t (by simp)
      have ih := sum_qS W n ts (fun s hs => h s (by simp [hs]))
      obtain ⟨hi, hj, hk⟩ := ok_idx n t ht
      have e : ∀ a b, qS (t :: ts) a b * bp W (n * a + b)
          = (t.w * tq t a b) * bp W (n * a + b) + qS ts a b * bp W (n * a + b) := by
        intro a b
        simp only [qS, List.map_cons, List.sum_cons]
        ring
      simp only [e, Finset.sum_add_distrib, ih, sum_tq W n t hi hj hk, List.map_cons, List.sum_cons]

/-! ### Bounds on the entries -/

theorem abs_tl_le (n : ℕ) (t : TriT) (ht : t.ok n = true) (a : ℕ) : |tl t a| ≤ 12 := by
  unfold TriT.ok at ht
  obtain ⟨_, _, _, h1, h2, h3, _, _⟩ := of_decide_eq_true ht
  rw [abs_le]
  unfold tl
  constructor <;> split_ifs <;> omega

theorem abs_tq_le (n : ℕ) (t : TriT) (ht : t.ok n = true) (a b : ℕ) : |tq t a b| ≤ 12 := by
  unfold TriT.ok at ht
  obtain ⟨_, _, _, h1, h2, h3, _, _⟩ := of_decide_eq_true ht
  rw [abs_le]
  unfold tq
  constructor <;> split_ifs <;> omega

theorem abs_lS_le (n : ℕ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) → ∀ a,
    |lS ts a| ≤ 12 * (ts.map (fun t => t.w)).sum
  | [], _, a => by simp [lS]
  | t :: ts, h, a => by
      have ht := h t (by simp)
      have ih := abs_lS_le n ts (fun s hs => h s (by simp [hs])) a
      have hw := ok_w n t ht
      have hl := abs_tl_le n t ht a
      have e : lS (t :: ts) a = t.w * tl t a + lS ts a := by simp [lS]
      have h1 : |t.w * tl t a| ≤ 12 * t.w := by
        rw [abs_mul, abs_of_nonneg hw]
        nlinarith [abs_nonneg (tl t a)]
      rw [e, List.map_cons, List.sum_cons]
      calc |t.w * tl t a + lS ts a| ≤ |t.w * tl t a| + |lS ts a| := abs_add_le _ _
        _ ≤ 12 * t.w + 12 * (ts.map (fun t => t.w)).sum := by linarith
        _ = 12 * (t.w + (ts.map (fun t => t.w)).sum) := by ring

theorem abs_qS_le (n : ℕ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) → ∀ a b,
    |qS ts a b| ≤ 12 * (ts.map (fun t => t.w)).sum
  | [], _, a, b => by simp [qS]
  | t :: ts, h, a, b => by
      have ht := h t (by simp)
      have ih := abs_qS_le n ts (fun s hs => h s (by simp [hs])) a b
      have hw := ok_w n t ht
      have hl := abs_tq_le n t ht a b
      have e : qS (t :: ts) a b = t.w * tq t a b + qS ts a b := by simp [qS]
      have h1 : |t.w * tq t a b| ≤ 12 * t.w := by
        rw [abs_mul, abs_of_nonneg hw]
        nlinarith [abs_nonneg (tq t a b)]
      rw [e, List.map_cons, List.sum_cons]
      calc |t.w * tq t a b + qS ts a b| ≤ |t.w * tq t a b| + |qS ts a b| := abs_add_le _ _
        _ ≤ 12 * t.w + 12 * (ts.map (fun t => t.w)).sum := by linarith
        _ = 12 * (t.w + (ts.map (fun t => t.w)).sum) := by ring

/-! ### Sums over groups of chunks, and the offsets -/

/-- the sum of `f` over all triangles of all chunks. -/
def gsum (f : TriT → ℤ) (cs : List (List TriT)) : ℤ := (cs.map (fun ch => (ch.map f).sum)).sum

theorem gsum_eq (f : TriT → ℤ) : ∀ cs : List (List TriT), gsum f cs = (cs.flatten.map f).sum
  | [] => by simp [gsum]
  | ch :: cs => by
      have ih := gsum_eq f cs
      simp only [gsum, List.map_cons, List.sum_cons, List.flatten_cons, List.map_append, List.sum_append] at ih ⊢
      rw [ih]

theorem gsum_append (f : TriT → ℤ) (A B : List (List TriT)) : gsum f (A ++ B) = gsum f A + gsum f B := by
  simp [gsum, List.map_append, List.sum_append]

theorem list_sum_range (f : ℕ → ℤ) : ∀ n : ℕ, ((List.range n).map f).sum = ∑ a ∈ range n, f a
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, list_sum_range f n]
      simp

theorem list_sum_range_nat (f : ℕ → ℕ) : ∀ n : ℕ, ((List.range n).map f).sum = ∑ a ∈ range n, f a
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, list_sum_range_nat f n]
      simp

/-- `Σ_{a<n} H 2^(W a)`: the offset of a packed vector. -/
def offL (W n : ℕ) : ℤ := ((List.range n).map (fun a => ((2 ^ (W - 1) : ℕ) : ℤ) * bp W a)).sum

/-- the offset of a packed table: `Σ_{a<n} (Σ_{b<n} H 2^(W b)) 2^(W n a)`. -/
def offQ (W n : ℕ) : ℤ := ((List.range n).map (fun a => offL W n * bp (W * n) a)).sum

/-- the natural number with rows `QR` packed in base `2^(W n)`. -/
def packRows (W n : ℕ) (QR : List ℕ) : ℕ := ((List.range n).map (fun a => QR.getD a 0 * (2 ^ (W * n)) ^ a)).sum

theorem offL_eq (W n : ℕ) : offL W n = ∑ a ∈ range n, ((2 ^ (W - 1) : ℕ) : ℤ) * bp W a := by
  unfold offL
  exact list_sum_range _ n

theorem offQ_eq (W n : ℕ) : offQ W n = ∑ a ∈ range n, offL W n * bp (W * n) a := by
  unfold offQ
  exact list_sum_range _ n

theorem packRows_eq (W n : ℕ) (QR : List ℕ) :
    packRows W n QR = ∑ a ∈ range n, QR.getD a 0 * (2 ^ (W * n)) ^ a := by
  unfold packRows
  exact list_sum_range_nat _ n

/-- the `Tri` of a packed table: the `U`-scaled coefficients. -/
def Tri.ofPacked (W : ℕ) (c : ℤ) (L : ℕ) (QR : List ℕ) : Tri :=
  ⟨Uu * c, fun a => Uu * dec W L a, fun a b => Uu * tb W QR a b⟩

/-- A `Tri` whose coefficients are those of a list of triangles is `>= 0` on the cube. -/
theorem Tri.coef_ok (n : ℕ) (tr : Tri) (ts : List TriT) (hok : ∀ t ∈ ts, t.ok n = true)
    (hc : tr.cT = Uu * cS ts) (hl : ∀ a < n, tr.lT a = Uu * lS ts a)
    (hq : ∀ a < n, ∀ b < n, tr.qT a b = Uu * qS ts a b) :
    ∀ y : ℕ → ℝ, (∀ i < n, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq n tr.cT tr.lT tr.qT y := by
  intro y hy
  have h1 := evq_triS n y ts hok
  have h2 := evq_smul n Uu (cS ts) (lS ts) (qS ts) y
  have h3 : evq n tr.cT tr.lT tr.qT y
      = evq n (Uu * cS ts) (fun a => Uu * lS ts a) (fun a b => Uu * qS ts a b) y := by
    apply evq_congr
    · exact hc
    · intro a ha
      exact hl a ha
    · intro a ha b hb
      rw [hq a ha b hb, hq b hb a ha]
  rw [h3, ← h2, h1]
  have := list_sum_nonneg_of n y hy ts hok
  have hU : (0 : ℝ) ≤ (Uu : ℝ) := by
    have : (0 : ℤ) ≤ Uu := by unfold Uu; norm_num
    exact_mod_cast this
  exact mul_nonneg hU this

theorem wsum_nonneg (n : ℕ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) → 0 ≤ (ts.map (fun t => t.w)).sum
  | [], _ => by simp
  | t :: ts, h => by
      simp only [List.map_cons, List.sum_cons]
      have h1 := ok_w n t (h t (by simp))
      have h2 := wsum_nonneg n ts (fun s hs => h s (by simp [hs]))
      linarith

/-- The assembly: the kernel-checked sums give `hT` of `region_of_tabs`.  Everything but the first hypothesis
is a closed equation or inequality between integers. -/
theorem tri_hT_packed (n W : ℕ) (hW : 1 ≤ W) (cs : List (List TriT))
    (hok : cs.all (fun ch => ch.all (TriT.ok n)) = true)
    (hbd : 12 * gsum wterm cs < ((2 ^ (W - 1) : ℕ) : ℤ))
    (cF : ℤ) (hc : gsum cterm cs = cF)
    (LF : ℕ) (hl : gsum (lterm W) cs + offL W n = (LF : ℤ))
    (QR : List ℕ) (hq : gsum (qterm W n) cs + offQ W n = (packRows W n QR : ℤ))
    (hQR : (List.range n).all (fun a => decide (QR.getD a 0 < 2 ^ (W * n))) = true) :
    ∀ y : ℕ → ℝ, (∀ i < n, 0 ≤ y i ∧ y i ≤ 1) →
      0 ≤ evq n (Tri.ofPacked W cF LF QR).cT (Tri.ofPacked W cF LF QR).lT (Tri.ofPacked W cF LF QR).qT y := by
  have hok' : ∀ ch ∈ cs, ∀ t ∈ ch, t.ok n = true := by
    intro ch hch t ht
    have h1 := List.all_eq_true.mp hok ch hch
    exact List.all_eq_true.mp h1 t ht
  obtain ⟨ts, hts⟩ : ∃ ts, ts = cs.flatten := ⟨_, rfl⟩
  have hok'' : ∀ t ∈ ts, t.ok n = true := by
    intro t ht
    rw [hts] at ht
    obtain ⟨ch, hch, hmem⟩ := List.mem_flatten.mp ht
    exact hok' ch hch t hmem
  have hg : ∀ f : TriT → ℤ, gsum f cs = (ts.map f).sum := by
    intro f
    rw [gsum_eq, hts]
  have hbd' : 12 * (ts.map (fun t => t.w)).sum < ((2 ^ (W - 1) : ℕ) : ℤ) := by
    have := hg wterm
    unfold wterm at this
    rw [← this]
    exact hbd
  have hw0 := wsum_nonneg n ts hok''
  refine Tri.coef_ok n (Tri.ofPacked W cF LF QR) ts hok'' ?_ ?_ ?_
  · show Uu * cF = Uu * cS ts
    have : cS ts = gsum cterm cs := by rw [hg]; rfl
    rw [this, hc]
  · -- linear part
    have hv : ∀ a < n, -((2 ^ (W - 1) : ℕ) : ℤ) ≤ lS ts a ∧ lS ts a < ((2 ^ (W - 1) : ℕ) : ℤ) := by
      intro a _
      have := abs_lS_le n ts hok'' a
      rw [abs_le] at this
      constructor <;> linarith [this.1, this.2]
    have hP : (LF : ℤ) = ∑ a ∈ range n, (lS ts a + ((2 ^ (W - 1) : ℕ) : ℤ)) * bp W a := by
      have e1 := sum_lS W n ts hok''
      have e2 := offL_eq W n
      rw [← hl, hg, ← e1, e2]
      simp only [add_mul, Finset.sum_add_distrib]
    intro a ha
    show Uu * dec W LF a = Uu * lS ts a
    rw [dec_of_pack W hW n (lS ts) LF hv hP a ha]
  · -- quadratic part
    have hv : ∀ a < n, ∀ b < n, -((2 ^ (W - 1) : ℕ) : ℤ) ≤ qS ts a b ∧ qS ts a b < ((2 ^ (W - 1) : ℕ) : ℤ) := by
      intro a _ b _
      have := abs_qS_le n ts hok'' a b
      rw [abs_le] at this
      constructor <;> linarith [this.1, this.2]
    have hQR' : ∀ a < n, QR.getD a 0 < 2 ^ (W * n) := fun a ha =>
      of_decide_eq_true (List.all_eq_true.mp hQR a (List.mem_range.mpr ha))
    have key : ∀ a, (∑ b ∈ range n, (qS ts a b + ((2 ^ (W - 1) : ℕ) : ℤ)) * bp W b) * bp (W * n) a
        = ∑ b ∈ range n, qS ts a b * bp W (n * a + b) + offL W n * bp (W * n) a := by
      intro a
      rw [offL_eq, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [bp_add]
      ring
    have hX : ((∑ a ∈ range n, QR.getD a 0 * (2 ^ (W * n)) ^ a : ℕ) : ℤ) =
        ∑ a ∈ range n, (∑ b ∈ range n, (qS ts a b + ((2 ^ (W - 1) : ℕ) : ℤ)) * bp W b) * bp (W * n) a := by
      have e1 := sum_qS W n ts hok''
      have e3 := offQ_eq W n
      have h := hq
      rw [packRows_eq] at h
      rw [← h, hg, ← e1, e3]
      simp only [key, Finset.sum_add_distrib]
    intro a ha b hb
    show Uu * tb W QR a b = Uu * qS ts a b
    rw [tb_of_pack W n hW (qS ts) QR hv hQR' hX a ha b hb]

end Erdos1186Ex
