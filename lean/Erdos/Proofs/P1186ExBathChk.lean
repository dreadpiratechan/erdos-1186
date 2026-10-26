import Mathlib
import Erdos.Proofs.P1186ExBathH2
import Erdos.Proofs.P1186ExData
import Erdos.Proofs.P1186ExBathTab

/-!
# Erdos 1186 - the computable per-cell certificate check for the bathtub inequality (definitions only)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's.  For a grid cell `i` (unit cells `p' ∈ [lo, hi)`), `cellChk` verifies, from the explicit profile tables
`alphaF`, `betaF` and the certificate values `ν = nuT i`, `T = tT i`:

* `a_i · 1096 · 2192 ≤ L ν` and `b_i · 4 · 1096² · T ≤ 6 L²` (`L` the number of unit cells);
* every unit cell has `ν ≤ min(α, α+β)`, `β ≠ 0`, `|β| ∣ 6`, and rises at most `3 L` above `ν`;
* the level-count slope sum `Σ_p [e_p ≤ c < e_p + s_p] · (6 / s_p)` is `≤ T` for the levels `c < 3 L`.

`P1186ExBathCell` proves that `cellChk = true` gives the bathtub bound for that cell; the chunk modules evaluate
`cellChk` on all cells of `G24` and `G8` by `decide +kernel`.
-/

namespace Erdos1186Ex

/-- the least value of the profile on unit cell `p'`: `min (α, α+β)` (the profile is `α + β θ`, `θ ∈ [0,1]`). -/
def dd (p' : ℕ) : ℤ := if alphaF p' ≤ alphaF p' + betaF p' then alphaF p' else alphaF p' + betaF p'
/-- the absolute slope `|β|` of unit cell `p'`. -/
def ss (p' : ℕ) : ℕ := (betaF p').natAbs

/-- the pieces `(e, s)` of the cells `lo, lo+1, …, lo+n-1`: offset of the least value above `ν`, and `|β|`. -/
def pcsL (ν : ℤ) (lo : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | n + 1 => ((dd lo - ν).toNat, ss lo) :: pcsL ν (lo + 1) n

/-- six times the slope of the level-count function at level `c`. -/
def S6 (l : List (ℕ × ℕ)) (c : ℕ) : ℕ :=
  (l.map (fun q => bif Nat.ble q.1 c && Nat.blt c (q.1 + q.2) then 6 / q.2 else 0)).sum

/-- `P 0 && … && P (n-1)` -/
def allBelow (P : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allBelow P n && P n

/-- the certificate check for cell `i` of `G` with tables `nuT`, `tT`. -/
def cellChk (G : Grid) (nuT : List ℤ) (tT : List ℕ) (i : ℕ) : Bool :=
  decide (0 < G.len i) && decide (G.hi i ≤ 1096) && decide (0 < tT.getD i 0) &&
  decide (G.ai i * (1096 * 2192) ≤ ((G.len i : ℕ) : ℚ) * (nuT.getD i 0)) &&
  decide (G.bi i * (4 * 1096 ^ 2) * ((tT.getD i 0 : ℕ) : ℚ) ≤ 6 * ((G.len i : ℕ) : ℚ) ^ 2) &&
  (List.range' (G.lo i) (G.len i)).all
    (fun p' => decide (nuT.getD i 0 ≤ dd p') && decide (0 < ss p') && (6 % ss p' == 0) &&
      Nat.ble ((dd p' - nuT.getD i 0).toNat + ss p') (3 * G.len i)) &&
  allBelow (fun c => Nat.ble (S6 (pcsL (nuT.getD i 0) (G.lo i) (G.len i)) c) (tT.getD i 0)) (3 * G.len i)

/-- `cellChk` on the cells `a, …, b-1`. -/
def chkRange (G : Grid) (nuT : List ℤ) (tT : List ℕ) (a b : ℕ) : Bool :=
  (List.range' a (b - a)).all (cellChk G nuT tT)

end Erdos1186Ex
