import Mathlib
import Erdos.Proofs.P1186Ex

/-!
Fidelity check of the Python model `sdpmodel.py` against the Lean DEFINITIONS (lane excertsdp; no theorem is proved here).

`Grid.N/lo/hi/len/wt/ai/bi/sgn/A4` are the REAL (computable) definitions of `P1186Ex.lean`, `K4`/`c1`/`sg` are the real ones
too (nothing is copied).  Only `pterm`, `Lval`, `mval` are `noncomputable` over `ℝ` there, so they are copied below with `ℝ`
replaced by `ℚ` (same formulas, line by line) to let `#eval` run them.  `fidelity_check.py` compares the printed values with
`sdpmodel.py` (exact rational arithmetic).
-/

namespace Fid

open Finset Erdos1186Ex

def pterm (G : Grid) (i j : ℕ) (yi yj : ℚ) : ℚ :=
  let P : ℚ := (G.wt i : ℚ) * G.wt j * yi * yj
  let Ain : ℚ := (G.A4 i j : ℚ) / (4 * 1096 ^ 2)
  let Aout : ℚ := (G.wt i : ℚ) * G.wt j - Ain
  if G.sgn i * G.sgn j = 1 then max 0 (P - Aout) else max (-Ain) (-P)

def Lval (G : Grid) (y : ℕ → ℚ) : ℚ :=
  ∑ i ∈ range G.N, ((G.ai i : ℚ) * y i + (G.bi i : ℚ) * y i ^ 2)
    + ∑ i ∈ range G.N, ∑ j ∈ range G.N, pterm G i j (y i) (y j)

def mval (G : Grid) (y : ℕ → ℚ) : ℚ := ∑ i ∈ range G.N, (G.wt i : ℚ) * y i

/-- test points used by `fidelity_check.py` -/
def ytest : ℕ → ℕ → ℚ
  | 0, i => (((i * 7 + 3) % 13 : ℕ) : ℚ) / 13
  | 1, i => (((i * 5 + 1) % 17 : ℕ) : ℚ) / 16
  | 2, i => if i % 2 = 0 then 1 else 0
  | 3, _ => 1
  | 4, i => (((i * 11 + 4) % 7 : ℕ) : ℚ) / 6
  | _, _ => 0

#eval (Grid.N G24, Grid.N G8)
#eval (G24.A4 5 7, G24.A4 0 0, G24.A4 60 70, G8.A4 10 20, G8.A4 100 3, G8.A4 145 145)
#eval (G24.sgn 0, G24.sgn 60, G24.sgn 129, G8.sgn 3, G8.sgn 100)
#eval ((List.range 6).map fun k => mval G24 (ytest k), (List.range 6).map fun k => mval G8 (ytest k))
#eval ((List.range 6).map fun k => Lval G24 (ytest k), (List.range 6).map fun k => Lval G8 (ytest k))

end Fid
