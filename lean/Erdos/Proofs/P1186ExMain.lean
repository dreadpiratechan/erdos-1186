import Erdos.Proofs.P1186ExGlue
import Erdos.Proofs.P1186ExStar
import Erdos.Proofs.P1186ExBath
import Erdos.Proofs.P1186ExPair

/-!
# Erdos 1186 - the claimed proof of `δ 3 = 117/2192`, assembled (coordinator, 2026-10-26)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's. Lanes over the shared interface `P1186Ex.lean` (plan: `problems/1186/exact/PLAN.md`):
- exstar `starOK` (`P1186ExStar.lean`), exbath `bathOK24`, `bathOK8` (`P1186ExBath*.lean`), expair `pairOK24`, `pairOK8`
  (`P1186ExPair.lean`), exglue `delta3_eq_of_parts` (`P1186ExGlue.lean`).
- The five finite certificates `RegionLB` (lane excert) are the only hypotheses left in `delta3_eq_of_regions`.

`δ` is the verbatim upstream definition (formal-conjectures c83a94d) copied in `P1186.lean`.
-/

namespace Erdos1186Ex

/-- `δ 3 = 117/2192`, given the claim's five finite certificates (everything else is proved). -/
theorem delta3_eq_of_regions
    (r1 : RegionLB G24 0 (1 / 5)) (r2 : RegionLB G24 (1 / 5) (3 / 10)) (r3 : RegionLB G24 (3 / 10) (2 / 5))
    (r4 : RegionLB G8 (2 / 5) (9 / 20)) (r5 : RegionLB G8 (9 / 20) (1 / 2)) :
    Erdos1186Day.δ 3 = 117 / 2192 :=
  delta3_eq_of_parts starOK bathOK24 bathOK8 pairOK24 pairOK8 r1 r2 r3 r4 r5

end Erdos1186Ex
