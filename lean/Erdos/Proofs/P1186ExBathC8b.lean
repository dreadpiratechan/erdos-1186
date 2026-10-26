import Erdos.Proofs.P1186ExBathChk

/-!
# Erdos 1186 - bathtub certificate check on G8 cells 37 to 74 (kernel evaluation)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's.  `chkRange` (`P1186ExBathChk`) re-checks every inequality the soundness proof `P1186ExBathCell.cell_sound`
uses, on cells `37, …, 74 - 1` of `G8`, by `decide +kernel` (no `native_decide`).
-/

namespace Erdos1186Ex

theorem chk8b : chkRange G8 nuTab8 tTab8 37 74 = true := by decide +kernel

end Erdos1186Ex
