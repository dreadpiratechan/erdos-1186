import Erdos.Proofs.P1186ExBathChk

/-!
# Erdos 1186 - bathtub certificate check on G24 cells 0 to 26 (kernel evaluation)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's.  `chkRange` (`P1186ExBathChk`) re-checks every inequality the soundness proof `P1186ExBathCell.cell_sound`
uses, on cells `0, …, 26 - 1` of `G24`, by `decide +kernel` (no `native_decide`).
-/

namespace Erdos1186Ex

theorem chk24a : chkRange G24 nuTab24 tTab24 0 26 = true := by decide +kernel

end Erdos1186Ex
