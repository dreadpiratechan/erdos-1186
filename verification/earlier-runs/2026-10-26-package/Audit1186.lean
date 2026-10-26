import Erdos.Proofs.P1186M2Main

/-!
# Audit file for the manuscript on Erdos Problem 1186

Run from the `lean/` directory of the research repository (module list and build commands: `../README.md`):

    lake env lean <path to this file>

It prints the statement of each theorem the paper cites and the axioms it depends on.  A theorem counts as proved in the
paper's sense only if the printed axioms are a subset of `propext`, `Classical.choice`, `Quot.sound`.
(`sorryAx` or `Lean.ofReduceBool` in a list would mean `sorry` or `native_decide` in the closure.)
-/

open Erdos1186Day

-- the definitions as shipped (verbatim copies of upstream formal-conjectures c83a94d, namespace renamed)
#print monoCount
#print minMonoCount
#print δ

-- Theorem A (Parrilo-Robertson-Saracino bounds; the upstream statement `prs_bounds`)
#check @erdos_1186.variants.prs_bounds
#print axioms erdos_1186.variants.prs_bounds
#print axioms erdos_1186.variants.prs_bounds_lower
#print axioms erdos_1186.variants.prs_bounds_upper
#check @delta3_ge_L256
#print axioms delta3_ge_L256

-- the two further upstream `research solved` variants proved in the same file (not claimed as results of the paper)
#check @erdos_1186.variants.van_der_waerden
#print axioms erdos_1186.variants.van_der_waerden
#check @erdos_1186.variants.probabilistic
#print axioms erdos_1186.variants.probabilistic

-- Theorem B (MODEL2 cover, Shor + triangle cuts)
#check @delta3_ge_model2_L64
#check @delta3_ge_model2_L128
#check @delta3_ge_model2_L256
#check @delta3_bounds_model2_L256
#print axioms delta3_ge_model2_L64
#print axioms delta3_ge_model2_L128
#print axioms delta3_ge_model2_L256
#print axioms delta3_bounds_model2_L256

-- the generic reductions and the three certificate theorems
#check @Erdos1186Night2.lower_of_cert
#print axioms Erdos1186Night2.lower_of_cert
#check @Erdos1186Night2M2.lower_of_cubeLB
#print axioms Erdos1186Night2M2.lower_of_cubeLB
#check @Erdos1186Night2M2.cubeLB64
#check @Erdos1186Night2M2.cubeLB128
#check @Erdos1186Night2M2.cubeLB256
#print axioms Erdos1186Night2M2.cubeLB64
#print axioms Erdos1186Night2M2.cubeLB128
#print axioms Erdos1186Night2M2.cubeLB256
#print axioms Erdos1186Night2M2.cubeLB_of_cert
#print axioms Erdos1186Night2M2.Cert.link_sound
#print axioms Erdos1186Night2M2.Cert.psd

-- the two diagonal-certificate instances of the strip cover (used by Theorem A and delta3_ge_L256)
#print axioms Erdos1186Night2.cert128
#print axioms Erdos1186Night2.cert256
