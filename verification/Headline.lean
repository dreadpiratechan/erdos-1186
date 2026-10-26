import Erdos1186

/-!
Prints the definitions and the exact statements of every theorem the paper relies on, the definitions of the five
target propositions of Theorem C, and the axioms each theorem depends on.
A theorem counts as proved only if its axioms are among `propext`, `Classical.choice`, `Quot.sound`
(`sorryAx` would mean `sorry`, `Lean.ofReduceBool` would mean `native_decide`).
Run from `lean/`:  lake env lean ../verification/Headline.lean
-/

-- The problem: definitions copied verbatim from Formal Conjectures (checked by rfl in UpstreamPin.lean).
#print Erdos1186Day.monoCount
#print Erdos1186Day.minMonoCount
#print Erdos1186Day.δ

-- Theorem A (the bounds of Parrilo, Robertson and Saracino; the upstream statement `prs_bounds`).
#check @Erdos1186Day.erdos_1186.variants.prs_bounds
#check @Erdos1186Day.erdos_1186.variants.prs_bounds_lower
#check @Erdos1186Day.erdos_1186.variants.prs_bounds_upper
#check @Erdos1186Day.delta3_ge_L256

-- Two further upstream `research solved` variants proved in the same development (not results of the paper).
#check @Erdos1186Day.erdos_1186.variants.van_der_waerden
#check @Erdos1186Day.erdos_1186.variants.probabilistic

-- Theorem B (the sharper cover, Shor relaxation with triangle cuts, kernel-checked integer certificates).
#check @Erdos1186Day.delta3_ge_model2_L64
#check @Erdos1186Day.delta3_ge_model2_L128
#check @Erdos1186Day.delta3_ge_model2_L256
#check @Erdos1186Day.delta3_bounds_model2_L128
#check @Erdos1186Day.delta3_bounds_model2_L256

-- The generic reductions behind Theorems A and B, and their certificate instances.
#print Erdos1186Night2.DiagCert
#check @Erdos1186Night2.lower_of_cert
#check @Erdos1186Night2.cert128
#check @Erdos1186Night2.cert256
#print Erdos1186Night2M2.CubeLB
#check @Erdos1186Night2M2.lower_of_cubeLB
#check @Erdos1186Night2M2.cubeLB_of_cert
#check @Erdos1186Night2M2.Cert.link_sound
#check @Erdos1186Night2M2.Cert.psd
#check @Erdos1186Night2M2.cubeLB64
#check @Erdos1186Night2M2.cubeLB128
#check @Erdos1186Night2M2.cubeLB256

-- Theorem C (the Lean formalisation of another author's unrefereed proof claim; the mathematics is theirs).
#check @Erdos1186Day.erdos_1186.variants.prs_conjecture
set_option pp.fullNames true in
set_option pp.numericTypes true in
#check @Erdos1186Day.erdos_1186.variants.prs_conjecture

-- The interface of Theorem C: the five target propositions and the finite lower bound `Lval`.
#print Erdos1186Ex.StarOK
#print Erdos1186Ex.BathOK
#print Erdos1186Ex.PairOK
#print Erdos1186Ex.RegionLB
#print Erdos1186Ex.Grid.Lval
#print Erdos1186Ex.Grid.pterm
#print Erdos1186Ex.Grid.mval

-- The conditional theorems and the parts of Theorem C.
#check @Erdos1186Ex.delta3_eq_of_regions
#check @Erdos1186Ex.delta3_eq_of_parts
#check @Erdos1186Ex.lower_of_parts
#check @Erdos1186Ex.starOK
#check @Erdos1186Ex.bathOK24
#check @Erdos1186Ex.bathOK8
#check @Erdos1186Ex.pairOK_of_WF
#check @Erdos1186Ex.pairOK24
#check @Erdos1186Ex.pairOK8
#check @Erdos1186Ex.region1
#check @Erdos1186Ex.region2
#check @Erdos1186Ex.region3
#check @Erdos1186Ex.region4
#check @Erdos1186Ex.region5

-- Axioms.
#print axioms Erdos1186Day.erdos_1186.variants.prs_bounds
#print axioms Erdos1186Day.erdos_1186.variants.prs_bounds_lower
#print axioms Erdos1186Day.erdos_1186.variants.prs_bounds_upper
#print axioms Erdos1186Day.delta3_ge_L256
#print axioms Erdos1186Day.erdos_1186.variants.van_der_waerden
#print axioms Erdos1186Day.erdos_1186.variants.probabilistic
#print axioms Erdos1186Day.delta3_ge_model2_L64
#print axioms Erdos1186Day.delta3_ge_model2_L128
#print axioms Erdos1186Day.delta3_ge_model2_L256
#print axioms Erdos1186Day.delta3_bounds_model2_L128
#print axioms Erdos1186Day.delta3_bounds_model2_L256
#print axioms Erdos1186Night2.lower_of_cert
#print axioms Erdos1186Night2.cert128
#print axioms Erdos1186Night2.cert256
#print axioms Erdos1186Night2M2.lower_of_cubeLB
#print axioms Erdos1186Night2M2.cubeLB_of_cert
#print axioms Erdos1186Night2M2.Cert.link_sound
#print axioms Erdos1186Night2M2.Cert.psd
#print axioms Erdos1186Night2M2.cubeLB64
#print axioms Erdos1186Night2M2.cubeLB128
#print axioms Erdos1186Night2M2.cubeLB256
#print axioms Erdos1186Day.erdos_1186.variants.prs_conjecture
#print axioms Erdos1186Ex.delta3_eq_of_regions
#print axioms Erdos1186Ex.delta3_eq_of_parts
#print axioms Erdos1186Ex.lower_of_parts
#print axioms Erdos1186Ex.starOK
#print axioms Erdos1186Ex.bathOK24
#print axioms Erdos1186Ex.bathOK8
#print axioms Erdos1186Ex.pairOK_of_WF
#print axioms Erdos1186Ex.pairOK24
#print axioms Erdos1186Ex.pairOK8
#print axioms Erdos1186Ex.region1
#print axioms Erdos1186Ex.region2
#print axioms Erdos1186Ex.region3
#print axioms Erdos1186Ex.region4
#print axioms Erdos1186Ex.region5
