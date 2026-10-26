import Erdos.Proofs.P1186ExFinal

/-!
# Audit file for Section 10 (the claimed proof of `δ 3 = 117/2192`) of the manuscript on Erdos Problem 1186

Run from the `lean/` directory of the standalone project (see `../README.md`, section 7):

    lake env lean AuditClaim1186.lean

The Lean files audited here formalise the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed);
the mathematics is its author's.  They were written by AI agents of the research project, not by the author of the
manuscript; their source is the branch `agent/n3c` of the research repository (commit f726409).

It prints the statement of each theorem of the chain and the axioms it depends on.  A theorem counts as proved in the
manuscript's sense only if the printed axioms are a subset of `propext`, `Classical.choice`, `Quot.sound`
(`sorryAx` or `Lean.ofReduceBool` in a list would mean `sorry` or `native_decide` in the closure).
-/

-- the definitions (shared with Audit1186.lean: verbatim copies of upstream formal-conjectures c83a94d, namespace renamed)
#print Erdos1186Day.monoCount
#print Erdos1186Day.minMonoCount
#print Erdos1186Day.δ

-- the final statement: the upstream statement `erdos_1186.variants.prs_conjecture`, no hypotheses
#check @Erdos1186Day.erdos_1186.variants.prs_conjecture
set_option pp.fullNames true in
set_option pp.numericTypes true in
#check @Erdos1186Day.erdos_1186.variants.prs_conjecture
#print axioms Erdos1186Day.erdos_1186.variants.prs_conjecture

-- the conditional theorem it is built from (five hypotheses `RegionLB`) and the assembly
#check @Erdos1186Ex.delta3_eq_of_regions
#print axioms Erdos1186Ex.delta3_eq_of_regions
#print axioms Erdos1186Ex.delta3_eq_of_parts
#print axioms Erdos1186Ex.lower_of_parts

-- the parts
#check @Erdos1186Ex.starOK
#print axioms Erdos1186Ex.starOK
#check @Erdos1186Ex.bathOK24
#check @Erdos1186Ex.bathOK8
#print axioms Erdos1186Ex.bathOK24
#print axioms Erdos1186Ex.bathOK8
#check @Erdos1186Ex.pairOK24
#check @Erdos1186Ex.pairOK8
#print axioms Erdos1186Ex.pairOK_of_WF
#print axioms Erdos1186Ex.pairOK24
#print axioms Erdos1186Ex.pairOK8

-- the five finite certificates
#check @Erdos1186Ex.region1
#check @Erdos1186Ex.region2
#check @Erdos1186Ex.region3
#check @Erdos1186Ex.region4
#check @Erdos1186Ex.region5
#print axioms Erdos1186Ex.region1
#print axioms Erdos1186Ex.region2
#print axioms Erdos1186Ex.region3
#print axioms Erdos1186Ex.region4
#print axioms Erdos1186Ex.region5
