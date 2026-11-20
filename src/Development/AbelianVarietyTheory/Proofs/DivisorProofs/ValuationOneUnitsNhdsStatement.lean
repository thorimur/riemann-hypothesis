import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationOneUnitsNhds
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_one_units_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    {x : kˣ | ValuativeRel.valuation k (x : k) = 1} ∈ 𝓝 (1 : kˣ) := by
  first | exact @GlobalTheory.units_valuation_eq_one_mem_nhds_one | exact GlobalTheory.units_valuation_eq_one_mem_nhds_one | (intros; apply GlobalTheory.units_valuation_eq_one_mem_nhds_one <;> assumption)
