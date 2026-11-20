import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIwasawaDecompositionUpperUnitriangularInte
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iwasawa_decomposition_upperUnitriangular_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (g : GL (Fin m) k), ∃ u ∈ unipB k (Fin m), ∃ t : Fin m → kˣ, ∃ κ ∈ KO k (Fin m), g = u * diagT k (Fin m) t * κ := by
  first | exact @GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO | exact GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO | (intros; apply GlobalTheory.SmGL.exists_unipB_mul_diagT_mul_KO <;> assumption)
