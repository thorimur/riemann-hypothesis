import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AverageEmbeddingsFieldExtension
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_embeddings_field_extension : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (f : (K →+* ℂ) → ℝ), (∑ σ : K' →+* ℂ, f (σ.comp (algebraMap K K'))) / (Module.finrank ℚ K' : ℝ) = (∑ σ : K →+* ℂ, f σ) / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.mean_embeddings_comp_restrict | exact GlobalTheory.mean_embeddings_comp_restrict | (intros; apply GlobalTheory.mean_embeddings_comp_restrict <;> assumption)
