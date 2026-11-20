import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenEmbeddingFiniteAdeleOfSPartAndIntegralPart
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenEmbedding_finiteAdeleOfSPartAndIntegralPart : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), IsOpenEmbedding (jS F S) := by
  first | exact @GlobalTheory.ModuLR.isOpenEmbedding_jS | exact GlobalTheory.ModuLR.isOpenEmbedding_jS | (intros; apply GlobalTheory.ModuLR.isOpenEmbedding_jS <;> assumption)
