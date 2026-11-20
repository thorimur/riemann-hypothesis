import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerOrderEqOne
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_order_eq_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ord (algebraMap F (v.adicCompletion F) (ϖ : F)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | exact GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one | (intros; apply GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one <;> assumption)
