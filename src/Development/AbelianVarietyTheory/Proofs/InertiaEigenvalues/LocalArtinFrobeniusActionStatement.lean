import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinFrobeniusAction
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_artin_frobenius_action : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι →
    ∀ (σ : Weil h) (τ : GalLoc w), Lifts ι τ (σ : G E Ω) →
    ∀ (z : Kbar w) (hz : z ∈ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
      τ ((localArtinMap (w.adicCompletion E) (Kbar w) (a σ) ⟨z, hz⟩ : maximalAbelianExtension (w.adicCompletion E) (Kbar w)) : Kbar w) = z := by
  first | exact @GlobalTheory.ArtinCompareApply.lift_localArtinMap_apply | exact GlobalTheory.ArtinCompareApply.lift_localArtinMap_apply | (intros; apply GlobalTheory.ArtinCompareApply.lift_localArtinMap_apply <;> assumption)
