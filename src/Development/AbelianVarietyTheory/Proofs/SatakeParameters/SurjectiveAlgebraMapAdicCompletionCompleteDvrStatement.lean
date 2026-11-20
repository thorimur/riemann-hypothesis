import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SurjectiveAlgebraMapAdicCompletionCompleteDvr
open NumberField IsDedekindDomain WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_algebraMap_adicCompletion_complete_dvr : ∀ {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (π : W) (hπ : Irreducible π) (hc : IsAdicComplete (Ideal.span {π}) W) (v : HeightOneSpectrum W), Function.Surjective (algebraMap Qq (v.adicCompletion Qq)) := by
  first | exact @GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion | exact GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion | (intros; apply GlobalTheory.DenseCompl.surjective_algebraMap_adicCompletion <;> assumption)
