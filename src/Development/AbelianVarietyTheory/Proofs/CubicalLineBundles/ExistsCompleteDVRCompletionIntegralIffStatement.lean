import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_completion_integral_iff : ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)), ∃ (T : CDVR) (iK : K →+* T.Fr), T.FinRes ∧ ∀ y : K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation K y ≤ 1 := by
  first | exact @GlobalTheory.exists_cdvr_completion_integral_iff | exact GlobalTheory.exists_cdvr_completion_integral_iff | (intros; apply GlobalTheory.exists_cdvr_completion_integral_iff <;> assumption)
