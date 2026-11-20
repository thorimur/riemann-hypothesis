import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_codim_one_stalk_dvr : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one | exact GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one | (intros; apply GlobalTheory.CompanionTheory.Ar.stalk_isDiscreteValuationRing_of_dim_one <;> assumption)
