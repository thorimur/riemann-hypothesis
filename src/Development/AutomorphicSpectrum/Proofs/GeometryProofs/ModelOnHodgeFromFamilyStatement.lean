import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOnHodgeFromFamily
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_on_hodge_from_family : GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos → HodgeLatticeFlagBound := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos <;> assumption)
