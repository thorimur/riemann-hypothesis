import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivFlagOnHodgeOfFargues
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triv_flag_on_hodge_of_fargues : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → TrivFlagOnHodge := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.trivFlagOnHodge_of_fargues | exact GlobalTheory.CompanionTheory.Ar.Num.trivFlagOnHodge_of_fargues | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.trivFlagOnHodge_of_fargues <;> assumption)
