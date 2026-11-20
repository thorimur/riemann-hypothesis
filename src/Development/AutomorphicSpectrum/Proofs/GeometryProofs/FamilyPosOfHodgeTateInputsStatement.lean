import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPosOfHodgeTateInputs
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_pos_of_hodge_tate_inputs : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.familyExistsPos_holds | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.familyExistsPos_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.familyExistsPos_holds <;> assumption)
