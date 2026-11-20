import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfHodgeDeRham
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeSquareZeroLifts_of_hodgeDeRham : CrystallineSmoothLift → AbelianHodgeDeRham → AbelianSchemeLifts := by
  first | exact @GlobalTheory.LiftSys.abelianSchemeLifts_of_hodgeDeRham | exact GlobalTheory.LiftSys.abelianSchemeLifts_of_hodgeDeRham | (intros; apply GlobalTheory.LiftSys.abelianSchemeLifts_of_hodgeDeRham <;> assumption)
