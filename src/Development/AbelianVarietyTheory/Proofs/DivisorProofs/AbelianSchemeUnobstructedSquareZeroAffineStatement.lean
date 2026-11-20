import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffine
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine : GlobalTheory.Published.AbelianUnobstructed := by
  first | exact @GlobalTheory.UnobTop.abelianUnobstructed | exact GlobalTheory.UnobTop.abelianUnobstructed | (intros; apply GlobalTheory.UnobTop.abelianUnobstructed <;> assumption)
