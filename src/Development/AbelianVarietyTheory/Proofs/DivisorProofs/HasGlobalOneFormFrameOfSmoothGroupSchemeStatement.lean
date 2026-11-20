import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGlobalOneFormFrameOfSmoothGroupScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGlobalOneFormFrame_of_smooth_groupScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], Smooth A.hom → HasFrame (OAff A.hom) := by
  first | exact @GlobalTheory.AbCoh.hasFrame_of_smooth_grpObj | exact GlobalTheory.AbCoh.hasFrame_of_smooth_grpObj | (intros; apply GlobalTheory.AbCoh.hasFrame_of_smooth_grpObj <;> assumption)
