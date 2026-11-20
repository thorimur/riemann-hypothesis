import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPrincipalPolarisation_sections_baseChange : DVR.TwistBaseChangeStatement := by
  first | exact @GlobalTheory.twistBaseChange | exact GlobalTheory.twistBaseChange | (intros; apply GlobalTheory.twistBaseChange <;> assumption)
