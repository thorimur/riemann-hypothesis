import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationBaseChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisation_baseChange : PolBaseChangeSt → GlobalFnsSt → SecBaseChangeSt → DVR.TwistBaseChangeStatement → UnifBaseChangeSt := by
  first | exact @GlobalTheory.unifBaseChange | exact GlobalTheory.unifBaseChange | (intros; apply GlobalTheory.unifBaseChange <;> assumption)
