import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_degenerationData_unique : GlobalFnsSt → SecBaseChangeSt → AmpleSt → UnifUniqSt := by
  first | exact @GlobalTheory.unifUniq | exact GlobalTheory.unifUniq | (intros; apply GlobalTheory.unifUniq <;> assumption)
