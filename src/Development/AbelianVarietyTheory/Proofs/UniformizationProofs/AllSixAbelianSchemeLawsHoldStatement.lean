import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.all_six_abelian_scheme_laws_hold : Laws ∧ Laws2 ∧ Laws3 ∧ Laws4 ∧ Laws5 ∧ Laws6 := by
  first | exact @GlobalTheory.allSixLaws | exact GlobalTheory.allSixLaws | (intros; apply GlobalTheory.allSixLaws <;> assumption)
