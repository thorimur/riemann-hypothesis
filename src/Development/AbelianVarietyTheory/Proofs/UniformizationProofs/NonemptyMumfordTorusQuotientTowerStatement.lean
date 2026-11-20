import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_mumfordTorusQuotientTower : (AllSet fun s => Nonempty (Tower s)) := by
  first | exact @GlobalTheory.UU.TowerEx.nonempty_tower | exact GlobalTheory.UU.TowerEx.nonempty_tower | (intros; apply GlobalTheory.UU.TowerEx.nonempty_tower <;> assumption)
