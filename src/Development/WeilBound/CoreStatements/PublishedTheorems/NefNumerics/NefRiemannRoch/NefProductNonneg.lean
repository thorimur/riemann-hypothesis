import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegAllDimsStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem nefProductNonneg : GlobalTheory.Published.NefProductNonneg := by
  intro k _ _ X _ d hp hd N hN
  exact GlobalTheory.T.nef_intersection_nonneg_all_dims k X hp d (structureModule X) (by rw [suppDim_structureModule, hd]) N hN

end GlobalTheory
