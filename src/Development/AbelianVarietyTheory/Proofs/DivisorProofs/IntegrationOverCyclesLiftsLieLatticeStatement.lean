import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrationOverCyclesLiftsLieLattice
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrationOverCycles_lifts_lieLattice : PLie := by
  first | exact @GlobalTheory.AnPer.pLie_holds | exact GlobalTheory.AnPer.pLie_holds | (intros; apply GlobalTheory.AnPer.pLie_holds <;> assumption)
