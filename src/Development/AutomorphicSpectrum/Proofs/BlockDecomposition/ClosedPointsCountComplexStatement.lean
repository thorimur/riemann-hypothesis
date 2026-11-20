import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedPointsCountComplex
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_points_count_complex : ∀ (Y : Var ℂ) (Z : Set Y.X), (∀ x ∈ Z, IsClosed ({x} : Set Y.X)) → ({y : CxPts Y.str (RingHom.id ℂ) | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z}).ncard = Z.ncard := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed | exact GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed <;> assumption)
