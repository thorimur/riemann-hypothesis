import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSeminormBallFamily_sectionBalls : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ a b : ℤ, IsBallFam (P.H a b) (P.Bl a b) := by
  first | exact @GlobalTheory.VolBr.Pair.isBallFam | exact GlobalTheory.VolBr.Pair.isBallFam | (intros; apply GlobalTheory.VolBr.Pair.isBallFam <;> assumption)
