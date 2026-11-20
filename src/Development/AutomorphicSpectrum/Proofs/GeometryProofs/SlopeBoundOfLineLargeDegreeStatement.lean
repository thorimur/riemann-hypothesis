import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLineLargeDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_bound_of_line_large_degree : LineOfLargeDegree.Statement → SlopeBoundSt ∧ Prov.LemmaS := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel | exact GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel <;> assumption)
