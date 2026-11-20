import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsoOfThickenings
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_of_thickenings : IsoOfThick := by
  first | exact @GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick | exact GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick | (intros; apply GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick <;> assumption)
