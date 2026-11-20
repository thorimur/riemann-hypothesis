import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TwoLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_on_regular_flagged : GlobalTheory.CovTop.Hypotheses2 → VanishOn RegFlagged := by
  first | exact @GlobalTheory.TwoLat.vanishOn_regFlagged | exact GlobalTheory.TwoLat.vanishOn_regFlagged | (intros; apply GlobalTheory.TwoLat.vanishOn_regFlagged <;> assumption)
