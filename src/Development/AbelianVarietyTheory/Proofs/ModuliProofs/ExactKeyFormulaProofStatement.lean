import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProof
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exactKeyFormula_proof : KeyFormula := by
  first | exact @GlobalTheory.KeyFam.keyFormula_holds | exact GlobalTheory.KeyFam.keyFormula_holds | (intros; apply GlobalTheory.KeyFam.keyFormula_holds <;> assumption)
