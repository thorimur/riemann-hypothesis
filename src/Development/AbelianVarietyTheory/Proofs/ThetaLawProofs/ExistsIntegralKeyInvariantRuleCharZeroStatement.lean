import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIntegralKeyInvariantRuleCharZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralKeyInvariantRule_charZero : Out.Laws → ThetaUnifAV → GlobalTheory.TorusAlgebraic → KeyDesc → KaSt := by
  first | exact @GlobalTheory.KaExists.kaSt | exact GlobalTheory.KaExists.kaSt | (intros; apply GlobalTheory.KaExists.kaSt <;> assumption)
