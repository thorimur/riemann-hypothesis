import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SiuInequalityIntegralHolds
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siu_inequality_integral_holds : SiuZStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.siuZ | exact GlobalTheory.CompanionTheory.Ar.Giv.siuZ | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.siuZ <;> assumption)
