import Development.AutomorphicSpectrum.Proofs.MetricProofs.GrassmannHeightZ2OfInputsAndZ2Statement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackInputsOfStatementsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem grassmann_height_Z2_of_systems :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
        GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement := by
  intro hSys hHS hBig hResK
  exact GlobalTheory.T.grassmann_height_Z2_of_inputs_and_Z2 (GlobalTheory.T.pullback_inputs_of_statements hSys hHS hBig hResK) hSys
    (hsLinks_of_moriwaki hHS hBig).2.2.1

end GlobalTheory.CompanionTheory.Ar.Giv
