import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsLeftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticProvisionHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeIndexOfIntersectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NineFreeOfIntersectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelClauseHolds
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NumericalSegreClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem given_of_moriwaki :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → Top.Given := by
  intro hAI hHS hBig hRes hSA hHT hGaga hLine
  exact GlobalTheory.T.final_theorem_of_inputs_left GlobalTheory.CompanionTheory.Ar.Top.modelClause_holds GlobalTheory.KeyFam.keyFormula_holds hSA
    GlobalTheory.CompanionTheory.Segre.numericalSegre_closed hRes hHT hGaga hLine
    (GlobalTheory.T.pullback_inputs_of_statements hAI hHS hBig hRes) (GlobalTheory.T.hodge_index_of_intersection hAI hHS hBig hRes) GlobalTheory.T.analytic_provision_holds
    (GlobalTheory.T.nine_free_of_intersection hAI hHS hBig hRes)

end GlobalTheory.CompanionTheory.Ar.Link
