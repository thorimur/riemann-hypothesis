import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstK
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionOfFunctorialityAdoptedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsCuspidalOfFunctorialityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipOfWeilConvergenceAndThetaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetsOfOrthogonalSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearIndependenceOfCuspidalLiftsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRationalSumsOfFiniteSumsMeaningfulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingOfCuspidalLiftsStatement

namespace GlobalTheory.RowClaim.Join

theorem fiveClaims : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  intro P K L s1 s2 s3
  have c := GlobalTheory.ConstNZ.constK P K L s1 s2 s3
  have cusp := GlobalTheory.T.lifts_cuspidal_of_functoriality P
  have sum := GlobalTheory.T.row_sum_of_published_inputs P
  exact ⟨sum, c, GlobalTheory.T.linear_independence_of_cuspidal_lifts P cusp,
    GlobalTheory.T.rowTestLiftFormula_principalLevel (GlobalTheory.T.projection_of_functoriality_adopted P) (GlobalTheory.T.flip_of_weil_convergence_and_theta P cusp s1 K c) (GlobalTheory.T.unfolding_of_cuspidal_lifts P cusp sum)
      (GlobalTheory.T.jets_of_orthogonal_sum P sum) c sum,
    GlobalTheory.T.rowTestRationalSums_of_finiteSumsMeaningful sum⟩

end GlobalTheory.RowClaim.Join
