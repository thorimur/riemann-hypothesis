import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguezStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSetStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingOfHoweDualityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingAssemblyStatement

namespace GlobalTheory.RowClaim.JoinF

theorem claims :
    GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK :=
  fun hP hK hM =>
    GlobalTheory.T.local_matching_assembly hP hK hM (GlobalTheory.T.weil_convergence_of_siegel_set hP.siegelSetUnitary hP)
      (GlobalTheory.T.local_matching_of_howe_duality hP.howeDualityReal hP hK hM) (GlobalTheory.T.theta_integrals_of_minguez hP.minguezThetaGL hP hK hM)

end GlobalTheory.RowClaim.JoinF
