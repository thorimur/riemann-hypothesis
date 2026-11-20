import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelOfPrincipalisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelNefOfAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPullOfPrincipalisation

namespace GlobalTheory

theorem arithHilbertSamuel_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArithHilbertSamuel :=
  fun h => GlobalTheory.T.arithHilbertSamuel_nef_of_ample (GlobalTheory.MixHt.arCalc_of_principalisation h) (GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation h)
    (GlobalTheory.SemiPullAll.semiPull_of_principalisation h)

end GlobalTheory
