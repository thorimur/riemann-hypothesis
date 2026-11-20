import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.SelfDualCovolumeProof
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.TripleEighthProof

namespace Formalism.L2.Th1.H

theorem unitaryIndex : UnitaryIndex := unitary_index
theorem phiBasic : PhiBasic := cayleyPhaseBasic
theorem gaussEighth : GaussEighth := gaussSumEighthPower
theorem unitaryGauss : UnitaryGauss := UnitaryGauss_of gaussEighth
theorem detCayley : DetCayley := cayleyDet
theorem unitaryConstant : UnitaryConstant := UnitaryConstant_proof
theorem unitaryEighth : UnitaryEighth := UnitaryEighth_proof

theorem tripleFormula : TripleFormula := TripleFormula_proof
theorem psiQuadratic : PsiQuadratic := triplePhaseQuadratic
theorem tripleEighth : TripleEighth := TripleEighth_proof

end Formalism.L2.Th1.H
