import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.KeySmall
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.NumericMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Skeleton

namespace GlobalTheory

theorem transferenceCover_holds : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall

end GlobalTheory
