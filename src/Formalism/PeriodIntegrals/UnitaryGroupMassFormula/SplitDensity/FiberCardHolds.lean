import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.CardFibreCompl
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.FiberCard

namespace PI.DensSplitW

theorem fiberCard_holds : FiberCard := by
  intro K V U _ _ _ _ _ _ _ φ hφ k g
  exact FibreCount.fiber_card φ hφ g

end PI.DensSplitW
