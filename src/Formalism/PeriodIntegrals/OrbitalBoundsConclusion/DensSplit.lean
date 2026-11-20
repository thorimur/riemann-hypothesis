import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.FiberCardHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.PhiXFinrankRange

theorem bilinearDensityFormula : Formalism.L2.SG.DensExact.DensExactSplit :=
  PI.DensSplitW.densExactSplit_of PI.DensSplitW.fiberCard_holds
