import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.InvInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq

namespace PI

theorem weil_quotient_measure : PI.WeilQuotMeas.WeilQuotient :=
  PI.WeilQuotMeas.UnitaryGroupMassFormula.weilQuotient_of_parts PI.WeilQuotMeas.UnitaryGroupMassFormula.stepBruhat
    PI.WeilQuotMeas.UnitaryGroupMassFormula.stepInvInv PI.wqUnique

end PI
