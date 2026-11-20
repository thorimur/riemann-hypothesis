import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.AgreeOnH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.LineReduce

noncomputable section

namespace PI.UnitaryGroupMassFormula.BetaLUniq

theorem betaLUniq_of_aniso_eigen (h3 : WAniso) (h5 : EigenvalueLastLineOne) : PI.BetaLUniq :=
  betaLUniq_of'' gram_matrix_nondegenerate agreeOnH h3 h5

end PI.UnitaryGroupMassFormula.BetaLUniq
