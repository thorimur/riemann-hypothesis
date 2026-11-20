import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliZ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.IoPolDiagHw
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem capelli_scalar_identity : CapelliZ :=
  capelliZ_of fun h lam mu φ hφ s hs u => capScalar highest_weight_irreducible h lam mu φ hφ s hs u

end PI.WGL
