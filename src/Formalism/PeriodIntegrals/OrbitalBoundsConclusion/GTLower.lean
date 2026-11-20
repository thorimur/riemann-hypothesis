import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTBranch
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SchurFock
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.GTLowerOf

theorem gTLower_of (h2 : Formalism.BasicNotions.FactDelDualNabla) : PI.GTLower :=
  PI.WGL.gTLower_of h2 highest_weight_irreducible gelfand_tsetlin_branching schur_fock
