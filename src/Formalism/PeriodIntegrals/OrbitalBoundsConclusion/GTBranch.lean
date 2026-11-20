import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ConstructionD

theorem gelfand_tsetlin_branching : PI.GTBranch :=
  PI.WGB.gTBranch_of_steps highest_weight_irreducible (PI.WGB.extremalFacts_of_A highest_weight_irreducible) PI.WGB.fixed_line_exists
    PI.WGB.stable_complement_exists PI.WGB.highest_weight_vector_exists
    (PI.WGB.realize_of highest_weight_irreducible (PI.WGB.extremalFacts_of_A highest_weight_irreducible) PI.WGB.fixed_line_exists
      PI.WGB.stable_complement_exists PI.WGB.highest_weight_vector_exists)
