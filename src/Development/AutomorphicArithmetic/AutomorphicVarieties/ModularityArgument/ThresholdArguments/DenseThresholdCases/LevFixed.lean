import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevFixedSs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FixedDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EqOneOfDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagPol

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Lev.fixedSs_of_prints (P : _root_.UpperTheory.V.Af.Hypotheses') : _root_.UpperTheory.V.Lev.FixedSsAlt :=
  _root_.UpperTheory.V.Lev.fixed_semisimple_of_flag_fixed_dvd_fixed_unramified UpperTheory.V.Lev.flagPol (_root_.UpperTheory.V.Z.Win.T2.fixedDvd' P) (_root_.UpperTheory.V.Z.Win.T2.fixedUnr_alt P)
end
