import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.OneUseOf

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Bc
structure Hypotheses4Z' : Prop where
  h : _root_.UpperTheory.V.Af.HypothesesH'
  eis : Published.HilbertEisOne
  one : Lit.OneUse
end UpperTheory.V.Z.Bc
end
