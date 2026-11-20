import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.AutNew
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutNewform2A
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BrRepNewAE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BrRepEig

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af
theorem UpperTheory.V.Br.autNewformA_of_printsH (P : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Win.RR.AutNewformA :=
  _root_.UpperTheory.V.Z.Win.RR.autNewformA_of_printsH_of_repNewAE P (_root_.UpperTheory.V.Br.repNewAE_of_printsH_of_repEig P (_root_.UpperTheory.V.Br.repEig_of_printsH_of_hermEx P Br.hermEx))
end
