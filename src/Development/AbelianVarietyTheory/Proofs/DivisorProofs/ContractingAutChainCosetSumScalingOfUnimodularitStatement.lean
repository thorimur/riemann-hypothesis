import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutChainCosetSumScalingOfUnimodularit
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity : GlobalTheory.SatakeWeyl.Unimod → GlobalTheory.SatakeWeyl.ChainIndex → GlobalTheory.SatakeWeyl.ChainSum := by
  first | exact @GlobalTheory.SatakeWeyl.chainSum_of_unimod | exact GlobalTheory.SatakeWeyl.chainSum_of_unimod | (intros; apply GlobalTheory.SatakeWeyl.chainSum_of_unimod <;> assumption)
