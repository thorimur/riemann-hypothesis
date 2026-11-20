import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THidaU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVFinalU
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.JointWinOfCounts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOfLemmaK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.PropZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ThmBcOfPsiBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.PfromAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Iv

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.HV.Core
open UpperTheory.V.Lit UpperTheory.V.W
theorem of_four_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hK : ∃ CK : ℝ, LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) : VWin := by
  obtain ⟨B, hB⟩ := Win.thmBab_of_lemmaK (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK FW.ferreroWashington hK
  obtain ⟨CK, hL⟩ := hK
  exact vwin_of_counts (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK hL (hB 401 (by norm_num))
    (Odd.thmBcFree_of (ML.iv (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.uo)) h1 h2 h3 h5 (countZ X.propZ)
theorem modU_of_printsH (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.W.ModUAlt := _root_.UpperTheory.V.W.modularity_unitary_of_automorphy_hida_unitary hH.litN Pa.pFromAut (_root_.UpperTheory.V.Hi.hida_unitary_of_printed_hida hH)
end UpperTheory.V.HV.Core
end
