import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelLocalOfToroidalIntegral
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_local_of_toroidal_integral : GlobalTheory.Published.SiegelToroidalIntegral → SiegLocSt := by
  first | exact @GlobalTheory.SiegLoc.siegLocSt_of_siegelToroidalIntegral | exact GlobalTheory.SiegLoc.siegLocSt_of_siegelToroidalIntegral | (intros; apply GlobalTheory.SiegLoc.siegLocSt_of_siegelToroidalIntegral <;> assumption)
