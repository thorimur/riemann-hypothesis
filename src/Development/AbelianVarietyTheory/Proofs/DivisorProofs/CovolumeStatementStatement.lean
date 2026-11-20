import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeStatement
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CovolumeStatement : CovolSt := by
  first | exact @GlobalTheory.DetHT.Covol.covol | exact GlobalTheory.DetHT.Covol.covol | (intros; apply GlobalTheory.DetHT.Covol.covol <;> assumption)
