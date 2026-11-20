import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembership
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_membership : AvgMem := by
  first | exact @GlobalTheory.CompanionTheory.EisMirGen.avgMem | exact GlobalTheory.CompanionTheory.EisMirGen.avgMem | (intros; apply GlobalTheory.CompanionTheory.EisMirGen.avgMem <;> assumption)
