import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TransferStatementBis
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TransferStatementBis : StTransfer := by
  first | exact @GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer | exact GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer | (intros; apply GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer <;> assumption)
