import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DeltaStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DeltaStatement : StDelta := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stDelta | exact GlobalTheory.CompanionTheory.RgFl.stDelta | (intros; apply GlobalTheory.CompanionTheory.RgFl.stDelta <;> assumption)
