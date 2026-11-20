import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InfinitesimalCharacterStatement

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.InfinitesimalCharacterStatement : CompanionTheory.RgExh.StepChar := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar | exact GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar <;> assumption)
