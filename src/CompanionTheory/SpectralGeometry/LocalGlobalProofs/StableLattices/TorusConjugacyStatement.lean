import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugacy
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TorusConjugacy : TorConj := by
  first | exact @GlobalTheory.CompanionTheory.BmuTorConj.torConj | exact GlobalTheory.CompanionTheory.BmuTorConj.torConj | (intros; apply GlobalTheory.CompanionTheory.BmuTorConj.torConj <;> assumption)
