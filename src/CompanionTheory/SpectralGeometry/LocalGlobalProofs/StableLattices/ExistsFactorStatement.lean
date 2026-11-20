import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsFactor
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorization' : Factor := by
  first | exact @GlobalTheory.CompanionTheory.BmuFactor.factor | exact GlobalTheory.CompanionTheory.BmuFactor.factor | (intros; apply GlobalTheory.CompanionTheory.BmuFactor.factor <;> assumption)
