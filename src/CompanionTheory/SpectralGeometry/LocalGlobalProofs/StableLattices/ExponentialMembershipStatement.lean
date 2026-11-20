import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExponentialMembership
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ExponentialMembership : ExpMem := by
  first | exact @GlobalTheory.CompanionTheory.BmuExpMem.expMem | exact GlobalTheory.CompanionTheory.BmuExpMem.expMem | (intros; apply GlobalTheory.CompanionTheory.BmuExpMem.expMem <;> assumption)
