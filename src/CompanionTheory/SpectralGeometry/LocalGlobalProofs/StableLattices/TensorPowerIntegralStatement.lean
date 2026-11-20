import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegral
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TensorPowerIntegral : OKTens := by
  first | exact @GlobalTheory.CompanionTheory.ZuckTens.okTens | exact GlobalTheory.CompanionTheory.ZuckTens.okTens | (intros; apply GlobalTheory.CompanionTheory.ZuckTens.okTens <;> assumption)
