import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplitting
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CasimirSplitting : CasSplit := by
  first | exact @GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit | exact GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit | (intros; apply GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit <;> assumption)
