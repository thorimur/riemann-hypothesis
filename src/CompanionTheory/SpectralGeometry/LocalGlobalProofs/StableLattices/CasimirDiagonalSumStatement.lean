import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSum
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CasimirDiagonalSum : CasDS := by
  first | exact @GlobalTheory.CompanionTheory.CasimirDS.casDS | exact GlobalTheory.CompanionTheory.CasimirDS.casDS | (intros; apply GlobalTheory.CompanionTheory.CasimirDS.casDS <;> assumption)
