import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegrality
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ExteriorIntegrality : WedgeInt := by
  first | exact @GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt | exact GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt | (intros; apply GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt <;> assumption)
