import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HomCategory
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HomCategory : HomCat := by
  first | exact @GlobalTheory.CompanionTheory.ZuckHomCat.homCat | exact GlobalTheory.CompanionTheory.ZuckHomCat.homCat | (intros; apply GlobalTheory.CompanionTheory.ZuckHomCat.homCat <;> assumption)
