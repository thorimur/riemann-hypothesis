import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplex
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ToRawComplex : ToRaw := by
  first | exact @GlobalTheory.CompanionTheory.ZuckToRaw.toRaw | exact GlobalTheory.CompanionTheory.ZuckToRaw.toRaw | (intros; apply GlobalTheory.CompanionTheory.ZuckToRaw.toRaw <;> assumption)
