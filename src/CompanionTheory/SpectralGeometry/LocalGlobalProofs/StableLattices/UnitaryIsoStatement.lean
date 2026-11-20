import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIso
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.UnitaryIso : UIso := by
  first | exact @GlobalTheory.CompanionTheory.ZuckUIso.uIso | exact GlobalTheory.CompanionTheory.ZuckUIso.uIso | (intros; apply GlobalTheory.CompanionTheory.ZuckUIso.uIso <;> assumption)
