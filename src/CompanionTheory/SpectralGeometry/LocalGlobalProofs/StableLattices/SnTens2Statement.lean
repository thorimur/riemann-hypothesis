import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensHom' : TensHom := by
  first | exact @GlobalTheory.CompanionTheory.ZuckTensHom.tensHom | exact GlobalTheory.CompanionTheory.ZuckTensHom.tensHom | (intros; apply GlobalTheory.CompanionTheory.ZuckTensHom.tensHom <;> assumption)
