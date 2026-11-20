import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerInnerProduct
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_inner_product : ReciprocityTheory.Ty.Fin.St.IntwIp := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.intwIp | exact GlobalTheory.CompanionTheory.TyFin.intwIp | (intros; apply GlobalTheory.CompanionTheory.TyFin.intwIp <;> assumption)
