import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirrorPartitions
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirror_partitions : ReciprocityTheory.Ty.Fin.St.MirrorsOf := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Mirrors.main | exact GlobalTheory.CompanionTheory.TyFin.Mirrors.main | (intros; apply GlobalTheory.CompanionTheory.TyFin.Mirrors.main <;> assumption)
