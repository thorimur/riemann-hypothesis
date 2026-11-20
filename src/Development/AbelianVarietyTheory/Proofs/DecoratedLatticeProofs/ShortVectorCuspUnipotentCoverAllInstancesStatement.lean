import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShortVectorCuspUnipotentCoverAllInstances
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortVectorCuspUnipotentCover_all_instances : ∀ I : AutInst, ShortCusp I := by
  first | exact @GlobalTheory.CuspGeo.shortCusp_all | exact GlobalTheory.CuspGeo.shortCusp_all | (intros; apply GlobalTheory.CuspGeo.shortCusp_all <;> assumption)
