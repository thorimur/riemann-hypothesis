import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFiniteVectorsHolds
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_finite_vectors_holds : GlobalTheory.Published.CuspFiniteVectorsGL := by
  first | exact @GlobalTheory.CompanionTheory.Published.cuspFiniteVectorsGL | exact GlobalTheory.CompanionTheory.Published.cuspFiniteVectorsGL | (intros; apply GlobalTheory.CompanionTheory.Published.cuspFiniteVectorsGL <;> assumption)
