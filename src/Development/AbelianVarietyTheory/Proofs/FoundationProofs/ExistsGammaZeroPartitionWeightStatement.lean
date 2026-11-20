import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGammaZeroPartitionWeight
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gammaZeroPartitionWeight : ∀ L : ℕ, 0 < L → ∃ ρ, Wt L ρ := by
  first | exact @GlobalTheory.wt_exists | exact GlobalTheory.wt_exists | (intros; apply GlobalTheory.wt_exists <;> assumption)
