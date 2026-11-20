import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RightGamma0CosetDecompositionAdjugateHeckeT
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightGamma0CosetDecomposition_adjugate_heckeT : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → RRep L (DT L q) (fun i => (repT q i).adjugate) := by
  first | exact @GlobalTheory.EisM.rrep_DT_adj_repT | exact GlobalTheory.EisM.rrep_DT_adj_repT | (intros; apply GlobalTheory.EisM.rrep_DT_adj_repT <;> assumption)
