import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFormCoeffSeqDirichletTwistLevelMulSq
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFormCoeffSeq_dirichletTwist_level_mul_sq : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ), 0 < M → CF k N (ch χ) g → CF k (N * M ^ 2) (fun d => ch χ d * ch φ d ^ 2) (fun n => φ n * g n) := by
  first | exact @GlobalTheory.EisM.CharTwist.cf_twist | exact GlobalTheory.EisM.CharTwist.cf_twist | (intros; apply GlobalTheory.EisM.CharTwist.cf_twist <;> assumption)
