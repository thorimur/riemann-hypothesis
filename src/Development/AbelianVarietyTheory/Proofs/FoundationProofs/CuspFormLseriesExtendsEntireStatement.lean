import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormLseriesExtendsEntire
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_lseries_extends_entire : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → CF k L (ch ε) g → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s ∧ LSeries g s = Λ s := by
  first | exact @GlobalTheory.EisM.lseries_cusp_entire | exact GlobalTheory.EisM.lseries_cusp_entire | (intros; apply GlobalTheory.EisM.lseries_cusp_entire <;> assumption)
