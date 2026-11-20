import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SturmSumOverCharactersEqZero
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sturm_sum_over_characters_eq_zero : ∀ (k L N : ℕ), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a : DirichletCharacter ℂ N → ℕ → ℂ, (∀ ε, MF k L (ch ε) (a ε)) → (∀ n < B, (∑ ε, a ε) n = 0) → ∑ ε, a ε = 0 := by
  first | exact @GlobalTheory.EisM.sturm_sum_coef_zero | exact GlobalTheory.EisM.sturm_sum_coef_zero | (intros; apply GlobalTheory.EisM.sturm_sum_coef_zero <;> assumption)
