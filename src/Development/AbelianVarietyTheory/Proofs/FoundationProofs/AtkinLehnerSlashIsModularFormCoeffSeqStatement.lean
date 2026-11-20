import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashIsModularFormCoeffSeq
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atkinLehner_slash_isModularFormCoeffSeq : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → MF k (N * l) (ch χ) a → ∃ a' : ℕ → ℂ, MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) := by
  first | exact @GlobalTheory.EisM.atkinLehner_MF | exact GlobalTheory.EisM.atkinLehner_MF | (intros; apply GlobalTheory.EisM.atkinLehner_MF <;> assumption)
