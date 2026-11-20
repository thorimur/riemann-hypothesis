import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiChiSqrtLogBound
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_chi_sqrt_log_bound : GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.ExplZeta → ∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u → ‖psiChi χ u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u)) := by
  first | exact @GlobalTheory.Mem.An.GoodLarge.psi_le_of_large | exact GlobalTheory.Mem.An.GoodLarge.psi_le_of_large | (intros; apply GlobalTheory.Mem.An.GoodLarge.psi_le_of_large <;> assumption)
