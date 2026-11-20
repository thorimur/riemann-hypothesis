import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0ZeroFreeRegionBound
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_psi0_le_exp_sqrt_log : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∃ C c : ℝ, 0 < c ∧ ∀ u : ℝ, 2 ≤ u → ‖GlobalTheoryTheory.psi0 χ u‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u)) := by
  first | exact @GlobalTheory.Mem.An.psi0_le_exp_neg_sqrt_log | exact GlobalTheory.Mem.An.psi0_le_exp_neg_sqrt_log | (intros; apply GlobalTheory.Mem.An.psi0_le_exp_neg_sqrt_log <;> assumption)
