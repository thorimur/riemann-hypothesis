import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimePairBoxBounds
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pair_box_bounds : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∃ q d : ℕ, Boxq x eps q d ∧ QDq x eps C q d ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ 2 * x ^ (2 + 8 * eps) → Rowq x eps n q d := by
  first | exact @GlobalTheory.Mem.An.exists_q_d_box_bounds_rows | exact GlobalTheory.Mem.An.exists_q_d_box_bounds_rows | (intros; apply GlobalTheory.Mem.An.exists_q_d_box_bounds_rows <;> assumption)
