import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeEqMulPrimitiveRootSubOnePow
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_eq_mul_primitiveRoot_sub_one_pow' : ∀ (l : ℕ) [Fact l.Prime] (H : ℕ) (ζ : PadicComplex l), IsPrimitiveRoot ζ (l ^ (1 + n0 l H)) → ∃ u : PadicComplex l, ‖u‖ ≤ 1 ∧ (l : PadicComplex l) = u * (ζ - 1) ^ H := by
  first | exact @GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow | exact GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow | (intros; apply GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow <;> assumption)
