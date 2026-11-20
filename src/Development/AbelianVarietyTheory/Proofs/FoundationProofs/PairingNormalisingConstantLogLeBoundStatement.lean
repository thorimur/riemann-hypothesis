import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PairingNormalisingConstantLogLeBound
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_normalising_constant_log_le_bound : ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∃ s : ℕ, 0 < s ∧ extNorm K lam = (s : K) ∧ Real.log s ≤ bound (Fintype.card ι) n R := by
  first | exact @GlobalTheory.extNorm_eq_nat_log_le_bound | exact GlobalTheory.extNorm_eq_nat_log_le_bound | (intros; apply GlobalTheory.extNorm_eq_nat_log_le_bound <;> assumption)
