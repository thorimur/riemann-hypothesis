import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeSummandWeightTwoBound
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeSummand_weightTwo_bound : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∃ C : ℝ, ∀ p : F × F, p ≠ 0 → ‖GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm 2 σ z p‖ ≤ C * (∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2)) ^ (-(1 + σ.re)) := by
  first | exact @GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound | exact GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound | (intros; apply GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound <;> assumption)
