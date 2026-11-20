import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransportSecondEisensteinCm
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_transport_second_eisenstein_cm : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → g (s2 Λ₀ / Ω₀ ^ 2) = s2 Λ₁ / Ω₁ ^ 2 := by
  first | exact @GlobalTheory.NormSqOfSquareEqNeg.main | exact GlobalTheory.NormSqOfSquareEqNeg.main | (intros; apply GlobalTheory.NormSqOfSquareEqNeg.main <;> assumption)
