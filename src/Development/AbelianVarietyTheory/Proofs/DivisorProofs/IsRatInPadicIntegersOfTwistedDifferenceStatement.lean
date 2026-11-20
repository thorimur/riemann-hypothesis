import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatInPadicIntegersOfTwistedDifference
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRatInPadicIntegers_of_twisted_difference : ∀ {G : Type} [CommGroup G] [Finite G] (l : ℕ) [Fact l.Prime] (g : G) (q : ℕ), l ∣ q →
    ∀ x : G → ℚ, (∀ C, InZl l (x C - (q : ℚ) * x (C * g))) → ∀ C, InZl l (x C) := by
  first | exact @GlobalTheory.inZl_of_twisted_difference | exact GlobalTheory.inZl_of_twisted_difference | (intros; apply GlobalTheory.inZl_of_twisted_difference <;> assumption)
