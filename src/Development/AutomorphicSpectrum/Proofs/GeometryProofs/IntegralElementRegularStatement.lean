import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegular
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_element_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ), IsCptGen ξ → IsIntegrallyClosed (X.presheaf.stalk p.1) → ∀ a : Ω, IsIntegral ℤ a → a ∈ regAt ξ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntReg.mem_regAt_of_isIntegral_of_stalk | exact GlobalTheory.CompanionTheory.Ar.IntReg.mem_regAt_of_isIntegral_of_stalk | (intros; apply GlobalTheory.CompanionTheory.Ar.IntReg.mem_regAt_of_isIntegral_of_stalk <;> assumption)
