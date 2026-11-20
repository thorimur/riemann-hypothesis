import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfEventualPolynomialGrowth

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_of_eventual_polynomial_growth : ∀ (d D a f : ℕ), (∀ N : ℕ, ∃ s, N ≤ s ∧ d * s ^ f ≤ D * (s + a) ^ f) → d ≤ D := by
  first | exact @GlobalTheory.le_of_frequently_mul_pow_le_mul_add_pow | exact GlobalTheory.le_of_frequently_mul_pow_le_mul_add_pow | (intros; apply GlobalTheory.le_of_frequently_mul_pow_le_mul_add_pow <;> assumption)
