import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorMulIntegralUnitFiniteAdelesAwayP
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisor_mul_integralUnit_finiteAdelesAwayP : ∀ (p : ℕ) [Fact p.Prime] (a b : AfP p) (K : ℕ), 0 < K → K.Coprime p → IsIntAf a → IsIntAf b → a * b = (K : AfP p) → ∃ (c : ℕ) (ε ε' : AfP p), c.Coprime p ∧ c ∣ K ∧ IsIntAf ε ∧ IsIntAf ε' ∧ ε * ε' = 1 ∧ a = (c : AfP p) * ε := by
  first | (exact @GlobalTheory.AfUnitSplit.exists_dvd_mul_unit) | (exact GlobalTheory.AfUnitSplit.exists_dvd_mul_unit) | (intros; apply GlobalTheory.AfUnitSplit.exists_dvd_mul_unit  <;> assumption)
