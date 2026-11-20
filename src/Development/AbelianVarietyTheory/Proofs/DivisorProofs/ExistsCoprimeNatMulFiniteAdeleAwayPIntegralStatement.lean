import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNatMulFiniteAdeleAwayPIntegral
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral : ∀ (p : ℕ) [Fact p.Prime] (a : AfP p), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ IsIntAf ((j : AfP p) * a) := by
  first | (exact @GlobalTheory.DenAway.exists_coprime_nat_adele) | (exact GlobalTheory.DenAway.exists_coprime_nat_adele) | (intros; apply GlobalTheory.DenAway.exists_coprime_nat_adele  <;> assumption)
