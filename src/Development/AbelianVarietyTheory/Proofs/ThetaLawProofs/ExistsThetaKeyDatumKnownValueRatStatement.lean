import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaKeyDatumKnownValueRat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaKeyDatum_known_value_rat : Out.Laws → ThetaUnifAV → ∀ g : ℕ, 1 ≤ g → ∃ y : KeyIn ℚ, y.P.g = g ∧ Known ℚ y := by
  first | exact @GlobalTheory.KeyFam.exists_known_rat | exact GlobalTheory.KeyFam.exists_known_rat | (intros; apply GlobalTheory.KeyFam.exists_known_rat <;> assumption)
