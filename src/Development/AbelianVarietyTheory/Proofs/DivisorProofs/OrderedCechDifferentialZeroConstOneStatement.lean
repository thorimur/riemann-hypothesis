import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechDifferentialZeroConstOne
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCechDifferential_zero_const_one : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), δ F 0 (fun _ => 1) = 0 := by
  first | exact @GlobalTheory.CechPoset.δ_zero_one | exact GlobalTheory.CechPoset.δ_zero_one | (intros; apply GlobalTheory.CechPoset.δ_zero_one <;> assumption)
