import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaCharLevelOneAndHolomorphicParameter
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChar_level_one_and_holomorphic_parameter : ∀ (g : ℕ) (a b : Fin g → ℂ), charHalf g a b → (∀ p ∈ Key.phDom g, IsLevel (per p) a b 1 (thetaChar (per p) a b)) ∧ (∀ (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ), DifferentiableOn ℂ (fun p => simTheta (per p) a b al m k n y) (Key.phDom g)) ∧ ∀ (k n : Fin g → ℤ) (z : Fin g → ℂ), Differentiable ℂ (fun p : Fin g → Fin g → ℂ => aut (per p) a b k n z) := by
  first | exact @GlobalTheory.SimilTheta.level_one_and_holomorphic | exact GlobalTheory.SimilTheta.level_one_and_holomorphic | (intros; apply GlobalTheory.SimilTheta.level_one_and_holomorphic <;> assumption)
