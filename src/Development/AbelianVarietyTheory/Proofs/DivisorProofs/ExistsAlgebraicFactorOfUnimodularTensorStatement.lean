import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicFactorOfUnimodularTensor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraic_factor_of_unimodular_tensor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, 1 ≤ r → (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  first | exact @GlobalTheory.Mum.Tens.nonempty_factor | exact GlobalTheory.Mum.Tens.nonempty_factor | (intros; apply GlobalTheory.Mum.Tens.nonempty_factor <;> assumption)
