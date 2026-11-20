import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSubalgebraMvPolynomialEvalOfFlatAeval
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_tensorSubalgebraMvPolynomialEval_of_flat_aeval : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] (A : Subalgebra ℂ K)
    (m : ℕ) (v : Fin m → A),
    (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A).toRingHom.Flat →
    (polyMap (κ' := κ') A v).Flat := by
  first | exact @GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval | exact GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval | (intros; apply GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval <;> assumption)
