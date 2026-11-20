import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointTensorGraphLocalization
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalRingOfVarietyPoint_tensorGraphLocalization : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
  [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ'),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  IsLocModel (algebraMap ℂ L) (GlobalTheory.DiagLoc.loc L σ) := by
  first | exact @GlobalTheory.DiagLoc.isLocModel_loc | exact GlobalTheory.DiagLoc.isLocModel_loc | (intros; apply GlobalTheory.DiagLoc.isLocModel_loc <;> assumption)
