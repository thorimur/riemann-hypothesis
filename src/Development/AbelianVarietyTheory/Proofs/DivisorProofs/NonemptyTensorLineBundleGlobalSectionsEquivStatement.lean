import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTensorLineBundleGlobalSectionsEquiv
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_tensor_lineBundle_globalSections_equiv : ∀ (T : Scheme.{0}) [IsAffine T] (A B : LB T), A.IsLB → B.IsLB → Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)] LB.Sec (GlobalTheory.CechPic.tens A B)) := by
  first | exact @GlobalTheory.SecTensor.tensorSecEquiv | exact GlobalTheory.SecTensor.tensorSecEquiv | (intros; apply GlobalTheory.SecTensor.tensorSecEquiv <;> assumption)
