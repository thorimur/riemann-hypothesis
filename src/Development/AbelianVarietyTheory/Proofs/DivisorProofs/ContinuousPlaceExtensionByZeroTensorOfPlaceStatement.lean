import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceExtensionByZeroTensorOfPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K] (P : GlobalTheory.CompanionTheory.SaGen.PlaceMap F K), Continuous (GlobalTheory.CompanionTheory.SaGen.iB (E := E) P) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place | exact GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place | (intros; apply GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place <;> assumption)
