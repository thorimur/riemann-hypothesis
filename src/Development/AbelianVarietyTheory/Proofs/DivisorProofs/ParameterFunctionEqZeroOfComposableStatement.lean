import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterFunctionEqZeroOfComposable
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_function_eq_zero_of_composable : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ (l m : Λ) (p : Hol F.V), (∀ (k k' k'' : K.K), K.le l k' k → K.le m k'' k' → K.cst k'' p = 0) → p = 0 := by
  first | exact @GlobalTheory.AnPer.Charts.eq_zero_of_cst_composable | exact GlobalTheory.AnPer.Charts.eq_zero_of_cst_composable | (intros; apply GlobalTheory.AnPer.Charts.eq_zero_of_cst_composable <;> assumption)
