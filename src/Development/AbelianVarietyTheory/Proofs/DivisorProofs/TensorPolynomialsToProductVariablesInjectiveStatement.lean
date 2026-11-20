import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesInjective
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPolynomialsToProductVariables_injective : ∀ (W Λ : Type) [Fintype W] [DecidableEq W], Function.Injective (GlobalTheory.CCRFock.polMap W Λ) := by
  first | exact @GlobalTheory.CCRFock.polMap_injective | exact GlobalTheory.CCRFock.polMap_injective | (intros; apply GlobalTheory.CCRFock.polMap_injective <;> assumption)
