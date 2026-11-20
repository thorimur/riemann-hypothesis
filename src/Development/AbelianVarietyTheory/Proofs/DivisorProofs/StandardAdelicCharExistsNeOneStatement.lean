import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharExistsNeOne

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_adelic_char_exists_ne_one : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ s : AF F, ψ s ≠ 1 := by
  first | exact @GlobalTheory.StdPsiNontrivial.exists_ne_one_of_isStd | exact GlobalTheory.StdPsiNontrivial.exists_ne_one_of_isStd | (intros; apply GlobalTheory.StdPsiNontrivial.exists_ne_one_of_isStd <;> assumption)
