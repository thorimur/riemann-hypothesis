import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfStandardChar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardArchimedeanAddChar_of_standardChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → GlobalTheory.WeilL2Words.IsStdInf D.host.F ψ := by
  first | exact @GlobalTheory.WeilL2Words.StdTheta.isStdInf_of_isStdChar | exact GlobalTheory.WeilL2Words.StdTheta.isStdInf_of_isStdChar | (intros; apply GlobalTheory.WeilL2Words.StdTheta.isStdInf_of_isStdChar <;> assumption)
