import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainSpannedParamsOfValueIndependent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.even_theta_chain_spanned_params_of_value_independent : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → MetEx D → EigSpan D ∧ ParOfVal D ∧ ParIndep D := by
  first | exact @GlobalTheory.EvenOnto.eig_parOfVal_indep | exact GlobalTheory.EvenOnto.eig_parOfVal_indep | (intros; apply GlobalTheory.EvenOnto.eig_parOfVal_indep <;> assumption)
