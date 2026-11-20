import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepSemilocalZetaNeZeroOfReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaStep_semilocalZeta_ne_zero_of_real : ∀ D : D7, MetEx D → RealZeta D → ZetaNe D := by
  first | exact @GlobalTheory.EvenOnto.ZetaNeProof.zetaNe_of_real | exact GlobalTheory.EvenOnto.ZetaNeProof.zetaNe_of_real | (intros; apply GlobalTheory.EvenOnto.ZetaNeProof.zetaNe_of_real <;> assumption)
