import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepRealZetaNonvanishing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaStep_realZeta_nonvanishing : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, RealZeta D := by
  first | exact @GlobalTheory.EvenOntoRealZeta.realZeta | exact GlobalTheory.EvenOntoRealZeta.realZeta | (intros; apply GlobalTheory.EvenOntoRealZeta.realZeta <;> assumption)
