import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainWeilDatumExtendsToStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenRankThetaChain_weilDatum_extends_to_step : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, StepEx D := by
  first | exact @GlobalTheory.EvenOnto.StepExists.stepEx | exact GlobalTheory.EvenOnto.StepExists.stepEx | (intros; apply GlobalTheory.EvenOnto.StepExists.stepEx <;> assumption)
