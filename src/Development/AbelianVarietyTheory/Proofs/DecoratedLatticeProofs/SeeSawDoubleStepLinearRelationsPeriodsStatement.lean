import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepLinearRelationsPeriods
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_doubleStep_linearRelations_periods : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D → RapidVal D → ValMove D → PerSum D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ValX t → TwoX t → RdX t → StepX t := by
  first | exact @GlobalTheory.SeeSawStep.stepX_of_laws | exact GlobalTheory.SeeSawStep.stepX_of_laws | (intros; apply GlobalTheory.SeeSawStep.stepX_of_laws <;> assumption)
