import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDualLiftingProof
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCountDualLifting_proof : StepLocDual := by
  first | exact @GlobalTheory.Pass.LocDual.main | exact GlobalTheory.Pass.LocDual.main | (intros; apply GlobalTheory.Pass.LocDual.main <;> assumption)
