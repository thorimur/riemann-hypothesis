import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DutiesOfLarge
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.duties_of_large_of_cheb : GlobalTheory.TwSys.Cheb → ∀ D : D7, Large D → SumRepresentations.Conclusion41 D → AutomorphicSideWildInertia.ResidualIrreducibleGood D → Duties D := by
  first | exact @GlobalTheory.CoefDuty.duties_of_large | exact GlobalTheory.CoefDuty.duties_of_large | (intros; apply GlobalTheory.CoefDuty.duties_of_large <;> assumption)
