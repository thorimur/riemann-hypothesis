import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantHermitianWeightForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_hermitian_weight_form : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ β, IsInvForm a β := by
  first | exact @GlobalTheory.InvFormBdd.exists_isInvForm | exact GlobalTheory.InvFormBdd.exists_isInvForm | (intros; apply GlobalTheory.InvFormBdd.exists_isInvForm <;> assumption)
