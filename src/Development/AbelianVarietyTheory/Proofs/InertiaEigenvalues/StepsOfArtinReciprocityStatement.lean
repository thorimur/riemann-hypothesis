import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StepsOfArtinReciprocity
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.steps_of_artin_reciprocity : GlobalTheory.Published.GlobalArtinReciprocity → StepsNoCut := by
  first | exact @GlobalTheory.Pass.stepsNoCut_of_artin | exact GlobalTheory.Pass.stepsNoCut_of_artin | (intros; apply GlobalTheory.Pass.stepsNoCut_of_artin <;> assumption)
