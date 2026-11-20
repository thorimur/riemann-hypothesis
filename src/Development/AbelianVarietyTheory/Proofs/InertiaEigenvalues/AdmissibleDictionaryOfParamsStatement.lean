import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParams
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_dictionary_of_params : GlobalTheory.TwSys.Cheb → ∀ D : D7, SumRepresentations.adm2 D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  first | exact @GlobalTheory.BridgeAdmDict.main | exact GlobalTheory.BridgeAdmDict.main | (intros; apply GlobalTheory.BridgeAdmDict.main <;> assumption)
