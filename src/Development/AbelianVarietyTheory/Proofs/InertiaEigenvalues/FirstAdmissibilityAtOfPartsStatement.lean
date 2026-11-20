import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstAdmissibilityAtOfParts
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypicValuationAtRing_of_unrRho_hodgeL_noInv_negCount : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HodgeL bkP i s → (∀ v, NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v) → NegCount bkP i s → IsotypicValuationAtRing bkP i s := by
  first | exact @GlobalTheory.TripleGal.firstAdmissibilityAt_of_parts | exact GlobalTheory.TripleGal.firstAdmissibilityAt_of_parts | (intros; apply GlobalTheory.TripleGal.firstAdmissibilityAt_of_parts <;> assumption)
