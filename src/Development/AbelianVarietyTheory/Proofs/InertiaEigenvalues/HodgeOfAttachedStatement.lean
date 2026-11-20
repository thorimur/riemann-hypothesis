import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeOfAttached
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → HodgeL bkP i s := by
  first | exact @GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt | exact GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt | (intros; apply GlobalTheory.TripleGal.HodgeOfAtt.hodgeL_of_tripleAtt <;> assumption)
