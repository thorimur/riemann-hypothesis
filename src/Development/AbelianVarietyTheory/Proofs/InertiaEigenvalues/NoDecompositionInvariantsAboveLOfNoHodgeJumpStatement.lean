import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAboveLOfNoHodgeJump
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noDecompositionInvariants_aboveL_of_noHodgeJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tmat i s) v := by
  first | exact @GlobalTheory.InvJump.noInv_of_noJump | exact GlobalTheory.InvJump.noInv_of_noJump | (intros; apply GlobalTheory.InvJump.noInv_of_noJump <;> assumption)
