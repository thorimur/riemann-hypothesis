import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrime
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noDecompositionInvariants_auxiliaryPrime : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → ∀ v ∈ D.ntw.pD i, NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  first | exact @GlobalTheory.TripleGal.ScalarInvariants.noInv_pD | exact GlobalTheory.TripleGal.ScalarInvariants.noInv_pD | (intros; apply GlobalTheory.TripleGal.ScalarInvariants.noInv_pD <;> assumption)
