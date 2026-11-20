import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoint_finitePart_isotropic_pairing : ∀ {D : D7} (S T : HSp D) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E), symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) = 0 := by
  first | exact @GlobalTheory.RatFinIso.isotropic | exact GlobalTheory.RatFinIso.isotropic | (intros; apply GlobalTheory.RatFinIso.isotropic <;> assumption)
