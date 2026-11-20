import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame : ∀ {D : D7} (S : HSp D) (B : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → IsSelfDualC S (colLat B) := by
  first | exact @GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal | exact GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal | (intros; apply GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal <;> assumption)
