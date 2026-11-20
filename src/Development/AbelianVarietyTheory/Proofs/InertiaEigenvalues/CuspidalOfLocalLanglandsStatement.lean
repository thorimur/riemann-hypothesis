import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalOfLocalLanglands
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_of_local_langlands : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), CGTrue hL D T → CuspRead (recT T hL) := by
  first | exact @GlobalTheory.CuspReadTrue.cuspRead_recT | exact GlobalTheory.CuspReadTrue.cuspRead_recT | (intros; apply GlobalTheory.CuspReadTrue.cuspRead_recT <;> assumption)
