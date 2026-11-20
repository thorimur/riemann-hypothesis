import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_of_local_langlands : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : AUSide D), AUTrue hL D T A → UnitaryRead D.nbc (recT T hL) := by
  first | exact @GlobalTheory.UnitaryReadTrue.unitaryRead_true | exact GlobalTheory.UnitaryReadTrue.unitaryRead_true | (intros; apply GlobalTheory.UnitaryReadTrue.unitaryRead_true <;> assumption)
