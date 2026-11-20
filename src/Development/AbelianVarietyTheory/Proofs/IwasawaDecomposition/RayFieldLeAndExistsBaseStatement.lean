import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldLeAndExistsBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayField_le_and_exists_base : RayField → PrincipalIdealSt → ∀ (P : Pre) (f : Fr P) (δ : FieldDat P), listField δ f ≤ δ.Om ∧ ∃ B : Base, B.toPre = P ∧ B.KsC = listField δ f := by
  first | exact @GlobalTheory.Mem.KsBase.exists_base_listField | exact GlobalTheory.Mem.KsBase.exists_base_listField | (intros; apply GlobalTheory.Mem.KsBase.exists_base_listField <;> assumption)
