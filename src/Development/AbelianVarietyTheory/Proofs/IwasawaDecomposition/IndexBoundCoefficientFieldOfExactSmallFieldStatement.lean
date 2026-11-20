import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldTies_of_rayField_of_ksExact : GlobalTheory.NT.RayField → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : Fld.FieldDat X.B.toPre), X.B.KsExact δ f → FieldTies X.toD7 (Fr.at X f) := by
  first | exact @GlobalTheory.AtMember.fieldTies_of_ksExact | exact GlobalTheory.AtMember.fieldTies_of_ksExact | (intros; apply GlobalTheory.AtMember.fieldTies_of_ksExact <;> assumption)
