import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldStalkImageOfGenericPoint
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z], IsOpen (Set.range π) →
    IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  first | exact @GlobalTheory.NormSheafDescent.isField_stalk_genPt | exact GlobalTheory.NormSheafDescent.isField_stalk_genPt | (intros; apply GlobalTheory.NormSheafDescent.isField_stalk_genPt <;> assumption)
