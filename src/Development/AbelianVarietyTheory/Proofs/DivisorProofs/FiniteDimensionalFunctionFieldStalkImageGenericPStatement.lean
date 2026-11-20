import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFunctionFieldStalkImageGenericP
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
    FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField := by
  first | exact @GlobalTheory.NormSheafDescent.finiteDimensional_functionField | exact GlobalTheory.NormSheafDescent.finiteDimensional_functionField | (intros; apply GlobalTheory.NormSheafDescent.finiteDimensional_functionField <;> assumption)
