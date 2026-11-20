import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariant
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefiniteUnitaryGroup_haar_isMulRightInvariant : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.haar_UJ_isMulRightInvariant | exact GlobalTheory.haar_UJ_isMulRightInvariant | (intros; apply GlobalTheory.haar_UJ_isMulRightInvariant <;> assumption)
