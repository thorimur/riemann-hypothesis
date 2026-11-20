import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSlRightAction
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_sl_rightAction : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ f, T.sl 1 f = f) ∧ ∀ g h f, T.sl (g * h) f = T.sl h (T.sl g f) := by
  first | exact @GlobalTheory.FN.frac_sl_right_action | exact GlobalTheory.FN.frac_sl_right_action | (intros; apply GlobalTheory.FN.frac_sl_right_action <;> assumption)
