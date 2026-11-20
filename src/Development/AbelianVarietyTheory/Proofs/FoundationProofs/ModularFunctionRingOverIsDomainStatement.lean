import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionRingOverIsDomain
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionRingOver_isDomain : ∀ E : Subring ℂ, IsDomain (GlobalTheory.FN.ring E) := by
  first | exact @GlobalTheory.FN.ring_isDomain | exact GlobalTheory.FN.ring_isDomain | (intros; apply GlobalTheory.FN.ring_isDomain <;> assumption)
