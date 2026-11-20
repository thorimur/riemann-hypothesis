import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldIsAlgebraicAdjoinJInvariant
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionField_isAlgebraic_adjoin_jInvariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range), (a : ℍ → ℂ) = jT → ∀ f : T.K, IsAlgebraic (IntermediateField.adjoin Ω {T.io a}) f := by
  first | exact @GlobalTheory.FN.frac_isAlgebraic_adjoin_j | exact GlobalTheory.FN.frac_isAlgebraic_adjoin_j | (intros; apply GlobalTheory.FN.frac_isAlgebraic_adjoin_j <;> assumption)
