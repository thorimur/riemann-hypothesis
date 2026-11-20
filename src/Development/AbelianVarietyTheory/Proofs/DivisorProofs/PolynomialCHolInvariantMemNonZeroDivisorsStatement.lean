import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialCHolInvariantMemNonZeroDivisors
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialC_holInvariant_mem_nonZeroDivisors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (D : HA M), (∀ c, ∃ x : M.dom, (D : C → M.dom → ℂ) c x ≠ 0) → Polynomial.C D ∈ nonZeroDivisors (Polynomial (HA M)) := by
  first | exact @GlobalTheory.CuspEmb.C_mem_nonZeroDivisors | exact GlobalTheory.CuspEmb.C_mem_nonZeroDivisors | (intros; apply GlobalTheory.CuspEmb.C_mem_nonZeroDivisors <;> assumption)
