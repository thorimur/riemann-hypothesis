import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetPowerSectionNeZeroDefinite
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_detPowerSection_ne_zero_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ γ ∈ X.Γ, γ = 1) → (X.p0 = 0 ∨ X.p0 = r) → ∀ s : ℕ, ∀ x ∈ X.dom, ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x ≠ 0 := by
  first | exact @GlobalTheory.DefConst.exists_ne_zero | exact GlobalTheory.DefConst.exists_ne_zero | (intros; apply GlobalTheory.DefConst.exists_ne_zero <;> assumption)
