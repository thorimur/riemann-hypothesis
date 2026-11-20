import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankRatSkewHermitianMatricesCmField
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_rat_skewHermitian_matrices_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ρ : ℕ) (Ψ : Finset (E →+* ℂ)), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → ∀ W : Submodule ℚ (Matrix (Fin ρ) (Fin ρ) E), (∀ β, β ∈ W ↔ FJ.IsSkew β) → Module.finrank ℚ W = Ψ.card * ρ ^ 2 := by
  first | exact @GlobalTheory.finrank_skewHermitian_eq | exact GlobalTheory.finrank_skewHermitian_eq | (intros; apply GlobalTheory.finrank_skewHermitian_eq <;> assumption)
