import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortGeneratorSectionsSmallShiftedFubiniStudy
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortGenerator_sections_small_shifted_fubiniStudy : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → ∀ (j : Fin n) (hj : w j ∈ W), s ⟨w j, hj⟩ ∈ (L.shift (fun _ => t) (fun _ => rfl)).smallSec := by
  first | exact @GlobalTheory.ImageModel.smallSec_shift_of_isShortGen | exact GlobalTheory.ImageModel.smallSec_shift_of_isShortGen | (intros; apply GlobalTheory.ImageModel.smallSec_shift_of_isShortGen <;> assumption)
