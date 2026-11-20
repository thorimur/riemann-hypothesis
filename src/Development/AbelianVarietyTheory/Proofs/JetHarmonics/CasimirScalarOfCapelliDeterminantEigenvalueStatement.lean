import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_scalar_of_capelliDeterminant_eigenvalue : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (mu : Fin n → ℝ), 2 ≤ n → Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → ∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w := by
  first | exact @GlobalTheory.CapelliCasimir.cas_of_capelli | exact GlobalTheory.CapelliCasimir.cas_of_capelli | (intros; apply GlobalTheory.CapelliCasimir.cas_of_capelli <;> assumption)
