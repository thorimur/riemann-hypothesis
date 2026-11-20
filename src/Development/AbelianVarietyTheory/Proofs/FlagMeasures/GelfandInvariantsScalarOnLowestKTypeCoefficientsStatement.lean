import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantsScalarOnLowestKTypeCoefficients
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariants_scalar_on_lowestKType_coefficients : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ c : ℕ → ℂ, ∀ s ∈ lowKSub ε lam σ, ∀ u : H, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) ∧ ∀ m, ∀ g ∈ UJset ε, gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) g = c m * ⟪u, σ g s⟫_ℂ := by
  first | exact @GlobalTheory.CentreLow.centre_scalar_low | exact GlobalTheory.CentreLow.centre_scalar_low | (intros; apply GlobalTheory.CentreLow.centre_scalar_low <;> assumption)
