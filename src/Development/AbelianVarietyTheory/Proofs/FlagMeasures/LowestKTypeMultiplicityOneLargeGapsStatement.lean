import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_isKType_of_large_gaps : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ → (∀ a b : Fin n, ε a ≠ ε b → 2 * (n : ℝ) < |lam a - lam b|) → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) := by
  first | exact @GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub | exact GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub | (intros; apply GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub <;> assumption)
