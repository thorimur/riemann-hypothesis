import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselPairMajorantMulRight
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_besselPairMajorant_mul_right : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (γ₁ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (C : ℝ≥0∞), 0 < L.κN → L.κN ≠ ⊤ → 0 ≤ b → γ₁ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → C ≠ ⊤ → L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj γ₁ b) (Formalism.MainNotions.S.pairMeas L) → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (γ₁ * a) b) (Formalism.MainNotions.S.pairMeas L) := by
  first | exact @GlobalTheory.CellMajTransfer.integrable_mul_right | exact GlobalTheory.CellMajTransfer.integrable_mul_right | (intros; apply GlobalTheory.CellMajTransfer.integrable_mul_right <;> assumption)
