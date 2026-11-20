import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
namespace GlobalTheory.NConjHaar

theorem map_conj_eq_smul : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r), 0 < L.κN → L.κN ≠ ⊤ → ∀ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → (∀ n, n ∈ Formalism.QuantumDeterminants.Nset k r ↔ a * n * a⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN := by
  intro k r L h0 ht a ha hN
  have hμ := GlobalTheory.haarLie_isHaarOn_Nset k r L.κN h0 ht.lt_top
  have hu : IsUnit a.det := GlobalTheory.Amp.StabHaar.unit_of_GG ha
  have hmap := GlobalTheory.Amp.StabHaar.haar_conj (G := Formalism.QuantumDeterminants.Nset k r) (G' := Formalism.QuantumDeterminants.Nset k r) a hu hN hμ
  obtain ⟨c, c0, ct, hc⟩ := GlobalTheory.BesselPeriodCompare.haar_unique (Formalism.FourierDecayAlt.P.B2x2.closedN k r) hmap hμ
  exact ⟨c, ct, hc⟩

end GlobalTheory.NConjHaar
