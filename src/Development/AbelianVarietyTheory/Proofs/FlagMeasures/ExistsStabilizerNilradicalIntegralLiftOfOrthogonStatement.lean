import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalIntegralLiftOfOrthogon
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stabilizerNilradicalIntegral_lift_of_orthogonal : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), R ≤ perpIn I x R → ∀ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ R, Φ *ᵥ y = 0) → (∀ y ∈ perpIn I x R, Φ *ᵥ y ∈ R) → ∃ Y ∈ nilInt I x R, ∀ y ∈ perpIn I x R, Y *ᵥ y = Φ *ᵥ y := by
  first | exact @GlobalTheory.NilLift.exists_nilInt_lift | exact GlobalTheory.NilLift.exists_nilInt_lift | (intros; apply GlobalTheory.NilLift.exists_nilInt_lift <;> assumption)
