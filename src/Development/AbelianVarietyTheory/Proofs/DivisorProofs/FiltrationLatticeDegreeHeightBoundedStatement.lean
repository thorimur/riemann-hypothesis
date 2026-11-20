import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationLatticeDegreeHeightBounded
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_lattice_degree_height_bounded : Hypotheses2 → HypothesesH → OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ y : Pt O.s, y ∈ H.int → ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K)), FibTie O y F ι → F.IsHerm h → ∀ τ, ∀ k ≤ O.S.Dw.mult τ, latRank K (stepLat O F τ k) = k ∧ |deg h (stepLat O F τ k) + stepHt O O.met.hm y τ k| ≤ C := by
  first | exact @GlobalTheory.LieRead.steps_read_heights | exact GlobalTheory.LieRead.steps_read_heights | (intros; apply GlobalTheory.LieRead.steps_read_heights <;> assumption)
