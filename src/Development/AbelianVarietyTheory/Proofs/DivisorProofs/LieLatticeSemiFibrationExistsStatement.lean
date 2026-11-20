import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeSemiFibrationExists
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_semi_fibration_exists : Hypotheses2 → HypothesesH → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated → OnObj fun D O _ _ H _ => ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
  ∀ y : Pt O.s, y ∉ H.int → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K))
    (h : HermFam K (Fin (D.R.f * O.N) → K)), IsLieAt O y K L h ∧
    ∃ (F : SemiFib K) (h' : HermFam K (Fin F.P₀.g → K)) (r : ℕ) (ε : Fin r → Fin (D.R.f * O.N) → K)
      (q : (Fin (D.R.f * O.N) → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h' ∧ TorusExt h L ε q h' F.lieLat C := by
  first | exact @GlobalTheory.HeightParts.lieLat_torusExt_at_boundary | exact GlobalTheory.HeightParts.lieLat_torusExt_at_boundary | (intros; apply GlobalTheory.HeightParts.lieLat_torusExt_at_boundary <;> assumption)
