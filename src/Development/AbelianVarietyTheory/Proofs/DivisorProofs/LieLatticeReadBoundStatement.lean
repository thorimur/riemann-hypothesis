import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeReadBound
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_read_bound : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∃ C : ℝ, ∀ (y : Pt O.s) (K : Type) [Field K] [NumberField K]
  (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)) (h : HermFam K (Fin (D.R.f * O.N) → K)),
    IsLieAt O y K L h → ReadsAt O (ref0 O) y h L C := by
  first | exact @GlobalTheory.LieSmooth.readsAt_smooth | exact GlobalTheory.LieSmooth.readsAt_smooth | (intros; apply GlobalTheory.LieSmooth.readsAt_smooth <;> assumption)
