import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshCompAnalytic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPsh_comp_analytic : ∀ (D D' : ℕ) (U : Set (Fin D → ℂ)) (V : Set (Fin D' → ℂ)) (φ : (Fin D → ℂ) → ℝ) (h : (Fin D' → ℂ) → (Fin D → ℂ)), IsOpen U → IsOpen V → ReciprocityTheory.AnForm.A.IsPsh U φ → AnalyticOnNhd ℂ h V → Set.MapsTo h V U → ReciprocityTheory.AnForm.A.IsPsh V (φ ∘ h) := by
  first | exact @GlobalTheory.PshPullback.isPsh_comp | exact GlobalTheory.PshPullback.isPsh_comp | (intros; apply GlobalTheory.PshPullback.isPsh_comp <;> assumption)
