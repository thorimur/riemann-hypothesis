import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSmoothedEisensteinFxWeightOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansion_smoothedEisensteinFx_weightOne : ∀ (c M : ℕ) (a b : ℤ), 0 < M → GlobalTheory.QFam.HasQ M (GlobalTheory.Sieg.cF c 1 ![(a : ℚ) / M, (b : ℚ) / M]) (GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M (GlobalTheory.Sieg.ee (1 / (M : ℂ))) a b) := by
  first | exact @GlobalTheory.Sieg.EisQ.hasQ_cF_one | exact GlobalTheory.Sieg.EisQ.hasQ_cF_one | (intros; apply GlobalTheory.Sieg.EisQ.hasQ_cF_one; all_goals assumption)
