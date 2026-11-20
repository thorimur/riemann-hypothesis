import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundOfCoreLaws
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanLogSupNorm_lower_bound_of_coreLaws : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (D : D7) (T : Core D) (h : LawsCore T), GamAt T → ∀ (large₂ : SizeData₂ D), (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) → ∀ (j : ℕ) (w : WeightFamilies.Wt D j) (C A : ℝ), C0 ≤ C → 2 ≤ A → Formalism.MainNotions.Gaps.EtaleWeightGaps.LAMwAt large₂ (recB h) j w C A := by
  first | exact @GlobalTheory.lamwAt_of_lawsCore | exact GlobalTheory.lamwAt_of_lawsCore | (intros; apply GlobalTheory.lamwAt_of_lawsCore <;> assumption)
