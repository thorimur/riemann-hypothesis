import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundOfCoreLawsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RunJoin

theorem lamwAt_absolute : ∃ CL : ℝ, 0 < CL ∧ ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D) (CA : ℝ), ParA large₂ CA → ∀ (j : ℕ) (w : WeightFamilies.Wt D j), LAMwAt large₂ (recB h.toLawsCore) j w CL 2 := by
  obtain ⟨C0, hC0, H⟩ := GlobalTheory.T.meanLogSupNorm_lower_bound_of_coreLaws
  exact ⟨C0, hC0, fun D T h large₂ CA hP j w =>
    H D T.toCore h.toLawsCore (GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore) large₂ hP.2.2.2.2.1 j w C0 2 le_rfl le_rfl⟩

end GlobalTheory.RunJoin
