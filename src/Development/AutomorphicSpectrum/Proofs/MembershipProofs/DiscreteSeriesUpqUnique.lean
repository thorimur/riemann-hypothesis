import Development.AutomorphicSpectrum.Proofs.JetProofs.ExistsDiagonalCongrOfSimilitudeDistinctEigenvalu
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification

namespace GlobalTheory.CompanionTheory.Front

theorem discreteSeriesUpqUnique : GlobalTheory.Published.DiscreteSeriesUpqUnique := by
  have h := GlobalTheory.CompanionTheory.DS.dsUnique
  unfold GlobalTheory.CompanionTheory.DS.DSUnique at h
  unfold GlobalTheory.Published.DiscreteSeriesUpqUnique
  intros
  apply h <;> assumption

end GlobalTheory.CompanionTheory.Front
