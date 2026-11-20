import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ReductionOfDerivedSeries
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_of_derived_series : DsLin → DsAd → DsDer → Reduce := by
  first | exact @GlobalTheory.CompanionTheory.BmuReduce.reduce | exact GlobalTheory.CompanionTheory.BmuReduce.reduce | (intros; apply GlobalTheory.CompanionTheory.BmuReduce.reduce <;> assumption)
