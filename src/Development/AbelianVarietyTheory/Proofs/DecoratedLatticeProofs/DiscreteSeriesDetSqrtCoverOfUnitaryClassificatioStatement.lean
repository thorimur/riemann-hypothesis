import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesDetSqrtCoverOfUnitaryClassificatio
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_detSqrtCover_of_unitary_classification : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCover := by
  first | exact @GlobalTheory.CoverDS.discreteSeriesCover_of_classification | exact GlobalTheory.CoverDS.discreteSeriesCover_of_classification | (intros; apply GlobalTheory.CoverDS.discreteSeriesCover_of_classification <;> assumption)
