import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealData
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanThetaCorrespondence_towers_real_data : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D := by
  first | exact @GlobalTheory.TwArch.archOnRecord_closed | exact GlobalTheory.TwArch.archOnRecord_closed | (intros; apply GlobalTheory.TwArch.archOnRecord_closed <;> assumption)
