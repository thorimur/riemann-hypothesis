import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement

open Formalism.BasicNotions

namespace GlobalTheory

theorem modelsAreCoverSeries_of_hypotheses :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra

end GlobalTheory
