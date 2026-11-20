import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem existsUnique_rat (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι :=
  (GlobalTheory.CompanionTheory.Ar.PB.Known.fieldNumbers ℚ K ι).1

end GlobalTheory.CompanionTheory.Ar.Link
