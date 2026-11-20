import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoInclLast
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ

namespace GlobalTheory.FlagZ.Univ

theorem isIso_incl_last_step : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι), IsIso (GlobalTheory.FlagZ.Univ.incl ι N τ (Fin.last N)) :=
  isIso_incl_last

end GlobalTheory.FlagZ.Univ
