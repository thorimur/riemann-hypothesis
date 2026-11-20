import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherianSubringPrimeContractionOrDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noetherian_subring_prime_contraction_or_dvr : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (p : PrimeSpectrum R₁), p ∈ Set.range (PrimeSpectrum.comap R₁.subtype) ∨ ∃ (Q : PrimeSpectrum R) (k : Type) (_ : Field k) (i : R₁ →+* k) (j : k →+* Q.asIdeal.ResidueField) (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ρ : R₁ →+* V) (e : k →+* FractionRing V), j.comp i = (algebraMap R Q.asIdeal.ResidueField).comp R₁.subtype ∧ e.comp i = (algebraMap V (FractionRing V)).comp ρ ∧ p ∈ Set.range (PrimeSpectrum.comap ρ) := by
  first | exact @GlobalTheory.PrimeReach.prime_contraction_or_dvr | exact GlobalTheory.PrimeReach.prime_contraction_or_dvr | (intros; apply GlobalTheory.PrimeReach.prime_contraction_or_dvr <;> assumption)
